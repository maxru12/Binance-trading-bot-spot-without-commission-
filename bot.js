const Decimal = require('decimal.js');
require('dotenv').config();
const fs = require('fs');
const axios = require('axios');
const crypto = require('crypto');
const WebSocket = require('ws');

const API_KEY = process.env.BINANCE_API_KEY;
const API_SECRET = process.env.BINANCE_API_SECRET;

if (!API_KEY || !API_SECRET) {
  console.error('ERROR: API keys not found! Please check your .env file.');
  console.error('Required variables: BINANCE_API_KEY and BINANCE_API_SECRET');
  process.exit(1);
}

//// --- Настройки ---
const PROFIT_TARGET_PERCENT = 0.3; // Процент прибыли от средней цены
const FIXED_NOTIONAL = 1.3; // Начальный notional ордера FDUSD
const MAX_GRID_POSITIONS = 20; // Макс уровней сетки
const GRID_ORDER_INCREASE_ENABLED = true; // Включить/отключить рост notional последующих ордеров
const GRID_ORDER_INCREASE_PERCENT = 0.12; // Увеличение последующих ордеров в сетке FDUSD (%) если включено выше

// --- Настройки автошага сетки ---
const GRID_STEP_AUTO_ENABLED = true; // Включить/отключить автошаг сетки (по волатильности)
const GRID_STEP_MIN_TICKS = 30;
const GRID_STEP_MAX_TICKS = 50;
const GRID_STEP_AUTO_PERCENT = 0.1;
const GRID_STEP_BASE_TICKS = 40; // Базовый шаг для всех режимов сетки

// --- Настройки подтяжки сетки ---
const GRID_PULL_DELAY_MINUTES = 2.5; // Время в минутах, через которое подтягивать сетку, если цена ушла выше base price

// --- Настройки выставления сетки ---
const GRID_MODE = 'NONLINEAR'; // 'LINEAR' или 'NONLINEAR' Режим равномерной сетки или нелинейный
const ORDER_PLACEMENT_MODE = 'SEQUENTIAL'; // 'ALL_AT_ONCE' или 'SEQUENTIAL' Выставляются сразу все ордера или последовательно
const NONLINEAR_MULTIPLIER = 1.12; // Множитель для нелинейного увеличения шага
const GRID_BASE_OFFSET_TICKS = 0; // дополнительные тики ниже bestAsk для начала установки сетки (0 = близко к рынку)

let GRID_STEP_TICKS = GRID_STEP_BASE_TICKS;

// Глобальные переменные состояния с очисткой памятью
let activeBuyOrderIds = new Map(); // orderId -> {origQty, side, price}
let activeSellOrderInfo = { orderId: null, origQty: 0, side: 'SELL', price: 0 }; // for sell, it's one
let symbolInfo = null;
let listenKey = null;
let bookTicker = { bestBid: null, bestAsk: null };
let bookTickerWs = null;
let userDataWs = null;
let klineWs = null;
let isInitialized = false;
let calculatedGridPositions = 0; // Рассчитанное количество ордеров сетки

// Очистка старых данных каждые 24 часа
setInterval(() => {
  logger.log('Performing periodic cleanup...');

  // Очищаем старые записи в activeBuyOrderIds если их слишком много
  if (activeBuyOrderIds.size > 100) {
    logger.warn('Cleaning up old buy order entries');
    const entries = Array.from(activeBuyOrderIds.entries());
    const keepEntries = entries.slice(-50); // Оставляем только последние 50
    activeBuyOrderIds.clear();
    keepEntries.forEach(([id, data]) => activeBuyOrderIds.set(id, data));
  }

  logger.log('Cleanup complete');
}, 24 * 60 * 60 * 1000); // Раз в 24 часа

// --- WebSocket reconnection backoff ---
let wsReconnectAttempts = { userData: 0, bookTicker: 0, kline: 0 };
const MAX_RECONNECT_DELAY = 30000; // 30 seconds max delay
const INITIAL_RECONNECT_DELAY = 1000; // 1 second initial delay

function getReconnectDelay(type) {
  const attempts = wsReconnectAttempts[type] || 0;
  const delay = Math.min(INITIAL_RECONNECT_DELAY * Math.pow(2, attempts), MAX_RECONNECT_DELAY);
  wsReconnectAttempts[type]++;
  return delay;
}

function resetReconnectAttempts(type) {
  wsReconnectAttempts[type] = 0;
}
let avgBuyPrice = new Decimal(0); // СТАНДАРТИЗИРОВАНО: все цены теперь Decimal
let tickSize = 0;
let isGridPlacing = false; // ❌ РАСОВАЯ УСЛОВИЕ: недостаточно защиты
let gridActive = false;
let gridBasePrice = 0;
let lastGridAdjustmentTime = 0;
let cycleStartTime = null;
let botStartTime = null;
let currentDOGEQty = new Decimal(0); // ✅ ИСПРАВЛЕНО: теперь всегда Decimal
let totalNotionalSpent = new Decimal(0); // ✅ ИСПРАВЛЕНО: всегда Decimal
let initialBalance = 0;
let sequentialOrderIndex = 0; // Индекс для последовательного размещения
let sequentialGridPrices = []; // ❌ РАСОВАЯ УСЛОВИЕ: массив без лимита размера
let executedBuyOrders = 0; // Количество исполненных ордеров на покупку в текущем цикле
let totalCycles = 0; // Счётчик циклов
let totalGridPulls = 0; // Счётчик подтяжек сетки

// ✅ ДОБАВЛЕН МЬЮТЕКС ДЛЯ РАСОВЫХ СОСТОЯНИЙ
let operationInProgress = false; // Защита от одновременных операций
const MAX_ORDER_HISTORY_SIZE = 200; // Лимит на историю ордеров
const MAX_GRID_PRICES_SIZE = 50; // Максимальный размер массива цен сетки

// --- Простой Точный PnL ---
let totalPnL = new Decimal(0);
let totalBought = new Decimal(0); // Общая сумма купленных FDUSD
let totalQty = new Decimal(0); // Общее количество DOGE
let currentDayPnL = new Decimal(0); // Накопленная прибыль за текущий период
let currentWeekPnL = new Decimal(0); // Накопленная прибыль за текущую неделю
let currentMonthPnL = new Decimal(0); // Накопленная прибыль за текущий месяц
let lastDayTimestamp = null; // Timestamp последнего сброса дня
let lastWeekTimestamp = null; // Timestamp последнего сброса недели
let lastMonthTimestamp = null; // Timestamp последнего сброса месяца
let lastDayTotalPnL = null; // Baseline PnL для дня
let lastWeekTotalPnL = null; // Baseline PnL для недели
let lastMonthTotalPnL = null; // Baseline PnL для месяца

// --- НОВАЯ ПЕРЕМЕННАЯ ---
let sellOrderTargetPrice = 0; // Цена, на которую выставлен ордер на продажу
let activeSellOrderId = null; // ID активного ордера на продажу

// Логирование в файл с ротацией
const LOG_DIR = './logs';
if (!fs.existsSync(LOG_DIR)) fs.mkdirSync(LOG_DIR);

let LOG_FILE = `${LOG_DIR}/bot.log`;
const MAX_LOG_SIZE = 10 * 1024 * 1024; // 10 MB

function checkLogRotation() {
  try {
    if (fs.existsSync(LOG_FILE) && fs.statSync(LOG_FILE).size > MAX_LOG_SIZE) {
      const timestamp = new Date().toISOString().replace(/:/g, '-');
      const archivedLog = `${LOG_DIR}/bot_${timestamp}.log`;
      fs.renameSync(LOG_FILE, archivedLog);
      logger.log(`Log rotated: ${archivedLog}`);
    }
  } catch (err) {
    console.error('Log rotation error:', err.message);
  }
}

function logToFile(message, level = 'INFO') {
  // Неблокирующая запись логов
  checkLogRotation();
  const timestamp = new Date().toISOString();
  const logEntry = `[${timestamp}] [${level}] ${message}\n`;
  fs.appendFile(LOG_FILE, logEntry, (err) => {
    if (err) console.error('Failed to write to log file:', err.message);
  });
}

const logger = {
  log: function(message, level = 'INFO') {
    const timestamp = new Date().toISOString();
    console.log(`[${timestamp}] [${level}] ${message}`);
    logToFile(message, level);
  },
  error: function(message) {
    this.log(message, 'ERROR');
  },
  warn: function(message) {
    this.log(message, 'WARN');
  },
  debug: function(message) {
    this.log(message, 'DEBUG');
  }
};

  // Загрузка данных PnL
  try {
    if (fs.existsSync(`${LOG_DIR}/pnl_data.json`)) {
      const pnlData = JSON.parse(fs.readFileSync(`${LOG_DIR}/pnl_data.json`));
      totalPnL = new Decimal(pnlData.totalPnL || 0);
      totalBought = new Decimal(pnlData.totalBought || 0);
      totalQty = new Decimal(pnlData.totalQty || 0);
      currentDayPnL = new Decimal(pnlData.currentDayPnL || 0);
      currentWeekPnL = new Decimal(pnlData.currentWeekPnL || 0);
      currentMonthPnL = new Decimal(pnlData.currentMonthPnL || 0);
      lastDayTimestamp = pnlData.lastDayTimestamp ? new Date(pnlData.lastDayTimestamp) : null;
      lastWeekTimestamp = pnlData.lastWeekTimestamp ? new Date(pnlData.lastWeekTimestamp) : null;
      lastMonthTimestamp = pnlData.lastMonthTimestamp ? new Date(pnlData.lastMonthTimestamp) : null;
      logger.log(`Loaded PnL data: Total PnL=${totalPnL.toFixed(6)}, Bought=${totalBought.toFixed(6)}, Qty=${totalQty.toFixed(6)}`);
    }
  } catch (e) {
    logger.error('Error loading PnL data: ' + e.message);
  }

function savePnLData() {
  // Неблокирующая запись данных PnL
  try {
    const data = {
      totalPnL: totalPnL.toString(),
      totalBought: totalBought.toString(),
      totalQty: totalQty.toString(),
      currentDayPnL: currentDayPnL.toString(),
      currentWeekPnL: currentWeekPnL.toString(),
      currentMonthPnL: currentMonthPnL.toString(),
      lastDayTimestamp: lastDayTimestamp?.toISOString(),
      lastWeekTimestamp: lastWeekTimestamp?.toISOString(),
      lastMonthTimestamp: lastMonthTimestamp?.toISOString()
    };
    fs.writeFile(`${LOG_DIR}/pnl_data.json`, JSON.stringify(data, null, 2), (err) => {
      if (err) logger.error('Error saving PnL data asynchronously: ' + err.message);
    });
  } catch (e) {
    logger.error('Error preparing PnL data: ' + e.message);
  }
}

// ✅ ТОЧНЫЙ РАСЧЁТ PnL (исправлен: полная консистентность типов)
function calculateSimplePnL(qtySold, sellPrice) {
  if (totalQty.lte(0) || totalBought.lte(0)) {
    logger.warn('No bought position, cannot calculate PnL');
    return new Decimal(0);
  }

  const qtySoldDec = new Decimal(qtySold);
  const sellPriceDec = new Decimal(sellPrice);

  const avgBuyPriceDec = totalBought.div(totalQty);
  const profit = sellPriceDec.minus(avgBuyPriceDec).times(qtySoldDec);
  totalPnL = totalPnL.plus(profit);

  // Уменьшаем позицию с проверкой на отрицательные значения
  const portion = qtySoldDec.div(totalQty);
  const costPortion = portion.times(totalBought);

  totalBought = totalBought.minus(costPortion);
  // Защита от отрицательных значений при floating point ошибках
  if (totalBought.lt(0)) totalBought = new Decimal(0);

  totalQty = totalQty.minus(qtySoldDec);
  if (totalQty.lt(0)) totalQty = new Decimal(0);

  savePnLData();

  logger.log(`PnL: Sold ${qtySoldDec.toFixed(8)} DOGE at ${sellPriceDec.toFixed(8)}, Profit=${profit.toFixed(8)}, Remaining Qty=${totalQty.toFixed(8)}`);
  console.log(`\x1b[33m[SALE COMPLETE] Total PnL: ${totalPnL.toFixed(8)} FDUSD\x1b[0m`);

  return profit; // Возвращаем Decimal, а не число
}

// Подпись запросов
function signRequest(params) {
  const query = Object.keys(params).map(k => `${k}=${params[k]}`).join('&');
  return crypto.createHmac('sha256', API_SECRET).update(query).digest('hex');
}

// Форматирование количества и цены
function formatQuantityAndPrice(quantity, price) {
  if (!symbolInfo) throw new Error('Symbol info not loaded');
  const lotSize = symbolInfo.filters.find(f => f.filterType === 'LOT_SIZE');
  const priceFilter = symbolInfo.filters.find(f => f.filterType === 'PRICE_FILTER');
  const stepSize = parseFloat(lotSize.stepSize);
  const tickSize = parseFloat(priceFilter.tickSize);
  const qtyRounded = Math.floor(quantity / stepSize) * stepSize;
  const priceRounded = Math.round(price / tickSize) * tickSize;
  const decimalPlaces = lotSize.stepSize.split('.')[1]?.length || 0;
  const priceDecimalPlaces = priceFilter.tickSize.split('.')[1]?.length || 0;
  return {
    quantity: qtyRounded.toFixed(decimalPlaces),
    price: priceRounded.toFixed(priceDecimalPlaces)
  };
}

// Проверка фильтров
function validateOrder(quantity, price) {
  if (!symbolInfo) throw new Error('Symbol info not loaded');
  const lotSize = symbolInfo.filters.find(f => f.filterType === 'LOT_SIZE');
  const notionalFilter = symbolInfo.filters.find(f => f.filterType === 'NOTIONAL');
  const minQty = parseFloat(lotSize.minQty);
  const maxQty = parseFloat(lotSize.maxQty);
  if (quantity < minQty || quantity > maxQty) {
    throw new Error(`Quantity ${quantity} out of LOT_SIZE bounds [${minQty}, ${maxQty}]`);
  }
  const notional = quantity * price;
  const minNotional = parseFloat(notionalFilter.minNotional);
  if (notional < minNotional) {
    throw new Error(`Notional ${notional} below minNotional ${minNotional}`);
  }
}

// Выставление ордера
async function placeOrder(side, quantity, price) {
  try {
    validateOrder(quantity, price);
    const { quantity: qtyStr, price: priceStr } = formatQuantityAndPrice(quantity, price);
    const timestamp = Date.now();
    const recvWindow = 5000;
    const params = {
      symbol: 'DOGEFDUSD',
      side,
      type: 'LIMIT_MAKER',
      quantity: qtyStr,
      price: priceStr,
      timestamp,
      recvWindow
    };
    params.signature = signRequest(params);
    const url = 'https://api.binance.com/api/v3/order';
    const response = await axios.post(url, new URLSearchParams(params).toString(), {
      headers: {
        'Content-Type': 'application/x-www-form-urlencoded',
        'X-MBX-APIKEY': API_KEY
      }
    });
    logger.log(`Order placed successfully: ${side} order ID: ${response.data.orderId}`);
    return response.data;
  } catch (error) {
    const errorMessage = error.response?.data?.msg || error.message;
    logger.error(`Error placing order: ${errorMessage}`);
    throw new Error(`Order placement failed: ${errorMessage}`);
  }
}



// Отмена ордера
async function cancelOrder(orderId) {
  try {
    const timestamp = Date.now();
    const recvWindow = 5000;
    const params = {
      symbol: 'DOGEFDUSD',
      orderId,
      timestamp,
      recvWindow
    };
    params.signature = signRequest(params);
    const url = `https://api.binance.com/api/v3/order?${new URLSearchParams(params).toString()}`;
    await axios.delete(url, {
      headers: { 'X-MBX-APIKEY': API_KEY }
    });
    logger.log(`Order cancelled: ${orderId}`);
  } catch (error) {
    logger.error('Error cancelling order: ' + error.message);
  }
}

// Получение баланса FDUSD
async function getBalance() {
  try {
    const timestamp = Date.now();
    const recvWindow = 5000;
    const params = { timestamp, recvWindow };
    params.signature = signRequest(params);
    const url = `https://api.binance.com/api/v3/account?${new URLSearchParams(params).toString()}`;
    const response = await axios.get(url, { headers: { 'X-MBX-APIKEY': API_KEY } });
    const balance = response.data.balances.find(b => b.asset === 'FDUSD');
    return parseFloat(balance?.free || 0);
  } catch (error) {
    logger.error('Error getting balance: ' + error.message);
    throw error;
  }
}

// Получение listenKey
async function getListenKey() {
  try {
    const url = 'https://api.binance.com/api/v3/userDataStream';
    const response = await axios.post(url, null, { headers: { 'X-MBX-APIKEY': API_KEY } });
    logger.log('User data stream key retrieved');
    return response.data.listenKey;
  } catch (error) {
    logger.error('Error getting listen key: ' + error.message);
    throw error;
  }
}

// Обновление listenKey
async function keepAliveListenKey() {
  if (!listenKey) return;
  try {
    const url = `https://api.binance.com/api/v3/userDataStream?listenKey=${listenKey}`;
    await axios.put(url, null, { headers: { 'X-MBX-APIKEY': API_KEY } });
  } catch (error) {
    logger.error('Error keeping listen key alive: ' + error.message);
  }
}

// Подключение к userDataStream
function connectUserDataStream() {
  if (userDataWs) userDataWs.close();
  const delay = getReconnectDelay('userData');
  logger.log(`Connecting to userData WebSocket with delay ${delay}ms`);
  setTimeout(() => {
    userDataWs = new WebSocket(`wss://stream.binance.com:9443/ws/${listenKey}`);
    userDataWs.on('open', () => {
      resetReconnectAttempts('userData');
      logger.log('UserData WebSocket connected successfully');
    });
    userDataWs.on('message', handleUserDataMessage);
    userDataWs.on('close', (code, reason) => {
      logger.warn(`UserData WebSocket closed (${code}): ${reason}, reconnecting with exponential backoff`);
      connectUserDataStream();
    });
    userDataWs.on('error', (err) => {
      logger.error('UserData WebSocket error: ' + err.message);
      connectUserDataStream();
    });
  }, delay);
}

// Подключение к bookTicker
function connectBookTicker() {
  if (bookTickerWs) bookTickerWs.close();
  const delay = getReconnectDelay('bookTicker');
  logger.log(`Connecting to bookTicker WebSocket with delay ${delay}ms`);
  setTimeout(() => {
    const wsUrl = 'wss://stream.binance.com:9443/ws/dogefdusd@bookTicker';
    logger.log(`Connecting to WebSocket: ${wsUrl}`);
    bookTickerWs = new WebSocket(wsUrl);
    bookTickerWs.on('open', () => {
      resetReconnectAttempts('bookTicker');
      logger.log('BookTicker WebSocket connected for DOGEFDUSD successfully');
    });
    bookTickerWs.on('message', handleBookTickerMessage);
    bookTickerWs.on('close', (code, reason) => {
      logger.warn(`BookTicker WebSocket closed (${code}): ${reason}, reconnecting with exponential backoff`);
      connectBookTicker();
    });
    bookTickerWs.on('error', (err) => {
      logger.error('BookTicker WebSocket error: ' + err.message);
      connectBookTicker();
    });
  }, delay);
}

// Обработка сообщений bookTicker
function handleBookTickerMessage(data) {
  try {
    const msg = JSON.parse(data);
    if (msg.s === 'DOGEFDUSD') {
      bookTicker.bestBid = parseFloat(msg.b);
      bookTicker.bestAsk = parseFloat(msg.a);

      if (isInitialized) {
        if (gridActive && bookTicker.bestAsk) {
          const now = Date.now();
          const gridPullDelayMs = GRID_PULL_DELAY_MINUTES * 60 * 1000;
          if (now - lastGridAdjustmentTime > gridPullDelayMs) {
            lastGridAdjustmentTime = now;
            if (bookTicker.bestAsk > gridBasePrice) {
              totalGridPulls++;
              logger.log(`Price moved up (${bookTicker.bestAsk.toFixed(6)} > ${gridBasePrice.toFixed(6)}), cancelling grid and restarting...`);
              cancelAllActiveOrders();
              resetGridState();
            }
          }
        }

        // ✅ Обновляем sell order, если цена поднялась выше цели, чтобы продать по новой цене
        if (activeSellOrderId && bookTicker.bestBid > sellOrderTargetPrice) {
          logger.log(`Price rose above sell target (${bookTicker.bestBid.toFixed(6)} > ${sellOrderTargetPrice.toFixed(6)}), updating sell order`);
          placeOrUpdateSellOrder();
        }

        if (!activeSellOrderId && !gridActive && activeBuyOrderIds.size === 0) {
          if (bookTicker.bestAsk) {
            placeGridOrders();
          }
        }
      }
    }
  } catch (e) {
    logger.error('Error processing bookTicker message: ' + e.message);
  }
}

// Обработка userDataStream
function handleUserDataMessage(data) {
  try {
    const msg = JSON.parse(data);
    if (msg.e !== 'executionReport') return;
    const orderId = msg.o;
    const status = msg.X;
    const side = msg.S;
    const qty = parseFloat(msg.q);
    const price = parseFloat(msg.p);

    if (status === 'FILLED' || status === 'PARTIALLY_FILLED') {
      if (side === 'BUY') {
        // ✅ Используем новый простой ПНЛ
        totalQty = totalQty.plus(new Decimal(qty));
        totalBought = totalBought.plus(new Decimal(qty).times(new Decimal(price)));

        currentDOGEQty = totalQty.toNumber();
        avgBuyPrice = totalQty.isZero() ? new Decimal(0) : totalBought.div(totalQty); // ✅ Всегда Decimal
        totalNotionalSpent = totalBought; // ✅ Всегда Decimal

        savePnLData();

        logger.log(`BUY: Added ${qty.toFixed(6)} DOGE at ${price.toFixed(6)}, Total Qty: ${totalQty.toFixed(6)}, Avg Price: ${avgBuyPrice.toFixed(6)}`);
        logger.log(`BUY order filled: ${orderId}, Qty: ${qty.toFixed(6)}, Price: ${price.toFixed(6)}`);

        activeBuyOrderIds.delete(orderId);
        executedBuyOrders++;

        // ✅ В последовательном режиме выставляем следующий ордер
        if (ORDER_PLACEMENT_MODE === 'SEQUENTIAL' && gridActive) {
          placeNextSequentialOrder();
        }

        // ✅ Пересчитываем ордер на продажу после каждой покупки
        placeOrUpdateSellOrder();
      } else if (side === 'SELL') {
        // ✅ Рассчитываем PnL для проданной части
        const profit = calculateSimplePnL(qty, price);
        logger.log(`SELL order ${status}: ${orderId}, Qty: ${qty.toFixed(6)}, Price: ${price.toFixed(6)}, Remaining Qty: ${totalQty.toFixed(6)}`);

        // Sync currentDOGEQty
        currentDOGEQty = totalQty.toNumber();
        avgBuyPrice = totalQty.isZero() ? new Decimal(0) : totalBought.div(totalQty); // ✅ Всегда Decimal
        totalNotionalSpent = totalBought; // ✅ Всегда Decimal

        // ✅ После каждого исполнения ордера на продажу всегда сбрасываем цикл и начинаем заново
        totalCycles++; // Считаем цикл только при завершении продажи
        resetGridState();

        activeSellOrderId = null;
        activeSellOrderInfo = { orderId: null, origQty: 0, side: 'SELL' };
      }
    } else if (status === 'CANCELED') {
      if (side === 'BUY' && activeBuyOrderIds.has(orderId)) {
        activeBuyOrderIds.delete(orderId);
        // ✅ Если все покупки отменены, и остались DOGE, пересчитываем продажу
        if (activeBuyOrderIds.size === 0 && currentDOGEQty > 0) {
          placeOrUpdateSellOrder();
        }
      } else if (side === 'SELL' && orderId === activeSellOrderId) {
        activeSellOrderId = null;
        activeSellOrderInfo = { orderId: null, origQty: 0, side: 'SELL' };
        logger.warn('Sell order was cancelled, resetting grid state.');
        // ✅ Если ордер на продажу отменился, и он был последним, сбрасываем цикл
        resetGridState();
      }
    }
  } catch (e) {
    logger.error('Error processing userData message: ' + e.message);
  }
}

// Расчёт цен сетки (LINEAR или NONLINEAR)
function calculateGridPrices(basePrice, positions) {
  const gridPrices = [];
  const priceFilter = symbolInfo.filters.find(f => f.filterType === 'PRICE_FILTER');
  const minPrice = parseFloat(priceFilter.minPrice);
  const maxPrice = parseFloat(priceFilter.maxPrice);

  if (GRID_MODE === 'LINEAR') {
    // Линейное расположение
    for (let i = 0; i < positions; i++) {
      const price = basePrice - (tickSize * GRID_STEP_TICKS * (i + 1));
      if (price < minPrice || price > maxPrice) {
        logger.warn(`Grid level ${i+1} price ${price.toFixed(6)} is out of bounds, skipping`);
        continue;
      }
      gridPrices.push(price);
    }
  } else if (GRID_MODE === 'NONLINEAR') {
    // Нелинейное (экспоненциальное) расположение
    let currentStep = GRID_STEP_TICKS;
    let currentPrice = basePrice;
    
    for (let i = 0; i < positions; i++) {
      currentPrice = currentPrice - (tickSize * currentStep);
      
      if (currentPrice < minPrice || currentPrice > maxPrice) {
        logger.warn(`Grid level ${i+1} price ${currentPrice.toFixed(6)} is out of bounds, skipping`);
        break;
      }
      
      gridPrices.push(currentPrice);
      // Увеличиваем шаг экспоненциально
      currentStep = Math.floor(currentStep * NONLINEAR_MULTIPLIER);
    }
  }

  logger.log(`Grid mode: ${GRID_MODE}, calculated ${gridPrices.length} price levels`);
  return gridPrices;
}

// Выставление сетки ордеров с мьютексом
async function placeGridOrders() {
  // ✅ Проверяем мьютекс для предотвращения race conditions
  if (operationInProgress) {
    logger.log('placeGridOrders: Operation already in progress, skipping');
    return;
  }

  if (isGridPlacing || gridActive) {
    logger.log('placeGridOrders: Grid already active/placing, skipping');
    return;
  }

  operationInProgress = true;
  isGridPlacing = true;
  gridActive = true;

  const bestAsk = bookTicker.bestAsk;
  if (!bestAsk) {
    logger.warn('placeGridOrders: bestAsk is null or undefined, skipping.');
    isGridPlacing = false;
    gridActive = false;
    return;
  }

  gridBasePrice = bestAsk - tickSize * GRID_BASE_OFFSET_TICKS; // настройка расстояния от рынка

  const currentBalance = await getBalance();
  if (currentBalance <= 0) {
    logger.warn(`Insufficient balance: ${currentBalance.toFixed(6)} FDUSD. Skipping grid placement.`);
    isGridPlacing = false;
    gridActive = false;
    return;
  }

  // Расчитываем максимальное количество ородерров по балансу с учётом возрастающего notional (если включено)
  let accum = 0;
  let actualGridPositions = 0;
  for (let i = 0; i < MAX_GRID_POSITIONS; i++) {
    const notional = GRID_ORDER_INCREASE_ENABLED ? FIXED_NOTIONAL * (1 + i * GRID_ORDER_INCREASE_PERCENT) : FIXED_NOTIONAL;
    if (accum + notional > currentBalance) break;
    accum += notional;
    actualGridPositions++;
  }

  if (actualGridPositions <= 0) {
    logger.warn(`Insufficient balance: need at least ${FIXED_NOTIONAL}, have ${currentBalance.toFixed(2)}`);
    isGridPlacing = false;
    gridActive = false;
    return;
  }

  // Сохраняем рассчитанное количество ордеров для отображения в дашборде
  calculatedGridPositions = actualGridPositions;

  logger.log(`Placing grid orders: Mode=${ORDER_PLACEMENT_MODE}, Grid=${GRID_MODE}, Positions=${actualGridPositions}, Estimated total notional=${accum.toFixed(2)} FDUSD`);

  // Рассчитываем цены сетки
  const gridPrices = calculateGridPrices(bestAsk, actualGridPositions);

  if (gridPrices.length === 0) {
    logger.warn('No valid grid prices calculated, skipping');
    isGridPlacing = false;
    gridActive = false;
    return;
  }

  const lotSize = symbolInfo.filters.find(f => f.filterType === 'LOT_SIZE');
  const notionalFilter = symbolInfo.filters.find(f => f.filterType === 'NOTIONAL');
  const stepSize = parseFloat(lotSize.stepSize);
  const minQty = parseFloat(lotSize.minQty);
  const maxQty = parseFloat(lotSize.maxQty);
  const minNotional = parseFloat(notionalFilter.minNotional);

  if (ORDER_PLACEMENT_MODE === 'SEQUENTIAL') {
    // Сохраняем все рассчитанные цены для последовательного выставления
    sequentialGridPrices = gridPrices;
    sequentialOrderIndex = 0;
    
    // Последовательное выставление - только первый ордер
    const price = gridPrices[0];
    const qty = GRID_ORDER_INCREASE_ENABLED ? (FIXED_NOTIONAL * (1 + 0 * GRID_ORDER_INCREASE_PERCENT)) / price : FIXED_NOTIONAL / price;

    let finalQtyDec = new Decimal(Math.max(minQty, Math.min(maxQty, qty))).dividedBy(new Decimal(stepSize)).floor().times(new Decimal(stepSize));
    let finalQty = finalQtyDec.toNumber();
    
    if (finalQty < minQty) {
      logger.warn(`Sequential mode: Quantity ${finalQty} is less than minimum ${minQty}, skipping`);
      isGridPlacing = false;
      gridActive = false;
      return;
    }
    
    const calculatedNotional = finalQty * price;
    if (calculatedNotional < minNotional) {
      logger.warn(`Sequential mode: Notional ${calculatedNotional} is less than minimum ${minNotional}, skipping`);
      isGridPlacing = false;
      gridActive = false;
      return;
    }

    if ((totalNotionalSpent + calculatedNotional) > currentBalance) {
      logger.warn(`Sequential mode: Would exceed current balance, skipping`);
      isGridPlacing = false;
      gridActive = false;
      return;
    }

      try {
        const order = await placeOrder('BUY', finalQty, price);
        activeBuyOrderIds.set(order.orderId, { side: 'BUY', origQty: order.origQty || finalQty, price });
      sequentialOrderIndex = 1; // Следующий ордер будет на индексе 1
      logger.log(`Sequential mode: Order #${sequentialOrderIndex} placed at ${price.toFixed(6)}`);
    } catch (error) {
      logger.error(`Sequential mode: Error placing order: ${error.message}`);
    }
  } else {
    // Режим ALL_AT_ONCE - выставляем все ордера сразу
    for (let i = 0; i < gridPrices.length; i++) {
      const price = gridPrices[i];
      const qty = (FIXED_NOTIONAL * (1 + i * GRID_ORDER_INCREASE_PERCENT)) / price;

      let finalQtyDec = new Decimal(Math.max(minQty, Math.min(maxQty, qty))).dividedBy(new Decimal(stepSize)).floor().times(new Decimal(stepSize));
      let finalQty = finalQtyDec.toNumber();
      
      if (finalQty < minQty) {
        logger.warn(`Grid level ${i+1}: Calculated quantity ${finalQty} is less than minimum ${minQty}, skipping`);
        continue;
      }
      
      const calculatedNotional = finalQty * price;
      if (calculatedNotional < minNotional) {
        logger.warn(`Grid level ${i+1}: Calculated notional ${calculatedNotional} is less than minimum ${minNotional}, skipping`);
        continue;
      }

      if ((totalNotionalSpent + calculatedNotional) > currentBalance) {
        logger.warn(`Grid level ${i+1}: Would exceed current balance, skipping`);
        continue;
      }

      try {
        const order = await placeOrder('BUY', finalQty, price);
        activeBuyOrderIds.set(order.orderId, { side: 'BUY', origQty: order.origQty || finalQty, price });
      } catch (error) {
        logger.error(`Grid level ${i+1}: Error placing order: ${error.message}`);
      }
    }
  }

  isGridPlacing = false;
  operationInProgress = false; // ✅ Освобождаем мьютекс
}

// Выставление следующего ордера в последовательном режиме с мьютексом
async function placeNextSequentialOrder() {
  if (operationInProgress) {
    logger.log('placeNextSequentialOrder: Operation already in progress, skipping');
    return;
  }

  operationInProgress = true;

  try {
    if (ORDER_PLACEMENT_MODE !== 'SEQUENTIAL' || !gridActive) return;

    // Проверяем, есть ли еще ордера для размещения
    if (sequentialOrderIndex >= sequentialGridPrices.length) {
      logger.log('Sequential mode: All orders have been placed');

      // ✅ Если все ордера размещены в SEQUENTIAL режиме, выключаем isGridPlacing
      // чтобы начать отслеживать новый цикл
      isGridPlacing = false;
      gridActive = false;
      logger.log('Sequential mode: Grid placement completed, entering wait mode');
      return;
    }

    const currentBalance = await getBalance();
    const price = sequentialGridPrices[sequentialOrderIndex];
    const qty = (FIXED_NOTIONAL * (1 + sequentialOrderIndex * GRID_ORDER_INCREASE_PERCENT)) / price;

    const lotSize = symbolInfo.filters.find(f => f.filterType === 'LOT_SIZE');
    const notionalFilter = symbolInfo.filters.find(f => f.filterType === 'NOTIONAL');
    const stepSize = parseFloat(lotSize.stepSize);
    const minQty = parseFloat(lotSize.minQty);
    const maxQty = parseFloat(lotSize.maxQty);
    const minNotional = parseFloat(notionalFilter.minNotional);

    let finalQtyDec = new Decimal(Math.max(minQty, Math.min(maxQty, qty))).dividedBy(new Decimal(stepSize)).floor().times(new Decimal(stepSize));
    let finalQty = finalQtyDec.toNumber();

    if (finalQty < minQty) {
      logger.warn(`Sequential mode: Next order quantity ${finalQty} is less than minimum ${minQty}, stopping`);
      isGridPlacing = false;
      gridActive = false;
      return;
    }

    const calculatedNotional = finalQty * price;
    if (calculatedNotional < minNotional) {
      logger.warn(`Sequential mode: Next order notional ${calculatedNotional} is less than minimum ${minNotional}, stopping`);
      isGridPlacing = false;
      gridActive = false;
      return;
    }

    if (calculatedNotional > currentBalance) {
      logger.warn(`Sequential mode: Next order would exceed current balance, stopping`);
      isGridPlacing = false;
      gridActive = false;
      return;
    }

    const order = await placeOrder('BUY', finalQty, price);
    activeBuyOrderIds.set(order.orderId, { side: 'BUY', origQty: order.origQty || finalQty, price });
    sequentialOrderIndex++;
    logger.log(`Sequential mode: Order #${sequentialOrderIndex} placed at ${price.toFixed(6)}`);
  } catch (error) {
    logger.error(`Sequential mode: Error placing next order: ${error.message}`);
  } finally {
    operationInProgress = false; // ✅ Освобождаем мьютекс всегда
  }
}

// ✅ ФУНКЦИЯ УДАЛЕНА - БЫЛ ДУБЛИКАТ placeNextSequentialOrder

// Выставление или обновление ордера на продажу
async function placeOrUpdateSellOrder() {
  logger.log(`Placing or updating sell order: currentDOGEQty=${currentDOGEQty}`);

  if (currentDOGEQty <= 0) {
    logger.warn('No quantity to sell, cancelling existing sell order if any.');
    if (activeSellOrderId) {
      await cancelOrder(activeSellOrderId);
      activeSellOrderId = null;
      logger.log('Old sell order cancelled due to zero DOGE.');
    }
    return;
  }

  if (avgBuyPrice <= 0) {
    logger.warn('Average buy price is not defined, skipping sell order update');
    return;
  }

  try {
    if (activeSellOrderId) {
      await cancelOrder(activeSellOrderId);
      activeSellOrderId = null;
      logger.log('Old sell order cancelled for recalculation.');
    }

    logger.log(`avgBuyPrice: ${avgBuyPrice}, PROFIT_TARGET_PERCENT: ${PROFIT_TARGET_PERCENT}`);

    // ✅ Используем avgBuyPrice как базу для выставления продажи (профит от средней цены)
    let sellPrice = avgBuyPrice * (1 + PROFIT_TARGET_PERCENT / 100);

    logger.log(`calculated sellPrice: ${sellPrice}`);

    const priceFilter = symbolInfo.filters.find(f => f.filterType === 'PRICE_FILTER');
    const minPrice = parseFloat(priceFilter.minPrice);
    const maxPrice = parseFloat(priceFilter.maxPrice);
    logger.log(`priceFilter: min=${minPrice}, max=${maxPrice}`);
    if (sellPrice < minPrice || sellPrice > maxPrice) {
      logger.warn(`Sell price ${sellPrice.toFixed(6)} is out of PRICE_FILTER bounds [${minPrice}, ${maxPrice}], adjusting...`);
      sellPrice = Math.max(minPrice, Math.min(maxPrice, sellPrice));
      logger.log(`adjusted sellPrice: ${sellPrice}`);
    }

    const lotSize = symbolInfo.filters.find(f => f.filterType === 'LOT_SIZE');
    const notionalFilter = symbolInfo.filters.find(f => f.filterType === 'NOTIONAL');
    const stepSize = parseFloat(lotSize.stepSize);
    const minQty = parseFloat(lotSize.minQty);
    const maxQty = parseFloat(lotSize.maxQty);
    const minNotional = parseFloat(notionalFilter.minNotional);

    // ✅ Гарантируем, что продаем всё, что есть, с округлением вниз по stepSize
    let finalQtyDec = new Decimal(currentDOGEQty).dividedBy(new Decimal(stepSize)).floor().times(new Decimal(stepSize));
    let finalQty = finalQtyDec.toNumber();

    if (finalQty < minQty) {
      logger.warn(`Calculated sell quantity ${finalQty} is less than minimum ${minQty}. Cannot place sell order.`);
      logger.log(`Remaining DOGE: ${currentDOGEQty.toFixed(10)}.`);
      // ✅ Если не можем продать — всё равно сбрасываем цикл, чтобы не застрять
      logger.log('Resetting grid state due to insufficient quantity to sell.');
      resetGridState();
      return;
    }

    const calculatedNotional = finalQty * sellPrice;
    if (calculatedNotional < minNotional) {
      logger.warn(`Calculated sell notional ${calculatedNotional} is less than minimum ${minNotional}. Cannot place sell order.`);
      logger.log(`Remaining DOGE: ${currentDOGEQty.toFixed(10)}.`);
      // ✅ Если не можем продать — всё равно сбрасываем цикл, чтобы не застрять
      logger.log('Resetting grid state due to insufficient notional to sell.');
      resetGridState();
      return;
    }

    const order = await placeOrder('SELL', finalQty, sellPrice);
    activeSellOrderId = order.orderId;
    activeSellOrderInfo = { orderId: order.orderId, origQty: order.origQty || finalQty, side: 'SELL', price: sellPrice };
    sellOrderTargetPrice = parseFloat(order.price); // ✅ Сохраняем целевую цену
    logger.log(`New sell order placed: ID=${order.orderId}, Qty=${order.origQty}, Price=${order.price}`);
    logger.log(`Placing sell order for ${finalQty.toFixed(10)} DOGE from current cycle.`);
    logger.log(`Remaining ${ (currentDOGEQty - finalQty).toFixed(10) } DOGE will carry over to next cycle.`);
  } catch (error) {
    logger.error('Error updating sell order: ' + error.message);
    activeSellOrderId = null;
  }
}

// Отмена всех активных ордеров
async function cancelAllActiveOrders() {
  try {
    const timestamp = Date.now();
    const recvWindow = 5000;
    const params = { symbol: 'DOGEFDUSD', timestamp, recvWindow };
    params.signature = signRequest(params);
    const url = `https://api.binance.com/api/v3/openOrders?${new URLSearchParams(params).toString()}`;

    const response = await axios.get(url, { headers: { 'X-MBX-APIKEY': API_KEY } });
    const activeOrders = response.data;

    logger.log(`Found ${activeOrders.length} active orders on Binance`);

    let cancelledCount = 0;
    for (const order of activeOrders) {
      try {
        await cancelOrder(order.orderId);
        cancelledCount++;
      } catch (error) {
        // Игнорируем ошибки для уже отмененных или выполненных ордеров
        const msg = error.response?.data?.msg || error.message || '';
        if (!['does not exist', 'closed', 'not exist', 'already cancelled', 'partially filled', 'filled'].some(s => msg.toLowerCase().includes(s))) {
          logger.error('Error cancelling order ' + order.orderId + ': ' + error.message);
        }
      }
    }

    logger.log(`Successfully cancelled ${cancelledCount} orders from Binance`);

    // Обновляем внутреннее состояние
    activeBuyOrderIds.clear();
    activeSellOrderId = null;
    activeSellOrderInfo = { orderId: null, origQty: 0, side: 'SELL' };

  } catch (error) {
    logger.error('Error fetching/open orders: ' + error.message);
    // Если не удалось получить список, очищаем состояние
    activeBuyOrderIds.clear();
    activeSellOrderId = null;
    activeSellOrderInfo = { orderId: null, origQty: 0, side: 'SELL' };
  }
}

// Сброс состояния сетки
async function resetGridState() {
  logger.log(`Resetting grid state: active buys=${activeBuyOrderIds.size}, sell=${activeSellOrderId ? '1' : '0'}, totalQty=${totalQty.toString()}`);

  await cancelAllActiveOrders();

  gridActive = false;
  // avgBuyPrice и totalNotionalSpent будут пересчитаны на основе оставшегося totalQty и totalBought, если они есть.
  // Поэтому их тоже не сбрасываем жестко в 0, а даем возможность пересчитать.
  avgBuyPrice = totalQty.isZero() ? new Decimal(0) : totalBought.div(totalQty);
  totalNotionalSpent = totalBought;
  initialBalance = 0;
  sellOrderTargetPrice = 0;
  sequentialOrderIndex = 0;
  sequentialGridPrices = [];
  calculatedGridPositions = 0; // Сброс рассчитанного количества ордеров

  // ❌ НЕПРАВИЛЬНО: Это обнуляет "пыль", которая осталась после округления продажи.
  // ✅ ИСПРАВЛЕНИЕ: Убираем полное обнуление. `calculateSimplePnL` уже обновил эти значения.
  // totalQty = new Decimal(0);
  // totalBought = new Decimal(0);

  currentDOGEQty = totalQty.toNumber(); // Синхронизируем с оставшимся количеством
  executedBuyOrders = 0;
  activeSellOrderInfo = { orderId: null, origQty: 0, side: 'SELL' };

  logger.log('Grid cycle completed, all orders cancelled on Binance, state reset. Waiting for next opportunity...');

  cycleStartTime = Date.now();
}

// Получение информации о символе
async function loadSymbolInfo() {
  try {
    const url = 'https://api.binance.com/api/v3/exchangeInfo';
    const response = await axios.get(url);
    const symbol = response.data.symbols.find(s => s.symbol === 'DOGEFDUSD');
    if (!symbol) throw new Error('Symbol DOGEFDUSD not found');
    symbolInfo = symbol;
    logger.log('Symbol info loaded:', symbol.symbol);
    const priceFilter = symbol.filters.find(f => f.filterType === 'PRICE_FILTER');
    tickSize = parseFloat(priceFilter.tickSize);
    logger.log(`Tick size set to: ${tickSize}`);
    return symbol;
  } catch (error) {
    logger.error('Error loading symbol info: ' + error.message);
    throw error;
  }
}

// Подключение к WebSocket 5-минутных свечей
function connectKlineStream() {
  if (klineWs) klineWs.close();
  const wsUrl = 'wss://stream.binance.com:9443/ws/dogefdusd@kline_5m';
  logger.log(`Connecting to 5min kline WebSocket: ${wsUrl}`);
  klineWs = new WebSocket(wsUrl);
  klineWs.on('open', () => {
    logger.log('5min kline WebSocket connected for DOGEFDUSD');
  });
  klineWs.on('message', handleKlineMessage);
  klineWs.on('close', (code, reason) => {
    logger.warn(`5min kline WebSocket closed (${code}): ${reason}, reconnecting...`);
    setTimeout(connectKlineStream, 5000);
  });
  klineWs.on('error', (err) => {
    logger.error('5min kline WebSocket error: ' + err.message);
    setTimeout(connectKlineStream, 5000);
  });
}

// Обработка сообщений kline
function handleKlineMessage(data) {
  if (!GRID_STEP_AUTO_ENABLED) return;

  try {
    const msg = JSON.parse(data);
    if (msg.e === 'kline') {
      const kline = msg.k;
      if (kline.s === 'DOGEFDUSD' && kline.x) {
        const high = parseFloat(kline.h);
        const low = parseFloat(kline.l);
        const step = (high - low) * (GRID_STEP_AUTO_PERCENT / 100) / tickSize;

        let newStep = Math.round(step);
        newStep = Math.max(GRID_STEP_MIN_TICKS, Math.min(GRID_STEP_MAX_TICKS, newStep));

        GRID_STEP_TICKS = newStep;
        logger.log(`Auto step updated: ${newStep} ticks (from high=${high}, low=${low})`);
      }
    }
  } catch (e) {
    logger.error('Error processing kline message: ' + e.message);
  }
}

// --- ДАШБОРД ---
// Кэширование баланса для снижения API вызовов
let cachedBalance = 0;
let lastBalanceUpdate = 0;
const BALANCE_CACHE_TIME = 30000; // 30 секунд

async function getCachedBalance() {
  const now = Date.now();
  if (now - lastBalanceUpdate > BALANCE_CACHE_TIME || cachedBalance === 0) {
    try {
      cachedBalance = await getBalance();
      lastBalanceUpdate = now;
    } catch (error) {
      logger.warn('Failed to update balance cache: ' + error.message);
      // В случае ошибки возвращаем предыдущее кэшированное значение
    }
  }
  return cachedBalance;
}

// Валидация конфигурации при запуске
function validateConfiguration() {
  const issues = [];

  if (PROFIT_TARGET_PERCENT <= 0 || PROFIT_TARGET_PERCENT > 10) {
    issues.push('PROFIT_TARGET_PERCENT must be between 0.01 and 10');
  }

  if (FIXED_NOTIONAL < 1 || FIXED_NOTIONAL > 1000) {
    issues.push('FIXED_NOTIONAL must be between 1 and 1000');
  }

  if (MAX_GRID_POSITIONS < 1 || MAX_GRID_POSITIONS > 50) {
    issues.push('MAX_GRID_POSITIONS must be between 1 and 50');
  }

  if (GRID_ORDER_INCREASE_PERCENT < 0 || GRID_ORDER_INCREASE_PERCENT > 1) {
    issues.push('GRID_ORDER_INCREASE_PERCENT must be between 0 and 1');
  }

  if (GRID_STEP_BASE_TICKS < 10 || GRID_STEP_BASE_TICKS > 200) {
    issues.push('GRID_STEP_BASE_TICKS must be between 10 and 200');
  }

  if (!['LINEAR', 'NONLINEAR'].includes(GRID_MODE)) {
    issues.push('GRID_MODE must be either "LINEAR" or "NONLINEAR"');
  }

  if (!['ALL_AT_ONCE', 'SEQUENTIAL'].includes(ORDER_PLACEMENT_MODE)) {
    issues.push('ORDER_PLACEMENT_MODE must be either "ALL_AT_ONCE" or "SEQUENTIAL"');
  }

  if (issues.length > 0) {
    console.error('Configuration validation failed:');
    issues.forEach(issue => console.error('  - ' + issue));
    process.exit(1);
  }

  logger.log('Configuration validation passed');
}

// Graceful shutdown
process.on('SIGINT', () => {
  logger.log('Received SIGINT, shutting down gracefully...');
  shutdown();
});

process.on('SIGTERM', () => {
  logger.log('Received SIGTERM, shutting down gracefully...');
  shutdown();
});

async function shutdown() {
  logger.log('Cancelling all active orders before shutdown...');
  try {
    await cancelAllActiveOrders();
    logger.log('All orders cancelled successfully');
  } catch (error) {
    logger.error('Error cancelling orders during shutdown: ' + error.message);
  }

  logger.log('Saving final PnL data...');
  try {
    savePnLData();
    logger.log('PnL data saved successfully');
  } catch (error) {
    logger.error('Error saving PnL data during shutdown: ' + error.message);
  }

  logger.log('Shutdown complete');
  process.exit(0);
}

// --- ДАШБОРД ---
async function updateDashboard() {
  if (!isInitialized) return;

  const currentCycleOrders = activeBuyOrderIds.size;
  const sellTargetPrice = avgBuyPrice * (1 + PROFIT_TARGET_PERCENT / 100);
  const cycleStart = cycleStartTime ? new Date(cycleStartTime).toISOString() : 'N/A';

  // Рассчитываем нереализованный PnL текущего цикла
  const unrealizedPnL = totalQty > 0 ? totalQty * (bookTicker.bestBid - avgBuyPrice) : 0;

  // Получаем баланс из кэша для снижения API вызовов
  const currentBalance = await getCachedBalance();

  // Рассчитываем периодическую прибыль (обновляем текущие периоды)
  const now = new Date();

  // Проверяем, прошел ли день
  if (lastDayTimestamp && (now - lastDayTimestamp) >= 24 * 60 * 60 * 1000) {
    // Сохраняем текущий общий PnL как прибыль за прошедший день
    currentDayPnL = totalPnL.minus(new Decimal(lastDayTotalPnL || 0));
    lastDayTotalPnL = totalPnL.toString(); // Обновляем базовое значение
    lastDayTimestamp = now;
    logger.log(`Day P&L: ${currentDayPnL.toFixed(6)} FDUSD (total: ${totalPnL.toFixed(6)})`);
  }

  // Проверяем, прошла ли неделя
  if (lastWeekTimestamp && (now - lastWeekTimestamp) >= 7 * 24 * 60 * 60 * 1000) {
    currentWeekPnL = totalPnL.minus(new Decimal(lastWeekTotalPnL || 0));
    lastWeekTotalPnL = totalPnL.toString();
    lastWeekTimestamp = now;
    logger.log(`Week P&L: ${currentWeekPnL.toFixed(6)} FDUSD (total: ${totalPnL.toFixed(6)})`);
  }

  // Проверяем, прошел ли месяц
  if (lastMonthTimestamp && (now - lastMonthTimestamp) >= 30 * 24 * 60 * 60 * 1000) {
    currentMonthPnL = totalPnL.minus(new Decimal(lastMonthTotalPnL || 0));
    lastMonthTotalPnL = totalPnL.toString();
    lastMonthTimestamp = now;
    logger.log(`Month P&L: ${currentMonthPnL.toFixed(6)} FDUSD (total: ${totalPnL.toFixed(6)})`);
  }

  console.clear();

  const cycleElapsedMin = cycleStartTime ? (Date.now() - cycleStartTime) / 1000 / 60 : 0;
  const botElapsedHours = botStartTime ? (Date.now() - botStartTime) / 1000 / 60 / 60 : 0;

  console.log(`\x1b[35m=== ДАШБОРД ГРИД ТОРГОВЛИ ===\x1b[0m`);
  console.log(`\x1b[36mВремя Цикла:\x1b[0m ${cycleElapsedMin.toFixed(1)} мин, Бота: ${botElapsedHours.toFixed(2)} ч`);
  console.log(`\x1b[36mЦиклы:\x1b[0m ${totalCycles}, Подтяжек: ${totalGridPulls}`);
  console.log(`\x1b[36mРежим:\x1b[0m ${ORDER_PLACEMENT_MODE} | ${GRID_MODE}`);
  console.log(`\x1b[36mАвтошаг:\x1b[0m ${GRID_STEP_AUTO_ENABLED ? 'Да' : 'Нет'} (${GRID_STEP_TICKS} тиков)`);
  console.log(`\x1b[36mЦена Bid:\x1b[0m ${bookTicker.bestBid ? bookTicker.bestBid.toFixed(6) : 'N/A'}`);
  console.log(`\x1b[36mСредняя Цена:\x1b[0m ${avgBuyPrice.toFixed(6)}`);
  console.log(`\x1b[36mЦена профита:\x1b[0m ${sellTargetPrice.toFixed(6)}`);
  console.log(`\x1b[36mDOGE Кол-во:\x1b[0m ${currentDOGEQty.toFixed(6)} (${activeSellOrderInfo.origQty || '0'} на ордер)`);
  console.log(`\x1b[36mБаланс:\x1b[0m ${currentBalance.toFixed(6)} FDUSD`);
  console.log(`\x1b[36mБаланс в сетке:\x1b[0m ${totalNotionalSpent.toFixed(6)} FDUSD`);
  console.log(`\x1b[36mАктивных Ордеров:\x1b[0m ${currentCycleOrders}, Рассчитано: ${calculatedGridPositions}`);
  console.log(`\x1b[36mИсполнено:\x1b[0m ${executedBuyOrders}`);
  console.log(`\x1b[36mСтатус:\x1b[0m ${gridActive ? 'Активен' : 'Ожидание'}`);
  console.log(`\x1b[36mНастройки:\x1b[0m Профит ${PROFIT_TARGET_PERCENT.toFixed(1)}%, БазОрдер ${FIXED_NOTIONAL}, МаксОрдер ${MAX_GRID_POSITIONS}, МнжБаз ${(GRID_ORDER_INCREASE_PERCENT * 100).toFixed(1)}%, МнжСет ${NONLINEAR_MULTIPLIER}, Подтяж ${GRID_PULL_DELAY_MINUTES}м, Отст ${GRID_BASE_OFFSET_TICKS}т`);
  console.log('');
  console.log(`\x1b[32mНереализованная прибыль:\x1b[0m ${unrealizedPnL.toFixed(6)} FDUSD`);
  console.log(`\x1b[33mРеализованная прибыль:\x1b[0m ${totalPnL.toFixed(6)} FDUSD`);
  console.log(`\x1b[36mПрибыль За 24 часа: ${currentDayPnL.toFixed(6)} FDUSD, За неделю: ${currentWeekPnL.toFixed(6)} FDUSD, За месяц: ${currentMonthPnL.toFixed(6)} FDUSD\x1b[0m`);
  console.log('');

  if (activeBuyOrderIds.size > 0 || activeSellOrderId) {
    console.log('\x1b[37mАктивные Ордера:\x1b[0m');
    const activeOrders = [];
    let buyIndex = 0;
    for (const [orderId, info] of activeBuyOrderIds.entries()) {
      activeOrders.push({ 'ID Ордера': orderId, 'Сторона': info.side, 'Кол-во': info.origQty, 'Цена': info.price, 'Стоимость': (info.origQty * info.price).toFixed(2) + ' FDUSD', 'Прирост %': (buyIndex++ * GRID_ORDER_INCREASE_PERCENT * 100).toFixed(1) + '%' });
    }
    if (activeSellOrderInfo.orderId) {
      const sellNotional = activeSellOrderInfo.price ? (activeSellOrderInfo.origQty * activeSellOrderInfo.price).toFixed(2) + ' FDUSD' : '';
      activeOrders.push({ 'ID Ордера': activeSellOrderInfo.orderId, 'Сторона': activeSellOrderInfo.side, 'Кол-во': activeSellOrderInfo.origQty, 'Цена': activeSellOrderInfo.price, 'Стоимость': sellNotional, 'Прирост %': '-' });
    }
    console.table(activeOrders);
  }

  console.log('\x1b[37mЛоги:\x1b[0m');
}

// Инициализация бота
async function init() {
  try {
    logger.log('Starting Binance Trading Bot (Simple Grid Strategy with AVG, Filters, Simple PnL, and Order Cleanup)...');

    // Валидация конфигурации перед запуском
    validateConfiguration();

    await loadSymbolInfo();

    listenKey = await getListenKey();
    setInterval(keepAliveListenKey, 30 * 60 * 1000);

    logger.log('Cancelling all active orders...');
    await cancelAllActiveOrders();
    activeSellOrderInfo = { orderId: null, origQty: 0, side: 'SELL' };

    connectUserDataStream();
    connectBookTicker();
    if (GRID_STEP_AUTO_ENABLED) {
      connectKlineStream();
    } else {
      logger.log('Auto step disabled, skipping kline WebSocket connection');
    }

    isInitialized = true;
    logger.log('Bot initialized successfully');
    botStartTime = Date.now();
    cycleStartTime = Date.now();

    // Настройки периодов для прибыли (инициализация, если не загружено из файла)
    const now = new Date();
    if (!lastDayTimestamp) lastDayTimestamp = new Date();
    if (!lastWeekTimestamp) lastWeekTimestamp = new Date();
    if (!lastMonthTimestamp) lastMonthTimestamp = new Date();

    setInterval(async () => {
      await updateDashboard();
    }, 3000);
  } catch (error) {
    logger.error('Initialization error: ' + error.message);
    process.exit(1);
  }
}

init().catch(error => {
  logger.error('Critical error: ' + error.message);
  process.exit(1);
});
