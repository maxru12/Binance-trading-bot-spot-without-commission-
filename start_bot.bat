@echo off
chcp 65001 >nul
echo ========================================
echo    Binance Grid Trading Bot
echo ========================================
echo.
echo Current directory: %CD%
echo Starting bot...
echo.

REM Проверяем наличие .env файла
if not exist ".env" (
    echo ERROR: .env file not found!
    echo Please create .env file with your Binance API keys
    echo.
    echo Required variables:
    echo   BINANCE_API_KEY=your_api_key
    echo   BINANCE_SECRET_KEY=your_secret_key
    echo.
    pause
    exit /b 1
)

REM Проверяем наличие node_modules
if not exist "node_modules" (
    echo Installing dependencies...
    npm install
    if errorlevel 1 (
        echo ERROR: Failed to install dependencies
        pause
        exit /b 1
    )
)

echo Starting bot in production mode...
node bot.js

echo.
echo ========================================
echo Bot stopped.
echo Press any key to close this window.
echo ========================================
pause
