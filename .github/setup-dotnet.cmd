@ECHO OFF

REM Use PowerShell 7+ rather than built-in PowerShell 5 since, for Get-PackageProvider, the PowerShell 5 module path includes conflicting version 7 modules.

REM     Find PWSH.EXE
where.exe /q pwsh.exe >NUL 2>NUL
if %ERRORLEVEL% neq 0 (
    goto NeedPowershellExe
)
FOR /F "tokens=* usebackq" %%F IN (`where.exe pwsh.exe`) DO (
SET "INTERNAL_PWSHEXE=%%F"
)
"%INTERNAL_PWSHEXE%" -NoLogo -Help >NUL 2>NUL
if %ERRORLEVEL% equ 0 (
    SET "INTERNAL_POWERSHELLEXE=%INTERNAL_PWSHEXE%"
    goto HavePowershellExe
)

REM     Find Powershell.EXE
:NeedPowershellExe
FOR /F "tokens=* usebackq" %%F IN (`where.exe powershell.exe`) DO (
SET "INTERNAL_POWERSHELLEXE=%%F"
)
"%INTERNAL_POWERSHELLEXE%" -NoLogo -Help >NUL 2>NUL
if %ERRORLEVEL% neq 0 (
	echo.
	echo.Neither 'pwsh.exe' nor 'powershell.exe' were found. Make sure you have
	echo.PowerShell installed.
	echo.
	exit /b 1
)

REM Install Microsoft.DotNet.SDK.6 (major version of ulib\fs\VS\global.json)
:HavePowershellExe
IF NOT EXIST dotnet\dotnet.exe (
    "%INTERNAL_POWERSHELLEXE%" -NoProfile -ExecutionPolicy Bypass -Command "Invoke-WebRequest 'https://dot.net/v1/dotnet-install.ps1' -OutFile dotnet-install.ps1"
    REM     Use `winget search Microsoft.DotNet.SDK` to search versions
    "%INTERNAL_POWERSHELLEXE%" -NoProfile -ExecutionPolicy Bypass -Command "./dotnet-install.ps1 -InstallDir 'dotnet' -Version '6.0.425'"
)
