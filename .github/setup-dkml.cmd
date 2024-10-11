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

REM Install DkML compiler including MSYS2
:HavePowershellExe
SET OPAMYES=1
REM     TODO: Use [dkml-workflows] not [dkml-workflows-prerelease] once 2.1.2 is merged
if NOT EXIST dkml-workflows (
    IF NOT EXIST dkml-workflows-2.1.2.zip (
        powershell -NoProfile -ExecutionPolicy Bypass -Command "(New-Object Net.WebClient).DownloadFile('https://github.com/diskuv/dkml-workflows-prerelease/archive/refs/tags/2.1.2.zip', 'dkml-workflows-2.1.2.zip')"
    )
    powershell -NoProfile -ExecutionPolicy Bypass -Command "Expand-Archive -Force dkml-workflows-2.1.2.zip"
    move dkml-workflows-2.1.2\dkml-workflows-prerelease-2.1.2 dkml-workflows
    rmdir dkml-workflows-2.1.2
)
IF NOT EXIST .ci\o\dkml\bin\ocamlc.exe (
    "%INTERNAL_POWERSHELLEXE%" -NoProfile -ExecutionPolicy Bypass -Command "& dkml-workflows\test\pc\setup-dkml-windows_x86_64.ps1 %*; exit $LASTEXITCODE"
)
if %ERRORLEVEL% neq 0 (
    echo.
    echo.Failed to build OCaml compiler from DkML distribution.
    echo.Exit code: %ERRORLEVEL%
    echo.
    exit /b 1
)

REM Install MSYS2's zip.exe so `make package` works
if NOT EXIST msys64\usr\bin\zip.exe (
    msys64\usr\bin\pacman -Sy --noconfirm --needed zip
)
exit /b %ERRORLEVEL%
