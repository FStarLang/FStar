@echo off
rem Wrapper to locate and run MSBuild on Windows
rem
rem Checking Visual Studio 2017 first
rem Taken from:
rem https://github.com/Microsoft/vswhere
rem The tokens trick is documented in for /?
rem In particular, declaring variable %%x but using variable %%y is INTENDED:
rem %%j is implicitly declared by *, its name is chosen because it is "after" %%i
set VsWhere="%ProgramFiles(x86)%\Microsoft Visual Studio\Installer\vswhere.exe"
if not exist %VsWhere% goto vs2015
for /f "usebackq tokens=1* delims=: " %%i in (`%VsWhere% -latest -requires Microsoft.Component.MSBuild`) do (
  if /i "%%i"=="installationPath" set InstallDir=%%j
)
if "%InstallDir%" == "" goto vs2015
"%InstallDir%\MSBuild\15.0\Bin\MSBuild.exe" %*
if errorlevel 1 exit /b 1
goto end

:vs2015
rem Not found. Assuming Visual Studio 2015 now.
rem Same remarks as above re. %%x vs. %%y
for /f "tokens=2,*" %%x in ('reg.exe query "HKLM\Software\Microsoft\MSBuild\ToolsVersions\14.0" /v MSBuildToolsPath ^| findstr /ri "REG_SZ"') do set msbuildpath=%%y
if "%msbuildpath%" == "" exit /b 1
"%msbuildpath%\msbuild.exe" %*
if errorlevel 1 exit /b 1

:end
