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
rem PLATFORM must be unset in VS2017, otherwise
rem MSBuild complains about "Solution configuration Release|X64 invalid"
set PLATFORM=
rem We first have to properly set up the environment through VsDevCmd
rem NOTE: the current directory has to be saved prior to calling VsDevCmd
set VSCMD_START_DIR=%CD%
rem TODO: change the platform as needed
call "%InstallDir%\Common7\Tools\VsDevCmd.bat" -arch=amd64 -host_arch=amd64
if errorlevel 1 exit /b 1
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
