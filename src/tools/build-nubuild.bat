@echo off
setlocal enabledelayedexpansion
set A=!%1!
call "%A%\..\..\VC\bin\vcvars32.bat"
MsBuild.exe /nologo /verbosity:minimal NuBuild.sln
