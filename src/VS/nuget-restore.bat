@echo off
pushd %~dp0
dotnet tool restore
dotnet paket install
dotnet restore %~dp0\fstar.sln
popd