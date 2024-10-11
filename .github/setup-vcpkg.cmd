@ECHO OFF

if NOT EXIST vcpkg (
    git clone https://github.com/microsoft/vcpkg.git
)
IF NOT EXIST vcpkg\vcpkg.exe (
    cd vcpkg && CALL bootstrap-vcpkg.bat -disableMetrics && cd ..
)

REM Make CI-friendly binary cache at vcpkg\archive
SET VCPKG_BINARY_SOURCES=clear;files,%CD%\vcpkg\archive,readwrite

REM Install to vcpkg_installed (which is the primary thing to be cached in CI)
REM     TODO: This uses the default x64-windows triplet, but that builds both Debug and Release.
REM     Confer: https://github.com/microsoft/vcpkg/issues/10683#issuecomment-1968853554
IF NOT EXIST vcpkg_installed\x64-windows\lib\pkgconfig\gmp.pc (
    vcpkg\vcpkg install --x-install-root=%CD%\vcpkg_installed gmp
)
