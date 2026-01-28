#!/bin/bash
# Portable version file generation - works on Windows (Git Bash/Cygwin) and Unix

set -e

VERSION_FILE="$1"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

# Find Python - portable across Linux, macOS, Windows (cygwin)
PYTHON=''
for p in python3 python; do
  if command -v $p >/dev/null 2>&1; then PYTHON=$p; break; fi
done

# On Windows/cygwin, search Windows Store apps
if [ -z "$PYTHON" ]; then
  for u in /cygdrive/c/Users/*/AppData/Local/Microsoft/WindowsApps/python.exe; do
    if [ -x "$u" ]; then PYTHON="$u"; break; fi
  done
fi

# Try common Windows Python locations
if [ -z "$PYTHON" ]; then
  for u in /cygdrive/c/Python*/python.exe /cygdrive/c/ProgramData/Anaconda*/python.exe; do
    if [ -x "$u" ]; then PYTHON="$u"; break; fi
  done
fi

if [ -z "$PYTHON" ]; then
  echo "Error: Python not found" >&2
  exit 1
fi

# Convert paths to Windows format if on cygwin
if command -v cygpath >/dev/null 2>&1; then
  SCRIPT=$(cygpath -w "$SCRIPT_DIR/make_version.py")
  VERSION_FILE=$(cygpath -w "$VERSION_FILE")
else
  SCRIPT="$SCRIPT_DIR/make_version.py"
fi

exec "$PYTHON" "$SCRIPT" "$VERSION_FILE"
