#!/bin/bash
# Portable Python runner that works on Windows (via cygpath) and Unix

# Get project root from first argument
PROJECT_ROOT="$1"
shift

# Convert path to native format (Windows needs forward slashes for Python)
to_native_path() {
    if command -v cygpath >/dev/null 2>&1; then
        cygpath -m "$1"
    elif command -v realpath >/dev/null 2>&1; then
        realpath "$1"
    else
        # Fallback for macOS which may not have realpath
        (cd "$(dirname "$1")" 2>/dev/null && echo "$(pwd)/$(basename "$1")") || echo "$1"
    fi
}

# Find Python - try python3 first, then python
find_python() {
    if command -v python3 >/dev/null 2>&1; then
        which python3
    elif command -v python >/dev/null 2>&1; then
        which python
    else
        echo "Error: Python not found" >&2
        exit 1
    fi
}

PYTHON=$(find_python)
NATIVE_ROOT=$(to_native_path "$PROJECT_ROOT")

# Run the script with native paths
exec "$PYTHON" "$@"
