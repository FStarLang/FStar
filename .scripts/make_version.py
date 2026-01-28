#!/usr/bin/env python3
"""Generate FStarC_Version.ml with version information.

This script is a portable replacement for make_fstar_version.sh.
"""

import os
import platform
import subprocess
import sys


def get_version(version_file):
    """Read version from version.txt."""
    try:
        with open(version_file, 'r') as f:
            return f.readline().strip() + "~dev"
    except FileNotFoundError:
        return "unknown"


def get_platform():
    """Get platform string."""
    system = platform.system()
    machine = platform.machine()
    
    if system == "Windows":
        if machine == "AMD64":
            return "Windows_x64"
        else:
            return "Windows_x86"
    else:
        return f"{system}_{machine}"


def get_compiler():
    """Get OCaml compiler version."""
    try:
        result = subprocess.run(['ocamlc', '-version'], 
                              capture_output=True, text=True, timeout=10)
        if result.returncode == 0:
            return f"OCaml {result.stdout.strip()}"
    except Exception:
        pass
    return "OCaml unknown"


def get_git_commit():
    """Get git commit hash."""
    commit = os.environ.get('FSTAR_COMMIT')
    if commit:
        return commit
    try:
        result = subprocess.run(
            ['git', 'describe', '--match=', '--always', '--abbrev=40', '--dirty'],
            capture_output=True, text=True, timeout=10
        )
        if result.returncode == 0:
            return result.stdout.strip()
    except Exception:
        pass
    return "unset"


def get_git_date():
    """Get git commit date."""
    date = os.environ.get('FSTAR_COMMITDATE')
    if date:
        return date
    try:
        result = subprocess.run(
            ['git', 'log', '--pretty=format:%ci', '-n', '1'],
            capture_output=True, text=True, timeout=10
        )
        if result.returncode == 0:
            return result.stdout.strip()
    except Exception:
        pass
    return "unset"


def main():
    # Find version.txt
    version_file = 'version.txt'
    if len(sys.argv) > 1:
        version_file = sys.argv[1]
    
    version = os.environ.get('FSTAR_VERSION', get_version(version_file))
    plat = get_platform()
    compiler = get_compiler()
    commit = get_git_commit()
    date = get_git_date()
    
    # Output OCaml code
    # Add a dummy value that can be referenced to force this module to be linked
    print('let dummy = ()')
    print(f'let () = FStarC_Options._version := "{version}"')
    print(f'let () = FStarC_Options._platform := "{plat}"')
    print(f'let () = FStarC_Options._compiler := "{compiler}"')
    print(f'let () = FStarC_Options._date := "{date}"')
    print(f'let () = FStarC_Options._commit := "{commit}"')


if __name__ == '__main__':
    main()
