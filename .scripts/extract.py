#!/usr/bin/env python3
"""
F* Extraction Script - Portable across Windows, Linux, macOS

This script extracts OCaml code from F* sources, handling the --MLish
flag correctly for FStarC modules vs FStar library modules.

The approach:
1. First verify FStar.* library files (without --MLish) to populate cache
2. Then verify FStarC.Effect (the special effect module for MLish mode)
3. Then verify remaining FStarC.* modules (with --MLish)
4. Finally extract all modules using cached verification

Usage:
    python extract.py --fstar <path/to/fstar.exe> --output-dir <output>
"""

import subprocess
import sys
import os
import argparse
import re
from pathlib import Path

def run_fstar(fstar_exe, args, verbose=False):
    """Run fstar with given arguments."""
    cmd = [str(fstar_exe)] + args
    if verbose:
        print(f"  $ {' '.join(cmd[:8])}...", file=sys.stderr)
    result = subprocess.run(cmd, capture_output=True, text=True)
    return result.returncode == 0, result.stdout, result.stderr

def parse_depend_full(output):
    """Parse --dep full output to get source files to extract."""
    # The output has sections like:
    # ALL_ML_FILES= \
    #     FStar_Pervasives.ml \
    #     FStarC_Options.ml
    # 
    # ALL_FST_FILES= \
    #     path/to/file.fst
    
    ml_files = []
    fst_files = {}  # module_name -> path
    
    in_ml_section = False
    in_fst_section = False
    
    for line in output.split('\n'):
        stripped = line.strip().rstrip('\\').strip()
        
        if 'ALL_ML_FILES=' in line:
            in_ml_section = True
            in_fst_section = False
            continue
        elif 'ALL_FST_FILES=' in line:
            in_fst_section = True
            in_ml_section = False
            continue
        elif '=' in line and not stripped.endswith('.ml') and not stripped.endswith('.fst'):
            in_ml_section = False
            in_fst_section = False
            continue
        
        if in_ml_section and stripped.endswith('.ml'):
            ml_files.append(stripped)
        elif in_fst_section and (stripped.endswith('.fst') or stripped.endswith('.fsti')):
            # Extract module name from path
            # e.g., C:/path/to/FStarC.Options.fst -> FStarC.Options
            basename = Path(stripped).stem  # FStarC.Options
            fst_files[basename] = stripped
    
    # Match ML files to source files
    extract_files = []
    for ml_file in ml_files:
        # FStar_Pervasives.ml -> FStar.Pervasives
        module_name = Path(ml_file).stem.replace('_', '.')
        extract_files.append((ml_file, module_name))
    
    return extract_files

def verify_file(fstar_exe, includes, cache_dir, src_file, use_mlish):
    """Verify a single F* file and cache the result.
    
    Args:
        use_mlish: If True, add --MLish flag
    
    Note: We don't use --already_cached for verification because F* will
    automatically use cached .checked.lax files when available. The key is
    that ulib was cached WITHOUT --MLish, so when verifying FStarC modules
    WITH --MLish, F* loads the cached ulib files without re-verifying them.
    """
    args = [
        '--lax',
        '-c',
        '--cache_dir', str(cache_dir),
        '--warn_error', '-285-239-241-271-247',
        '--admit_smt_queries', 'true',
    ]
    if use_mlish:
        args.extend(['--MLish', '--MLish_effect', 'FStarC.Effect'])
    else:
        args.extend(['--MLish_effect', 'FStarC.Effect'])
    
    for inc in includes:
        args.extend(['--include', inc])
    args.append(str(src_file))
    
    success, stdout, stderr = run_fstar(fstar_exe, args)
    return success, stderr

def extract_file(fstar_exe, includes, cache_dir, output_dir, src_file, extract_module, use_mlish):
    """Extract OCaml code from a single F* file.
    
    Note: We don't use --already_cached for extraction. F* will use cached
    .checked.lax files when available, and verify any missing dependencies.
    """
    args = [
        '--lax',
        '--codegen', 'OCaml',
        '--odir', str(output_dir),
        '--cache_dir', str(cache_dir),
        '--warn_error', '-285-239-241-271-247',
        '--admit_smt_queries', 'true',
        '--extract', extract_module,
    ]
    if use_mlish:
        args.extend(['--MLish', '--MLish_effect', 'FStarC.Effect'])
    else:
        args.extend(['--MLish_effect', 'FStarC.Effect'])
    
    for inc in includes:
        args.extend(['--include', inc])
    args.append(str(src_file))
    
    success, stdout, stderr = run_fstar(fstar_exe, args)
    return success, stdout + stderr

def find_source_file(includes, module_name):
    """Find the source file for a module."""
    for inc_str in includes:
        inc = Path(inc_str)
        for ext in ['.fst', '.fsti']:
            candidate = inc / f"{module_name}{ext}"
            if candidate.exists():
                return candidate
    return None

def main():
    parser = argparse.ArgumentParser(description='Extract OCaml from F* sources')
    parser.add_argument('--fstar', required=True, help='Path to fstar.exe')
    parser.add_argument('--output-dir', required=True, help='Output directory for .ml files')
    parser.add_argument('--project-root', default='.', help='Project root directory')
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output')
    args = parser.parse_args()
    
    fstar_exe = Path(args.fstar).resolve()
    output_dir = Path(args.output_dir).resolve()
    project_root = Path(args.project_root).resolve()
    
    # Directories
    src_dir = project_root / 'src'
    ulib_dir = project_root / 'ulib'
    cache_dir = project_root / '_build' / 'default' / '.cache' / 'extract'
    
    # Create directories
    cache_dir.mkdir(parents=True, exist_ok=True)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # Include paths (as strings for consistency)
    includes = [
        str(ulib_dir),
        str(src_dir / 'basic'),
        str(src_dir / 'class'),
        str(src_dir / 'data'),
        str(src_dir / 'extraction'),
        str(src_dir / 'fstar'),
        str(src_dir / 'interactive'),
        str(src_dir / 'parser'),
        str(src_dir / 'prettyprint'),
        str(src_dir / 'reflection'),
        str(src_dir / 'smtencoding'),
        str(src_dir / 'syntax'),
        str(src_dir / 'syntax' / 'print'),
        str(src_dir / 'tactics'),
        str(src_dir / 'tosyntax'),
        str(src_dir / 'typechecker'),
        str(src_dir / 'tests'),
    ]
    
    include_args = []
    for inc in includes:
        include_args.extend(['--include', inc])
    
    root_file = str(src_dir / 'fstar' / 'FStarC.Main.fst')
    
    # Common flags
    common_flags = [
        '--lax',
        '--cache_dir', str(cache_dir),
        '--warn_error', '-285-239-241-271-247',
        '--admit_smt_queries', 'true',
    ]
    
    extract_filters = [
        '--extract', 'FStarC',
        '--extract', '+FStar.Pervasives',
        '--extract', '-FStar.Pervasives.Native',
    ]
    
    print("Step 1: Getting dependency graph...", file=sys.stderr)
    dep_args = common_flags + include_args + ['--dep', 'full'] + extract_filters + [root_file]
    success, stdout, stderr = run_fstar(fstar_exe, dep_args, verbose=args.verbose)
    if not success:
        print(f"Failed to get dependencies:\n{stderr}", file=sys.stderr)
        return 1
    
    extract_files = parse_depend_full(stdout)
    print(f"Found {len(extract_files)} files to extract", file=sys.stderr)
    
    if len(extract_files) == 0:
        print("Warning: No extraction targets found, showing sample:", file=sys.stderr)
        for line in stdout.split('\n')[:20]:
            if '.ml' in line:
                print(f"  {line}", file=sys.stderr)
    
    # Build a list of modules to verify and extract
    to_process = []  # (ml_target, module_name, source_file, use_mlish)
    
    for ml_target, module_name in extract_files:
        use_mlish = module_name.startswith('FStarC.')
        
        source_file = find_source_file(includes, module_name)
        if source_file:
            to_process.append((ml_target, module_name, source_file, use_mlish))
        else:
            print(f"  Warning: Could not find source for {module_name}", file=sys.stderr)
    
    # Phase 1: Verify ALL ulib files (WITHOUT --MLish)
    # This is critical - we must cache ALL ulib dependencies before using --MLish
    # because --MLish affects the semantics of verification
    print(f"\nStep 2: Verifying all ulib files (no MLish)...", file=sys.stderr)
    
    # Get all .fst and .fsti files in ulib
    ulib_files = []
    for ext in ['*.fst', '*.fsti']:
        ulib_files.extend(ulib_dir.glob(ext))
    
    print(f"  Found {len(ulib_files)} ulib files to verify", file=sys.stderr)
    
    # Verify all ulib files (without --MLish)
    for i, ulib_file in enumerate(sorted(ulib_files)):
        if i % 10 == 0:  # Progress every 10 files
            print(f"  [{i+1}/{len(ulib_files)}] Verifying {ulib_file.name}...", file=sys.stderr)
        verify_file(fstar_exe, includes, cache_dir, ulib_file, use_mlish=False)
    
    print(f"  Verified {len(ulib_files)} ulib files", file=sys.stderr)
    
    # Phase 2: Verify FStarC.Effect (WITH --MLish, but use already_cached for ulib deps)
    print(f"\nStep 3: Verifying FStarC.Effect (MLish with already_cached)...", file=sys.stderr)
    effect_path = src_dir / 'basic' / 'FStarC.Effect.fsti'
    if effect_path.exists():
        verify_file(fstar_exe, includes, cache_dir, effect_path, use_mlish=True)
    
    # Phase 3: Verify and extract all modules
    # F* will automatically use cached .checked.lax files
    print(f"\nStep 4: Verifying and extracting {len(to_process)} files...", file=sys.stderr)
    
    extracted = 0
    errors = []
    
    for i, (ml_target, module_name, source_file, use_mlish) in enumerate(to_process):
        mlish_str = "[MLish]" if use_mlish else ""
        print(f"  [{i+1}/{len(to_process)}] {module_name} -> {ml_target} {mlish_str}", file=sys.stderr)
        
        # First verify
        success, stderr_out = verify_file(fstar_exe, includes, cache_dir, source_file, use_mlish)
        if not success:
            errors.append((module_name, "verify", stderr_out))
            # Continue to try extraction anyway with already_cached
        
        # Then extract
        success, output = extract_file(fstar_exe, includes, cache_dir, output_dir, 
                                       source_file, module_name, use_mlish)
        if success and 'Extracted module' in output:
            extracted += 1
        elif not success:
            errors.append((module_name, "extract", output))
    
    # Count actual .ml files
    ml_files = list(output_dir.glob('*.ml'))
    print(f"\nExtracted {len(ml_files)} .ml files to {output_dir}", file=sys.stderr)
    
    if errors:
        print(f"\n{len(errors)} errors occurred:", file=sys.stderr)
        for module_name, phase, _ in errors[:10]:
            print(f"  - {module_name} ({phase})", file=sys.stderr)
    
    return 0 if len(ml_files) > 0 else 1

if __name__ == '__main__':
    sys.exit(main())
