import os
import glob

def to_module_name(path):
    # src/basic/FStarC.Const.fst -> FStarC.Const
    # Remove src/ prefix
    rel = os.path.relpath(path, "src")
    # Remove extension
    base = os.path.splitext(rel)[0]
    filename = os.path.basename(path)
    module_name = os.path.splitext(filename)[0]
    return module_name

def to_ml_name(module_name):
    # FStarC.Const -> FStarC_Const.ml
    return module_name.replace(".", "_") + ".ml"

src_dir = "src"
fst_files = []
for root, dirs, files in os.walk(src_dir):
    if "tests" in root: continue
    for f in files:
        if f.endswith(".fst") or f.endswith(".fsti"):
            fst_files.append(os.path.join(root, f))

fst_impls = [f for f in fst_files if f.endswith(".fst")]
targets = [to_ml_name(to_module_name(f)) for f in fst_impls]

# Manual ML files
ml_files = []
for root, dirs, files in os.walk(src_dir):
    if "tests" in root: continue
    for f in files:
        if f.endswith(".ml"):
            ml_files.append(os.path.join(root, f))

# Read include paths
with open(os.path.join(src_dir, "fstar.include")) as f:
    includes = [line.strip() for line in f if line.strip()]

include_flags = " ".join([f"--include {i}" for i in includes])

# Get all FST files relative to src_dir for command line
fst_args = []
for f in fst_files:
    # relpath from src/ to file
    rel = os.path.relpath(f, src_dir)
    fst_args.append(rel)

fst_args_str = " ".join(fst_args)

# Generate dune file content
dune_content = f"""(include_subdirs unqualified)

; Stage 1 Extraction Rule
(rule
 (enabled_if (= %{{profile}} stage1))
 (targets { " ".join(targets) })
 (deps (source_tree .))
 (action
  (run fstar.exe --codegen OCaml --output_dir . {include_flags} 
       --warn_error -272 --admit_smt_queries true
       {fst_args_str}))
)

; Stage 2 Extraction Rule
(rule
 (enabled_if (= %{{profile}} stage2))
 (targets { " ".join(targets) })
 (deps (source_tree .))
 (action
  (run fstar.exe --codegen OCaml --output_dir . {include_flags} 
       --warn_error -272 --admit_smt_queries true
       {fst_args_str}))
)

(library
 (name fstarcompiler)
 (public_name fstar.compiler)
 (enabled_if (or (= %{{profile}} stage1) (= %{{profile}} stage2)))
 (modules :standard \ FStarC_Main)
 (libraries 
    batteries zarith stdint yojson memtrace menhirLib mtime pprint sedlex ppxlib process fstar_ulib
 )
 (preprocess (pps ppx_deriving.show ppx_deriving_yojson sedlex.ppx))
 (flags -w -8-20-26-27-28-33-35)
)

(executable
 (name FStarC_Main)
 (public_name fstar)
 (package fstar)
 (enabled_if (or (= %{{profile}} stage1) (= %{{profile}} stage2)))
 (modules FStarC_Main)
 (libraries fstarcompiler)
)
"""

print(dune_content)
with open(os.path.join(src_dir, "dune"), "w") as f:
    f.write(dune_content)
