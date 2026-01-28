import os
import glob

def to_module_name(path):
    rel = os.path.relpath(path, "ulib")
    base = os.path.splitext(rel)[0]
    filename = os.path.basename(path)
    module_name = os.path.splitext(filename)[0]
    return module_name

def to_ml_name(module_name):
    return module_name.replace(".", "_") + ".ml"

src_dir = "ulib"
fst_files = []
for root, dirs, files in os.walk(src_dir):
    if ".cache" in root: continue
    for f in files:
        if f.endswith(".fst") or f.endswith(".fsti"):
            fst_files.append(os.path.join(root, f))

# For ulib, we primarily want to verify it.
# Extraction is complex due to partial extraction flags.
# We will generate a 'verify' alias.

# Get all FST files relative to ulib/
fst_args = []
for f in fst_files:
    rel = os.path.relpath(f, src_dir)
    fst_args.append(rel)

fst_args_str = " ".join(fst_args)

dune_content = f"""(include_subdirs unqualified)

(rule
 (alias verify_ulib)
 (enabled_if (= %{{profile}} stage1))
 (deps (source_tree .))
 (action
  (run fstar-stage1 --warn_error -272 
       {fst_args_str}))
)

(rule
 (alias verify_ulib)
 (enabled_if (= %{{profile}} stage2))
 (deps (source_tree .))
 (action
  (run %{{bin:fstar}} --warn_error -272 
       {fst_args_str}))
)

; We don't define a library yet because we are not compiling extracted code.
"""

print(dune_content)
with open(os.path.join(src_dir, "dune"), "w") as f:
    f.write(dune_content)
