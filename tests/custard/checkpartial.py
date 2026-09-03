#!/usr/bin/env python3
"""Report inexhaustive matches in Custard's own OCaml.

Section 49.1.  Nothing in the build catches one.  The compiler sources are
checked with --lax (mk/fstar-01.mk, mk/fstar-12.mk), so F* does not prove
pattern exhaustiveness for src/custard/; the extracted OCaml is then compiled
by dune with `-w -A`, so OCaml does not report it either.  A match missing a
constructor therefore reaches a user as

    Unexpected error: File "...ml", line N: Pattern matching failed

naming a line in generated OCaml rather than the construct.  The first one
found this way was flag_to_doc, missing Prologue; there were nine.

This runs the OCaml type checker over the extracted Custard modules with
warning 8 on and nothing else, and reports what is left.  Two kinds of
partial match are expected and filtered:

  * F*'s generated projectors (`match projectee with | C _0 -> _0`), which
    are partial by construction and never called on the wrong constructor;
  * `Some?.v` and `Inl?.v` style eliminations, which are one-constructor
    matches on option/either guarded at their use site.

Everything else is a function over an IR datatype, and a missing case there
is a latent crash.  Exit status is the number of such sites.

Needs a dune build tree for the cmi files; skips (exit 0) if there is none,
so that it is safe to run from `make all` in a source checkout.
"""

import glob
import os
import re
import subprocess
import sys
import tempfile

PKGS = ("batteries,zarith,stdint,yojson,ppxlib,menhirLib,pprint,process,"
        "sedlex,mtime.clock")

# A one-constructor match on option or either: `Some?.v`, `Inl?.v` and their
# siblings.  Partial in OCaml, guarded in the F* source.
ELIM = re.compile(r"FStar_Pervasives(_Native)?\.(Some|None|Inl|Inr)\b")


def find_tree(root):
    for stage in ("stage3", "stage2", "stagec", "stage1"):
        objs = os.path.join(root, stage, "dune", "_build", "default",
                            "fstar-guts", ".fstarcompiler.objs", "byte")
        if not os.path.isdir(objs):
            continue
        for rel in ("fstarc.ml",
                    os.path.join("out", "lib", "fstar", "compiler",
                                 "fstarc.ml")):
            mls = sorted(glob.glob(os.path.join(root, stage, rel,
                                                "FStarC_Custard_*.ml")))
            if mls:
                return objs, mls
    return None, None


def main():
    root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
    objs, mls = find_tree(root)
    if objs is None:
        print("checkpartial: no dune build tree; skipping")
        return 0

    out = []
    failed = []
    with tempfile.TemporaryDirectory() as td:
        for ml in mls:
            r = subprocess.run(
                ["ocamlfind", "ocamlc", "-package", PKGS, "-I", objs,
                 "-w", "+8", "-warn-error", "-a", "-stop-after", "typing",
                 "-c", ml],
                cwd=td, capture_output=True, text=True)
            # A module that does not compile reports no warnings, so without
            # this the check would pass for the wrong reason -- which is the
            # failure mode it exists to prevent.  Usually a stale build tree.
            if r.returncode != 0:
                failed.append((os.path.basename(ml), r.stdout + r.stderr))
            out.append(r.stdout + r.stderr)

    if failed:
        for name, msg in failed:
            print(f"checkpartial: {name} did not compile:\n{msg}")
        print(f"{len(failed)} module(s) did not compile; the warning-8 sweep "
              "did not run over them.  Is the dune build tree up to date?")
        return len(failed)

    bad = []
    for block in "".join(out).split('File "')[1:]:
        if "Warning 8" not in block:
            continue
        if "match projectee with" in block:
            continue
        if ELIM.search(block.split("Here is an example")[0]):
            continue
        where = block.split("\n")[0].rstrip(":")
        missing = block.split("not matched:\n")[-1].strip().replace("\n", " ")
        bad.append((where, missing))

    for where, missing in bad:
        print(f"partial match at {where}\n    missing: {missing}")
    if bad:
        print(f"\n{len(bad)} inexhaustive match(es) over an IR datatype.")
        print("Add the missing cases, or a case that fails with a message "
              "naming the broken invariant.")
    return len(bad)


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
