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
so that it is safe to run from `make all` in a source checkout.  Fails, rather
than reporting on the previous build, if that tree is older than src/custard/
(section 52.1).
"""

import glob
import os
import re
import subprocess
import sys
import tempfile

PKGS = ("batteries,zarith,stdint,yojson,ppxlib,menhirLib,pprint,process,"
        "sedlex,mtime.clock")

# Section 51.1.  OCaml prints the unmatched example two ways, and the check
# has to read both.  Long or annotated sets go on their own line:
#
#     ... is not matched:
#     (Prologue _|Epilogue _)
#
# but a short one is printed inline, after a space:
#
#     Here is an example of a case that is not matched: Prologue _
#
# The first version split on "not matched:\n", so the inline form did not
# match at all and `missing` silently became the *whole warning block* --
# which then contained whatever the source excerpt contained.
NOT_MATCHED = re.compile(r"not matched:[ \n]+(.*)", re.S)

# A one-constructor match on option or either: `Some?.v`, `Inl?.v` and their
# siblings.  Partial in OCaml, guarded in the F* source.
#
# Section 51.1.  Applied to the *unmatched constructors* and not to the source
# excerpt.  Against the excerpt it discarded any function whose body happened
# to eliminate an option anywhere -- which is how `flag_to_doc`, the function
# this whole check was written after, passed: its `Extern` case matches on a
# `FStar_Pervasives_Native.Some`, forty lines from the branch that was
# missing.  The module qualifier is optional because the inline form prints a
# bare `None` or `Inl {...}`.
ELIM = re.compile(r"(FStar_Pervasives(_Native)?\.)?(Some|None|Inl|Inr)\b")


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

    # Section 52.1.  The sweep reads the *extracted* compiler, so it answers
    # about the last build and not about src/custard/.  A module that does not
    # compile is guarded below, but that is only one of the two ways a stale
    # tree lies: a tree that is merely *old* compiles perfectly and reports on
    # the previous sources.  Both directions are wrong and both are silent --
    # making a match inexhaustive and running the gate passes, and fixing it
    # again keeps failing.
    #
    # The general shape, which is what makes this worth a comment: a gate about
    # the compiler that reads a *derived* artifact inherits that artifact's
    # staleness.  `check-sources' next to it greps CUSTARD_SRC and is always
    # current.  Unlike a test of generated output -- where the artifact is the
    # thing under test, so its being stale is the bug -- here the artifact is a
    # proxy, and nothing about it says which source it came from.
    #
    # This belongs in the script and not in the makefile: `check-partial:
    # $(FSTAR_EXE)' is an existence check, since tests/custard has no rule that
    # builds the compiler, so it would rebuild nothing.
    stale = []
    unmapped = []
    for ml in mls:
        base = os.path.basename(ml)[:-3].replace("_", ".")
        srcs = [os.path.join(root, "src", "custard", base + ext)
                for ext in (".fst", ".fsti")]
        srcs = [s for s in srcs if os.path.exists(s)]
        if not srcs:
            unmapped.append(os.path.basename(ml))
            continue
        mt = os.path.getmtime(ml)
        stale += [os.path.relpath(s, root) for s in srcs
                  if os.path.getmtime(s) > mt]
    # A module the sweep reads but cannot map to a source is unguarded, and
    # silently so, which is the failure this whole check is about.
    if unmapped:
        print("checkpartial: no source found for:")
        for m in sorted(unmapped):
            print(f"    {m}")
        print("Those modules cannot be checked for staleness.")
        return len(unmapped)
    if stale:
        print("checkpartial: the extracted compiler is older than its source:")
        for s in sorted(set(stale)):
            print(f"    {s}")
        print("The sweep would report on the previous build.  Rebuild first "
              "(make -j), then re-run.")
        return 1

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
    unparsed = []
    for block in "".join(out).split('File "')[1:]:
        if "Warning 8" not in block:
            continue
        # This one *is* about the source excerpt: a projector is recognized
        # by the shape of the match, not by what it fails to cover.
        if "match projectee with" in block:
            continue
        m = NOT_MATCHED.search(block)
        # No unmatched example means the warning was not parsed, which is a
        # bug in this script rather than a clean module; say so rather than
        # dropping it.
        if not m:
            unparsed.append(block.split("\n")[0].rstrip(":"))
            continue
        missing = " ".join(m.group(1).split())
        if ELIM.match(missing):
            continue
        where = block.split("\n")[0].rstrip(":")
        bad.append((where, missing))

    for where in unparsed:
        print(f"checkpartial: could not parse the warning at {where}; "
              "the unmatched-example format has changed.")
    for where, missing in bad:
        print(f"partial match at {where}\n    missing: {missing}")
    if bad:
        print(f"\n{len(bad)} inexhaustive match(es) over an IR datatype.")
        print("Add the missing cases, or a case that fails with a message "
              "naming the broken invariant.")
    return len(bad) + len(unparsed)


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
