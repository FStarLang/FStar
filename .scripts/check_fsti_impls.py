#!/usr/bin/env python3
"""Check that every interface in the verified libraries has an implementation.

An .fsti without an implementation is just a list of axioms, which may be
inconsistent.  So every X.fsti under one of the library roots must come with
an X.fst (when it is meant to be extracted) or an X-model.fst (when it is not,
e.g. when it is implemented natively; see doc/ref/targets.md).  The
implementation may live in another directory, as long as it is under one of
the roots, since those are verified.  Implementations elsewhere (e.g. in the
compiler sources) do not count: they are not verified.

Interfaces that cannot (yet) be implemented without axioms are listed in
.scripts/fsti_without_impl.txt.  New interfaces cannot be added there
silently: CI runs this script (make check-fsti-impls).

Model implementations must not contain axioms or admits themselves.
"""

import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOTS = ["ulib", "pulse/lib"]
ALLOWLIST = os.path.join(REPO, ".scripts", "fsti_without_impl.txt")


def files_under(ext):
    for root in ROOTS:
        for dirpath, _, filenames in os.walk(os.path.join(REPO, root)):
            for f in filenames:
                if f.endswith(ext):
                    yield os.path.relpath(os.path.join(dirpath, f), REPO), f[: -len(ext)]


# Constructs that would make a model vacuous: keywords and attributes (outside
# of strings), and options (inside strings, e.g. #push-options "--lax").
AXIOMS = re.compile(r"\b(assume|admit|magic|undefined)\b|\[@@@?[^\]]*\b(admitted)\b")
AXIOM_OPTIONS = re.compile(r"--(lax|admit_smt_queries)\b")
STRING = re.compile(r'"(?:\\.|[^"\\])*"')


def find_axiom(text):
    code = strip_comments(text)
    m = AXIOMS.search(STRING.sub('""', code))
    if m:
        return m.group(1) or m.group(2)
    m = AXIOM_OPTIONS.search(code)
    return m and m.group(0)


def strip_comments(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i) and not text.startswith("(*)", i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith("*)", i):
            depth, i = depth - 1, i + 2
        elif not depth and text.startswith("//", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        elif not depth and text[i] == '"':
            j = i + 1
            while j < len(text) and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i : j + 1])
            i = j + 1
        else:
            if not depth:
                out.append(text[i])
            i += 1
    return "".join(out)


def split_tag(stem):
    module, _, tag = stem.partition("-")
    return module, tag


def main():
    impls = {split_tag(stem) for _, stem in files_under(".fst")}

    allowed = set()
    with open(ALLOWLIST) as f:
        for line in f:
            line = line.split("#", 1)[0].strip()
            if line:
                allowed.add(line)

    missing, stale, axioms = [], [], []
    for path, stem in sorted(files_under(".fst")):
        if split_tag(stem)[1] == "model":
            with open(os.path.join(REPO, path)) as f:
                word = find_axiom(f.read())
            if word:
                axioms.append((path, word))
    seen = set()
    for path, stem in sorted(files_under(".fsti")):
        seen.add(path)
        module, tag = split_tag(stem)
        ok = (module, tag) in impls or (module, "-".join(filter(None, [tag, "model"]))) in impls
        if not ok and path not in allowed:
            missing.append(path)
        elif ok and path in allowed:
            stale.append(path)
    stale += sorted(allowed - seen)

    for path in missing:
        print(f"{path}: interface without implementation; add an .fst, or a -model.fst "
              "if it should not be extracted (see doc/ref/targets.md)", file=sys.stderr)
    for path in stale:
        print(f"{path}: remove it from {os.path.relpath(ALLOWLIST, REPO)} "
              "(it now has an implementation, or no longer exists)", file=sys.stderr)
    for path, word in axioms:
        print(f"{path}: model implementations must not use `{word}`", file=sys.stderr)
    return 1 if missing or stale or axioms else 0


if __name__ == "__main__":
    sys.exit(main())
