#!/usr/bin/env python3
#
# Migration aid: make the scoping declarations that an implementation file
# currently inherits from its interface explicit.
#
# Historically, F* *interleaved* the parsed declarations of A.fsti into A.fst
# before typechecking, which meant that `open`, `include` and `module X = Y`
# declarations written in A.fsti silently scoped over A.fst as well.  That
# behaviour is going away: an implementation must now declare its own opens.
#
# For every A.fsti/A.fst pair given on the command line (or found under the
# directories given on the command line), this script copies the scoping
# declarations of A.fsti that are missing from A.fst into A.fst, right after
# its `module A` header.
#
# Adding a redundant `open` is a no-op under the *old* semantics, so the output
# of this script can be landed and bootstrapped before the semantic change.
#
# Usage:
#   .scripts/add_iface_opens.py [--dry-run] PATH...
#
# Please do NOT trust this script blindly; review the diff.

import os
import re
import sys

# `open M`, `include M`, `module X = M`.  Anchored at the start of a line:
# scoping declarations are always written at column 0 in practice.
SCOPING_RE = re.compile(r"^(open|include)\s+([A-Za-z_][\w'.]*)\s*(\{[^}]*\})?\s*$|"
                        r"^module\s+([A-Za-z_][\w']*)\s*=\s*([A-Za-z_][\w'.]*)\s*$")

MODULE_HEADER_RE = re.compile(r"^module\s+([A-Za-z_][\w'.]*)\s*$")

FRIEND_RE = re.compile(r"^friend\s+([A-Za-z_][\w'.]*)\s*$")


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def scoping_decls(text):
    """Return the list of (lineno, line, key) scoping declarations of a file.

    The key identifies the declaration for de-duplication purposes: opens and
    includes are keyed by the opened module, abbreviations by the bound name.
    """
    out = []
    for i, line in enumerate(text.splitlines()):
        m = SCOPING_RE.match(line)
        if not m:
            continue
        if m.group(1) is not None:
            # A restricted open only brings the listed names into scope, so it
            # is not subsumed by (nor does it subsume) another open of the
            # same module: key it by its restriction as well.
            restr = re.sub(r"\s+", " ", m.group(3) or "")
            out.append((i, line.rstrip(), (m.group(1), m.group(2), restr)))
        else:
            out.append((i, line.rstrip(), ("module", m.group(4))))
    return out


def header_end(lines):
    """Index of the insertion point: just after the `module A` header, and
    after any `friend` declarations that follow it.

    `friend` must be the *first* dependence on a module, so nothing may be
    inserted before a friend declaration."""
    start = None
    for i, line in enumerate(lines):
        if MODULE_HEADER_RE.match(line):
            start = i + 1
            break
    if start is None:
        return None
    last_friend = None
    for i in range(start, len(lines)):
        if FRIEND_RE.match(lines[i]):
            last_friend = i
    return start if last_friend is None else last_friend + 1


def is_used(name, text):
    """Does `text` mention the module abbreviation `name` qualifying something?"""
    return re.search(r"(?<![\w'.])" + re.escape(name) + r"\s*\.", text) is not None


# Top-level names introduced by a file: vals, lets, type abbreviations and
# inductives, data constructors, record fields and exceptions.  This is a
# purely syntactic over-approximation, which is all we need here.
DEF_RES = [
    re.compile(r"^(?:val|let|and|type|effect|exception|instance)\s+(?:rec\s+)?"
               r"\(?\s*([A-Za-z_][\w']*)"),
    re.compile(r"^\s*\|\s*([A-Z][\w']*)"),          # data constructors
    re.compile(r"^\s*([A-Za-z_][\w']*)\s*:(?!:)"),  # record fields / ctor sigs
]


def top_level_names(text):
    names = set()
    for line in text.splitlines():
        for rex in DEF_RES:
            m = rex.match(line)
            if m:
                names.add(m.group(1))
    return names


def mentions(name, text):
    """Does `text` use `name` unqualified?"""
    return re.search(r"(?<![\w'.])" + re.escape(name) + r"(?![\w'])",
                     text) is not None


def would_shadow(module, itext, iline_no, mtext, module_files):
    """Would copying `open module` to the top of the implementation shadow a
    name that the interface itself defines *after* that open?

    The names an interface declares always shadow `open`ed ones inside its
    implementation, so this is only reported for review, not acted upon."""
    later = top_level_names("\n".join(itext.splitlines()[iline_no + 1:]))
    if not later:
        return None
    exports = set()
    for path in module_files.get(module, []):
        exports |= top_level_names(read(path))
    clash = {n for n in later & exports if mentions(n, mtext)}
    return sorted(clash) or None


def migrate(fsti, fst, module_files, dry_run):
    itext = read(fsti)
    mtext = read(fst)

    have = {key for _, _, key in scoping_decls(mtext)}
    missing = []
    skipped = []
    for lineno, line, key in scoping_decls(itext):
        if key in have:
            continue
        # A module abbreviation is only worth copying if the implementation
        # actually uses it as a qualifier; copying unused ones is pure noise.
        if key[0] == "module":
            if not is_used(key[1], mtext):
                continue
        else:
            clash = would_shadow(key[1], itext, lineno, mtext, module_files)
            if clash:
                skipped.append((line, clash))
        missing.append(line)
    for line, clash in skipped:
        print(f"{fst}: skipping '{line.strip()}' "
              f"(would shadow {', '.join(clash)})")
    if not missing:
        return False

    lines = mtext.splitlines(keepends=True)
    idx = header_end(lines)
    if idx is None:
        print(f"warning: no module header found in {fst}, skipping",
              file=sys.stderr)
        return False

    block = [line + "\n" for line in missing]
    # Keep a blank line between the header and the inserted block if the file
    # had one, so the result stays idiomatic.
    if idx < len(lines) and lines[idx].strip() == "":
        idx += 1
    new = lines[:idx] + block + lines[idx:]

    print(f"{fst}: +{len(missing)} scoping decl(s): "
          + ", ".join(line.strip() for line in missing))
    if not dry_run:
        with open(fst, "w", encoding="utf-8") as f:
            f.writelines(new)
    return True


def pairs(paths):
    # The implementation of a module need not sit next to its interface (e.g.
    # in pulse, `lib/common/M.fsti` is implemented by `lib/core/M.fst`), so
    # index every implementation by basename first.
    impls = {}
    for path in paths:
        base = path if os.path.isdir(path) else os.path.dirname(path)
        for dirpath, _, filenames in os.walk(base):
            for filename in filenames:
                if filename.endswith(".fst"):
                    impls.setdefault(filename, []).append(
                        os.path.join(dirpath, filename))
    for path in paths:
        if os.path.isfile(path) and path.endswith(".fsti"):
            files = [path]
        else:
            files = []
            for dirpath, _, filenames in os.walk(path):
                for filename in filenames:
                    if filename.endswith(".fsti"):
                        files.append(os.path.join(dirpath, filename))
        for fsti in sorted(files):
            local = fsti[:-1]
            if os.path.exists(local):
                yield fsti, local
                continue
            for fst in sorted(impls.get(os.path.basename(local), [])):
                yield fsti, fst


def collect_module_files(roots):
    """Map a module name to the source files defining it."""
    out = {}
    for root in roots:
        base = root if os.path.isdir(root) else os.path.dirname(root)
        for dirpath, _, filenames in os.walk(base):
            for filename in filenames:
                if not filename.endswith((".fst", ".fsti")):
                    continue
                path = os.path.join(dirpath, filename)
                name = filename.rsplit(".fst", 1)[0]
                out.setdefault(name, []).append(path)
    return out


def main(argv):
    dry_run = "--dry-run" in argv
    paths = [a for a in argv if not a.startswith("--")]
    if not paths:
        print(__doc__)
        return 1
    # The shadowing analysis needs to see every module, not just the ones we
    # are migrating, so always scan the standard library too.
    module_files = collect_module_files(set(paths) | {"ulib", "src"})
    n = 0
    for fsti, fst in pairs(paths):
        if migrate(fsti, fst, module_files, dry_run):
            n += 1
    print(f"{'would update' if dry_run else 'updated'} {n} file(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
