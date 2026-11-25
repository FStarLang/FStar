"""Check --custard_line_comments, alone and with --custard_hoist_locals."""

import os
from pathlib import Path
import re
import shlex
import subprocess
import sys


out = Path(sys.argv[1]).resolve()
assert sys.argv[2] == "--"
fstar = sys.argv[3:]
out.mkdir(parents=True, exist_ok=True)
cc = shlex.split(os.environ.get("CC", "cc"))
cxx = shlex.split(os.environ.get("CXX", "c++"))


def run(command, error=None):
    print(shlex.join(command), flush=True)
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    print(result.stdout, end="", flush=True)
    if error is None:
        result.check_returncode()
    else:
        assert result.returncode != 0, "expected extraction to fail"
        assert error in result.stdout, result.stdout


def extract(name, *flags):
    path = out / "{}{}.c".format(name, "".join(f.replace("--custard", "") for f in flags))
    run(fstar + [
        "--codegen", "C", "--custard_monomorphize_types", "true",
        "--custard_main", name + ".main", "--odir", str(out), "-o", str(path),
    ] + list(flags) + [name + ".fst"])
    return path.read_text(), path


def block(indent, *lines):
    return "".join(indent + l + "\n" for l in ("//",) + tuple("// " + l for l in lines) + ("//",))


def standalone_block_comments(source):
    # Comment-only lines inside function bodies; top-level ones are exempt.
    depth, found = 0, []
    for line in source.splitlines():
        if depth and re.match(r"^\s*/\*.*\*/\s*$", line):
            found.append(line.strip())
        depth += line.count("{") - line.count("}")
    return found


def compile_run(path):
    for compiler, standard, language in ((cc, "c11", "c"), (cxx, "c++17", "c++")):
        exe = path.with_suffix("." + language.replace("+", "x") + ".exe")
        # -Wall enables -Wcomment, which reports a backslash-newline in a
        # line comment.
        run(compiler + ["-std=" + standard, "-Wall", "-Wextra", "-Werror",
                        "-I.", "-I..", "-I" + str(out),
                        "-x", language, str(path), "-o", str(exe)])
        run([str(exe)])


for hoist in ([], ["--custard_hoist_locals"]):
    # Statement comments become framed line-comment blocks; a pair on an
    # unread value shares one block; inline comments stay block comments.
    source, path = extract("PulseComment", "--custard_line_comments", *hoist)
    for expected in [
            block("  ", "the running total"),
            block("    ", "one step"),
            block("  ", "doubling"),
            block("  ", "discarded load", "load done"),
            block("  ", "kept", "even unread")]:
        assert expected in source, (expected, path)
    assert "/* outer before */ /* inner before */" in source, path
    assert "/* accumulate */" in source, path
    assert standalone_block_comments(source) == [], path
    compile_run(path)

    # Lines are trimmed, an empty comment vanishes, and a comment whose line
    # ends in a backslash keeps the block form.
    source, path = extract("PulseLineComment", "--custard_line_comments", *hoist)
    assert block("  ", "first line", "second line, indented") in source, path
    assert block("  ", "after the addition") in source, path
    assert standalone_block_comments(source) == ["/* ends in a backslash \\ */"], path
    assert "/*  */" not in source and "// \n" not in source, path
    compile_run(path)

# Without the option, nothing changes.
source, path = extract("PulseLineComment")
assert "/*  */" in source and "/* after the addition */" in source, path
assert not re.search(r"^\s*//", source, flags=re.M), path

for backend in ("OCaml", "FSharp", "KrmlC", "Cherry"):
    run(fstar + [
        "--codegen", backend, "--custard_line_comments",
        "--custard_main", "PulseLineComment.main", "PulseLineComment.fst",
    ], error="--custard_line_comments requires --codegen C")
