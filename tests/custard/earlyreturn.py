"""Check --custard_early_return: flattened tail branches, and goto exit."""

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


def extract(name, tag, *flags, error=None):
    path = out / (name + "-" + tag + ".c")
    command = fstar + [
        "--codegen", "C", "--custard_monomorphize_types", "true",
        "--custard_main", name + ".main", "--odir", str(out),
        "-o", str(path),
    ]
    run(command + list(flags) + [name + ".fst"], error=error)
    return path


def compile_run(path, cpp=True, strict=False):
    for compiler, standard, language in (
            (cc, "c11", "c"), (cxx, "c++17", "c++")):
        if language == "c++" and not cpp:
            continue
        exe = path.with_suffix("." + language.replace("+", "x") + ".exe")
        flags = ["-std=" + standard, "-Wall", "-Wextra", "-Werror",
                 "-I.", "-I..", "-I" + str(out)]
        if language == "c" and strict:
            flags += ["-Werror=declaration-after-statement"]
        run(compiler + flags + ["-x", language, str(path), "-o", str(exe)])
        run([str(exe)])


def functions(path):
    """Map each function name to its body text."""
    source = path.read_text()
    source = re.sub(r"/\*.*?\*/|//[^\n]*", "", source, flags=re.S)
    result = {}
    for m in re.finditer(r"^\w[^\n;]*?\b(\w+)\(([^\n;]*)\)\s*\{\n(.*?)^\}",
                         source, flags=re.M | re.S):
        result[m.group(1)] = m.group(3)
    return result


def check_flat(path, names):
    bodies = functions(path)
    for name in names:
        body = bodies[name]
        assert not re.search(r"\belse\b", body), (path, name, body)


def check_goto(path, names, void=()):
    bodies = functions(path)
    for name in names:
        body = bodies[name]
        assert re.search(r"\bgoto exit\w*;", body), (path, name, body)
        assert re.search(r"^\s*exit\w*:", body, flags=re.M), (path, name, body)
        returns = re.findall(r"\breturn\b[^;]*;", body)
        assert len(returns) == 1, (path, name, body)
        if name in void:
            assert returns == ["return;"], (path, name, body)
            assert "result" not in body, (path, name, body)
        else:
            assert re.search(r"\bresult\w* = ", body), (path, name, body)
            assert re.search(r"return result\w*;", body), (path, name, body)


if Path("EarlyReturn.fst").exists():
    flat = ["EarlyReturn_choose", "EarlyReturn_classify", "EarlyReturn_nested",
            "EarlyReturn_effect_only", "EarlyReturn_make_point",
            "EarlyReturn_named"]
    void = ["EarlyReturn_effect_only"]
    default = extract("EarlyReturn", "default")
    same = extract("EarlyReturn", "no", "--custard_early_return", "no")
    assert (default.read_text().replace("-default.h", "-no.h")
            == same.read_text())
    compile_run(default)
    bodies = functions(default)
    plain = bodies["EarlyReturn_plain"]
    for tag, flags in (
            ("return", ["--custard_early_return", "return"]),
            ("goto", ["--custard_early_return", "goto"]),
            ("goto-hoist", ["--custard_early_return", "goto",
                            "--custard_hoist_locals"]),
            ("goto-init", ["--custard_early_return", "goto",
                           "--custard_hoist_locals",
                           "--custard_init_locals", "c99"])):
        source = extract("EarlyReturn", tag, *flags)
        check_flat(source, flat)
        bodies = functions(source)
        # Functions without an early return are unchanged.
        assert bodies["EarlyReturn_plain"] == plain, source
        for name in ("EarlyReturn_maybe_note", "EarlyReturn_skip_note"):
            assert "goto" not in bodies[name], (source, name)
        if tag.startswith("goto"):
            check_goto(source, flat, void)
        else:
            assert "goto" not in source.read_text(), source
        compile_run(source, strict="hoist" in tag)

    # A declaration after the early exit: goto mode must not jump past an
    # initialization, unless locals are hoisted first.
    compile_run(extract("EarlyReturnLate", "return",
                        "--custard_early_return", "return"))
    extract("EarlyReturnLate", "goto", "--custard_early_return", "goto",
            error="it has an initializer")
    source = extract("EarlyReturnLate", "goto-hoist",
                     "--custard_early_return", "goto", "--custard_hoist_locals")
    check_goto(source, ["EarlyReturnLate_later"])
    compile_run(source, strict=True)

    for backend in ("OCaml", "FSharp", "KrmlC", "Cherry"):
        run(fstar + [
            "--codegen", backend, "--custard_early_return", "return",
            "--custard_main", "EarlyReturn.main", "EarlyReturn.fst",
        ], error="--custard_early_return requires --codegen C")
else:
    # A variable-length array after the early exit: goto mode cannot jump
    # into its scope, even with hoisting; return mode is fine.
    source = extract("EarlyReturnVla", "return",
                     "--custard_early_return", "return")
    check_flat(source, ["EarlyReturnVla_run"])
    compile_run(source, cpp=False)
    for tag, flags in (("goto", []), ("goto-hoist", ["--custard_hoist_locals"])):
        extract("EarlyReturnVla", tag, "--custard_early_return", "goto",
                *flags, error="variable-length stack array")
