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
    if name == "GotoReturn":
        flags += ("--custard_entry", "GotoReturn.pulse_early_return",
                  "--custard_entry", "GotoReturn.no_early_return")
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
    # The port of karamel's test/pulse/GotoReturn.fst.
    early = ["early_return_int", "early_return_two_args", "collision_test",
             "early_return_bool", "early_return_uint32",
             "early_return_uint64", "early_return_int64",
             "early_return_void", "early_return_struct"]
    early = ["GotoReturn_" + name for name in early]
    unchanged = ["GotoReturn_" + name for name in
                 ("no_early_return", "unit_return", "pulse_early_return")]
    default = extract("GotoReturn", "default")
    compile_run(default)
    before = functions(default)
    for tag, flags in (
            ("goto", []),
            ("goto-hoist", ["--custard_hoist_locals"]),
            ("goto-lines", ["--custard_line_comments"])):
        source = extract("GotoReturn", tag, "--custard_early_return", "goto",
                         *flags)
        check_flat(source, early)
        check_goto(source, early, ["GotoReturn_early_return_void"])
        bodies = functions(source)
        for name in unchanged:
            assert "goto" not in bodies[name], (source, name)
            assert bodies[name] == before[name], (source, name)
        # The result variable gets a zero of its type, and a fresh name.
        assert re.search(r"^\s*bool result = false;",
                         bodies["GotoReturn_early_return_bool"], re.M), source
        for name in ("uint64", "int64"):
            assert re.search(r"^\s*u?int64_t result = 0\w*;",
                             bodies["GotoReturn_early_return_" + name],
                             re.M), (source, name)
        collision = bodies["GotoReturn_collision_test"]
        assert re.search(r"^\s*int32_t result = \(?gr_opaque_int32\(x\)", collision, re.M), source
        assert re.search(r"^\s*return result_1;", collision, re.M), source
        # A Pulse return is a flag: the function has a single C return.
        pulse = bodies["GotoReturn_pulse_early_return"]
        assert len(re.findall(r"\breturn\b", pulse)) == 1, (source, pulse)
        # Top-level comments stay block comments.
        assert re.search(r"/\*+\s*This function has no early return\.",
                         source.read_text()), source
        compile_run(source, strict="hoist" in tag)

    # A variable-length array after the early exit: goto mode cannot jump
    # into its scope, even with hoisting; return mode is fine.
    source = extract("EarlyReturnVla", "return",
                     "--custard_early_return", "return")
    check_flat(source, ["EarlyReturnVla_run"])
    compile_run(source, cpp=False)
    for tag, flags in (("goto", []), ("goto-hoist", ["--custard_hoist_locals"])):
        extract("EarlyReturnVla", tag, "--custard_early_return", "goto",
                *flags, error="variable-length stack array")
