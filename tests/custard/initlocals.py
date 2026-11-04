"""Check --custard_init_locals, alone and after --custard_hoist_locals."""

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
MODES = ("c99", "c89", "c23")


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


def extract(name, mode, hoist, *flags, error=None):
    path = out / "{}-{}-{}.c".format(name, mode, "hoist" if hoist else "normal")
    command = fstar + [
        "--codegen", "C", "--custard_monomorphize_types", "true",
        "--custard_main", name + ".main", "--odir", str(out),
        "-o", str(path), "--custard_init_locals", mode,
    ]
    if hoist:
        command += ["--custard_hoist_locals"]
    run(command + list(flags) + [name + ".fst"], error=error)
    return path


DECLARATION = re.compile(r"^\s*[A-Za-z_]\w*(?:\s+\w+)*[\s*]+\w+\s*(?:\[[^\]]*\])?\s*;\s*$")
STATEMENT = re.compile(r"^\s*(?:return|goto|break|continue|case|default)\b")


def initialized(path):
    # Every object declared inside a function body must carry an initializer.
    # Aggregate type definitions (struct/union/enum bodies) are skipped.
    source = path.read_text()
    source = re.sub(r"/\*.*?\*/|//[^\n]*", "", source, flags=re.S)
    source = re.sub(r'"(?:\\.|[^"\\])*"', '""', source)
    source = re.sub(r"^\s*#.*$", "", source, flags=re.M)
    stack = []
    for line in source.splitlines():
        in_code = stack and all(kind == "code" for kind in stack)
        if in_code and DECLARATION.match(line) and not STATEMENT.match(line):
            raise AssertionError((path, "uninitialized local", line))
        for _ in range(line.count("{")):
            aggregate = re.search(r"\b(?:struct|union|enum)\b", line) and "=" not in line
            stack.append("type" if aggregate or not stack and "(" not in line else "code")
        for _ in range(line.count("}")):
            stack.pop()
    assert not stack, path


def compile_run(path, mode, definitions=(), cpp=True):
    standard_c = "c2x" if mode == "c23" else "c11"
    for compiler, standard, language in (
            (cc, standard_c, "c"), (cxx, "c++17", "c++")):
        if language == "c++" and not cpp:
            continue
        exe = path.with_suffix("." + language.replace("+", "x") + ".exe")
        flags = ["-std=" + standard, "-Wall", "-Wextra", "-Werror",
                 "-I.", "-I..", "-I" + str(out)]
        if language == "c++":
            # Nullary constructors of tagged unions print as
            # `(T){ .tag = K }`; that is unrelated to this option.
            flags += ["-Wno-missing-field-initializers"]
        run(compiler + flags + list(definitions) +
            ["-x", language, str(path), "-o", str(exe)])
        run([str(exe)])


if Path("InitLocals.fst").exists():
    for mode in MODES:
        for hoist in (False, True):
            source = extract("InitLocals", mode, hoist)
            initialized(source)
            compile_run(source, mode)
            source = extract("HoistLocals", mode, hoist,
                             "--custard_unit", "HoistUnit")
            initialized(source)
            for definitions in ((), ("-DHOIST_LEFT",)):
                compile_run(source, mode, definitions)

    for backend in ("OCaml", "FSharp", "KrmlC", "Cherry"):
        run(fstar + [
            "--codegen", backend, "--custard_init_locals", "c99",
            "--custard_main", "InitLocals.main", "InitLocals.fst",
        ], error="--custard_init_locals requires --codegen C")
else:
    for mode in MODES:
        for name in ("HoistArrays", "PulseBasic", "PulseClosure",
                     "AllocOverflow"):
            for hoist in (False, True):
                source = extract(name, mode, hoist)
                initialized(source)
                compile_run(source, mode)
    # Only C23 can zero a variable-length array with an initializer.
    for name in ("ArrInit", "HoistVla"):
        for hoist in (False, True):
            source = extract(name, "c23", hoist)
            initialized(source)
            compile_run(source, "c23", cpp=False)
    for mode in ("c99", "c89"):
        extract("ArrInit", mode, False, error="variable-length stack array")
        extract("HoistVla", mode, True, error="variable-length stack array")
        extract("HoistVlaLate", mode, False, error="variable-length stack array")
