"""Check declaration placement without confusing it with C89 compatibility."""

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


def extract(name, hoist, *flags, error=None):
    path = out / (name + ("-hoist" if hoist else "-normal") + ".c")
    command = fstar + [
        "--codegen", "C", "--custard_monomorphize_types", "true",
        "--custard_main", name + ".main", "--odir", str(out),
        "-o", str(path),
    ]
    if hoist:
        command += ["--custard_hoist_locals"]
    run(command + list(flags) + [name + ".fst"], error=error)
    return path


def placement(path):
    # Fixtures deliberately emit only ordinary C object declarations. Count
    # braces after removing comments, strings and preprocessor lines; a
    # declaration at block entry is NOT sufficient -- it must be depth one.
    source = path.read_text()
    source = re.sub(r'#ifdef __cplusplus\s+extern "C" \{\s+#endif', "", source)
    source = re.sub(r"#ifdef __cplusplus\s+\}\s+#endif", "", source)
    source = re.sub(r"/\*.*?\*/|//[^\n]*", "", source, flags=re.S)
    source = re.sub(r'"(?:\\.|[^"\\])*"', '""', source)
    source = re.sub(r"^\s*#.*$", "", source, flags=re.M)
    declaration = re.compile(
        r"^\s*(?:u?int(?:8|16|32|64)_t|size_t|bool|"
        r"HoistArrays_pair|hl_(?:left|right)_t|"
        r"HoistLocals_item|FStar_Pervasives_Native_\w+)"
        r"\s+[*&]?\s*\w+(?:\s*\[|\s*[;=]|\s*\(\*)")
    depth = 0
    saw_declaration = False
    for line in source.splitlines():
        if depth and declaration.match(line):
            assert depth == 1, (path, line)
            saw_declaration = True
        assert not re.search(r"\bfor\s*\(\s*(?:size_t|u?int\w*_t)\s", line), line
        depth += line.count("{") - line.count("}")
    assert saw_declaration, "fixture did not exercise local declarations"


def compile_run(path, definitions=(), cpp=True, strict=True):
    for compiler, standard, language in (
            (cc, "c11", "c"), (cxx, "c++17", "c++")):
        if language == "c++" and not cpp:
            continue
        exe = path.with_suffix("." + language.replace("+", "x") + ".exe")
        flags = ["-std=" + standard, "-Wall", "-Wextra", "-Werror",
                 "-I.", "-I..", "-I" + str(out)]
        if language == "c" and strict:
            flags += ["-Werror=declaration-after-statement"]
        run(compiler + flags + list(definitions) +
            ["-x", language, str(path), "-o", str(exe)])
        run([str(exe)])


if Path("HoistLocals.fst").exists():
    for hoist in (False, True):
        source = extract("HoistLocals", hoist, "--custard_unit", "HoistUnit")
        if hoist:
            placement(source)
        # Foreign headers are not hoisted, so use their C11-compatible
        # fixtures here; each configuration defines only its own local type.
        for definitions in ((), ("-DHOIST_LEFT",)):
            compile_run(source, definitions, strict=hoist)

    header = out / "HoistHeader.h"
    run(fstar + [
        "--codegen", "C", "--custard_hoist_locals", "--custard_static_header",
        "--custard_monomorphize_types", "true", "--odir", str(out),
        "--custard_entry", "CShortCircuit.safe",
        "--custard_entry", "CShortCircuit.safe_and",
        "CShortCircuit.fst", "-o", str(header),
    ])
    placement(header)
    client = out / "header-client.c"
    client.write_text(
        '#include "HoistHeader.h"\n'
        "int main(void) { return !CShortCircuit_safe(0, true) || "
        "CShortCircuit_safe_and(0, true); }\n")
    for definitions in ((), ("-DHOIST_LEFT",)):
        compile_run(client, definitions)

    for backend in ("OCaml", "FSharp", "KrmlC", "Cherry"):
        run(fstar + [
            "--codegen", backend, "--custard_hoist_locals",
            "--custard_main", "HoistLocals.main", "HoistLocals.fst",
        ], error="--custard_hoist_locals requires --codegen C")
    run(fstar + [
        "--codegen", "C", "--custard_hoist_locals",
        "--custard_monomorphize_types", "true",
        "--custard_main", "RefBind.main", "RefBind.fst",
        "-o", str(out / "reference.c"),
    ], error="initialization-only semantics")
else:
    for name in ("HoistArrays", "PulseBasic", "PulseClosure", "AllocOverflow", "ArrInit"):
        normal = extract(name, False)
        compile_run(normal, cpp=name != "ArrInit", strict=False)
        hoisted = extract(name, True)
        placement(hoisted)
        compile_run(hoisted, cpp=name != "ArrInit")
    # A leading VLA is permitted; a VLA after a real statement is not.
    leading = extract("HoistVla", True)
    placement(leading)
    compile_run(leading, cpp=False)
    normal = extract("HoistVlaLate", False)
    compile_run(normal, cpp=False, strict=False)
    extract("HoistVlaLate", True, error="variable-length stack array")
