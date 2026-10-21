"""Exercise direct-C CIfDef with absent, empty, and zero-valued macros."""

import argparse
import itertools
from pathlib import Path
import shlex
import subprocess


def run(command):
    subprocess.run(command, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fstar", required=True)
    parser.add_argument("--cc", required=True)
    parser.add_argument("--cxx", required=True)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)

    fstar = shlex.split(args.fstar) + [
        "--codegen", "C", "--custard_monomorphize_types", "true",
        "--custard_warn_any", "--warn_error", "@367",
        "--odir", str(args.output),
    ]
    standalone = args.output / "standalone.c"
    library = args.output / "CIfDef.c"
    application = args.output / "application.c"
    globals_library = args.output / "CIfDefGlobal.c"
    run(fstar + [
        "--custard_main", "CIfDef.main", "CIfDef.fst", "-o", str(standalone),
    ])
    run(fstar + [
        "--custard_unit", "CIfDef", "--custard_entry", "CIfDef.main",
        "--custard_entry", "CIfDef.evaluate", "CIfDef.fst", "-o", str(library),
    ])
    run(fstar + [
        "--custard_link", str(args.output / "CIfDef.cui"),
        "--custard_main", "CIfDefApp.main", "CIfDefApp.fst",
        "-o", str(application),
    ])
    run(fstar + [
        "--custard_unit", "CIfDefGlobal", "--custard_entry", "CIfDefGlobal.result",
        "CIfDefGlobal.fst", "-o", str(globals_library),
    ])

    text = standalone.read_text() + standalone.with_suffix(".h").read_text()
    if text.count("cifdef_tick(") != 6:
        raise AssertionError("Mixed guards duplicated their continuation")
    for name in ("CUSTARD_IFDEF_A", "CIfDef_second"):
        if f"defined({name})" not in text:
            raise AssertionError(f"Missing preprocessor test of {name}")
        if f"extern bool {name}" in text:
            raise AssertionError(f"CIfDef {name} was declared as an object")

    configurations = (None, "", "0", "1")
    for a, b in itertools.product(configurations, repeat=2):
        defines = [
            "-D" + name + "=" + value
            for name, value in zip(("CUSTARD_IFDEF_A", "CIfDef_second"), (a, b))
            if value is not None
        ]
        for compiler, standard in ((args.cc, "c11"), (args.cxx, "c++17")):
            for sources in (
                (standalone,),
                (library, application),
                (globals_library, Path("CIfDefGlobal_main.c")),
            ):
                executable = args.output / "cifdef.exe"
                run(shlex.split(compiler) + [
                    "-std=" + standard, "-Wall", "-Wextra", "-Werror",
                    "-I.", "-I" + str(args.output),
                    "-x", "c" if standard == "c11" else "c++",
                ] + defines + [str(source) for source in sources]
                    + ["-o", str(executable)])
                run([str(executable.resolve())])


if __name__ == "__main__":
    main()
