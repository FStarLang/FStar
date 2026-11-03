#!/usr/bin/env python3

import argparse
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path


PACKAGES = (
    "threads,batteries,dynlink,mtime,mtime.clock,pprint,"
    "ppx_deriving.runtime,ppx_deriving_yojson.runtime,ppxlib,ppxlib.ast,"
    "process,stdint,yojson,zarith,unix"
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--worktree", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    worktree = args.worktree.resolve()
    root = Path(__file__).resolve().parent
    harness = root / "source_file_name_cache_regression.ml"
    build = worktree / "stage2/dune/_build/default/fstar-guts"
    archive = build / "fstarcompiler.cmxa"
    args.output.mkdir(parents=True, exist_ok=True)
    executable = args.output / "source-file-name-cache-regression.exe"
    command = [
        "ocamlfind", "ocamlopt", "-thread", "-linkpkg",
        "-package", PACKAGES,
        "-I", str(build / ".fstarcompiler.objs/byte"),
        "-I", str(build / ".fstarcompiler.objs/native"),
        str(archive), str(harness), "-o", str(executable),
    ]
    subprocess.run(command, check=True)
    with tempfile.TemporaryDirectory(
        prefix="source-file-name-cache-", dir=args.output
    ) as directory:
        fixture = Path(directory)
        source = fixture / "a/b/c.fst"
        source.parent.mkdir(parents=True)
        source.write_text("module A.B.C\n")
        process = subprocess.run(
            [str(executable), str(fixture)],
            text=True,
            capture_output=True,
            check=True,
        )
    if process.stdout != "source_file_name cache regression: ok\n":
        raise RuntimeError("unexpected regression output")
    result = {
        "compile_command": command,
        "run_output": process.stdout,
        "worktree_head": subprocess.check_output(
            ["git", "-C", str(worktree), "rev-parse", "HEAD"], text=True
        ).strip(),
        "compiler_archive_sha256": sha256(archive),
        "harness_sha256": sha256(harness),
        "runner_sha256": sha256(Path(__file__)),
    }
    (args.output / "result.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )


if __name__ == "__main__":
    main()
