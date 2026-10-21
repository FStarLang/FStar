#!/usr/bin/env python3
"""Non-owning CUI bindings: inheritance, conflicts, and implementation priority."""

import argparse
import itertools
from pathlib import Path
import shlex
import shutil
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fstar", required=True)
    parser.add_argument("--out", required=True)
    parser.add_argument("--cc", default="cc")
    parser.add_argument("--cxx", default="c++")
    args = parser.parse_args()
    fixtures = Path(__file__).resolve().parent / "foreign-bindings"
    out = Path(args.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(fixtures / "foreign_bindings.h", out / "foreign_bindings.h")

    def profile(name, *, mapped=False, target="fb_hook",
                header="foreign_bindings.h", signature=False, macro=False,
                implementation=False):
        directory = out / "sources" / name
        directory.mkdir(parents=True, exist_ok=True)
        for path in fixtures.glob("*.fst*"):
            if path.name != "Foreign.fst" or implementation:
                shutil.copyfile(path, directory / path.name)
        for interface in ["Foreign.fsti", "FStar.Stubs.ForeignBinding.fsti"]:
            source = (fixtures / interface).read_text()
            if mapped:
                for symbol, c_name, extra in [
                    ("hook", target, ""),
                    ("value", "FB_VALUE", "CMacro; "),
                    ("identity", "fb_identity", "CMacro; "),
                ]:
                    attrs = (f'[@@{extra}custard_extern "{c_name}"; '
                             f'custard_c_header "{header}"]\n')
                    source = source.replace(f"val {symbol}", attrs + f"val {symbol}")
            elif macro:
                source = source.replace("val hook", "[@@CMacro]\nval hook")
            if signature:
                source = source.replace("hook (_proof:unit) (x:U32.t) : U32.t",
                                        "hook (_proof:unit) (x:FStar.UInt64.t) : FStar.UInt64.t")
            (directory / interface).write_text(source)
        producer = (fixtures / "ForeignProducer.fst").read_text()
        for module in ["ForeignTwin", "ForeignChild"]:
            (directory / f"{module}.fst").write_text(producer.replace("ForeignProducer", module))
        return directory

    def extract(directory, name, source, *, unit=False, links=(), extra=(),
                entries=None, reject=None):
        cache = directory / "cache"
        cache.mkdir(exist_ok=True)
        base = shlex.split(args.fstar) + [
            "--cache_dir", str(cache), "--odir", str(out),
            "--cache_checked_modules",
        ]
        if "Stub" in source:
            base += ["--already_cached", "Prims"]
        extension = ".fst" if (directory / (source + ".fst")).exists() else ".fsti"
        sources = ["Foreign.fsti"]
        if (directory / "Foreign.fst").exists():
            sources.append("Foreign.fst")
        if source == "ForeignConsumer":
            sources.append("ForeignProducer.fst")
        elif source == "ForeignChildConsumer":
            sources.append("ForeignChild.fst")
        elif source == "ForeignNamingConsumer":
            sources.append("ForeignAlias.fst")
        elif source == "ForeignStubConsumer":
            sources.append("FStar.Stubs.ForeignBinding.fsti")
        if source + extension not in sources:
            sources.append(source + extension)
        for dependency in sources:
            checked = subprocess.run(base + [dependency], cwd=directory, text=True,
                                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            assert checked.returncode == 0, checked.stdout
        command = base + [
            "--codegen", "C", "--custard_monomorphize_types", "true",
            "--custard_dump_cui",
        ]
        if unit:
            command += ["--custard_unit", name]
            roots = entries or (["Foreign.hook", "Foreign.value"] if source == "Foreign" else [source + ".api"])
            for root in roots:
                command += ["--custard_entry", root]
        else:
            command += ["--custard_main", source + ".main"]
        for link in links:
            command += ["--custard_link", str(out / (link + ".cui"))]
        command += list(extra) + [source + extension, "-o", str(out / (name + ".c"))]
        result = subprocess.run(command, cwd=directory, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / (name + ".log")).write_text(result.stdout)
        if reject:
            assert result.returncode != 0, f"{name}: conflicting binding was accepted"
            assert reject.lower() in " ".join(result.stdout.lower().split()), result.stdout
            assert "unexpected error" not in result.stdout.lower(), result.stdout
        else:
            assert result.returncode == 0, result.stdout
        return result.stdout

    def compile_run(name, libraries=()):
        for compiler, standard, language in [
            (args.cc, "c11", "c"),
            (args.cxx, "c++17", "c++"),
        ]:
            exe = out / (name + "-" + standard)
            command = shlex.split(compiler) + [
                "-std=" + standard, "-Wall", "-Wextra", "-Werror",
                "-I" + str(out), "-x", language, str(out / (name + ".c")),
            ] + [str(out / (lib + ".c")) for lib in libraries] + ["-o", str(exe)]
            subprocess.run(command, check=True)
            subprocess.run([str(exe)], check=True)

    mapped = profile("mapped", mapped=True)
    plain = profile("plain")
    matching = profile("matching", mapped=True)
    dump = extract(mapped, "Bindings", "ForeignProducer", unit=True)
    assert "foreign binding" in dump and "target: fb_hook" in dump, dump
    assert dump.count("target: fb_identity") == 2, dump
    extract(mapped, "Twin", "ForeignTwin", unit=True)
    for index, links in enumerate(itertools.permutations(["Bindings", "Twin"])):
        name = "Identical" + str(index)
        extract(plain, name, "ForeignConsumer", links=links)
        compile_run(name, ["Bindings"])
    extract(matching, "Matching", "ForeignConsumer", links=["Bindings"])
    compile_run("Matching", ["Bindings"])
    extract(plain, "Child", "ForeignChild", unit=True, links=["Bindings"])
    child_consumer = (plain / "ForeignConsumer.fst").read_text().replace("ForeignProducer", "ForeignChild")
    (plain / "ForeignChildConsumer.fst").write_text(child_consumer.replace("module ForeignConsumer", "module ForeignChildConsumer"))
    extract(plain, "Chained", "ForeignChildConsumer", links=["Child"])
    compile_run("Chained", ["Child"])
    (matching / "ForeignChildConsumer.fst").write_text(
        child_consumer.replace("module ForeignConsumer", "module ForeignChildConsumer"))
    extract(matching, "ChainedMatching", "ForeignChildConsumer", links=["Child"])
    compile_run("ChainedMatching", ["Child"])
    real = profile("real", implementation=True)
    extract(real, "OwnedNoPrefix", "Foreign", unit=True, entries=["Foreign.other"],
            extra=["--custard_c_no_prefix", "Foreign"])
    extract(plain, "ProvisionalNames", "ForeignNamingConsumer", links=["Bindings", "OwnedNoPrefix"],
            extra=["--custard_entry", "ForeignAlias.hook",
                   "--custard_c_no_prefix", "ForeignAlias"])
    compile_run("ProvisionalNames", ["OwnedNoPrefix"])

    for kind, kwargs in [
        ("Target", {"target": "other_hook"}),
        ("Header", {"header": "other.h"}),
        ("Signature", {"signature": True}),
    ]:
        other = profile("conflict-" + kind, mapped=True, **kwargs)
        extract(other, "Other" + kind, "Foreign", unit=True)
        for index, links in enumerate(itertools.permutations(["Bindings", "Other" + kind])):
            extract(plain, "LinkedConflict" + kind + str(index), "ForeignConsumer",
                    links=links, reject="conflicting foreign bindings")
        extract(other, "ExplicitConflict" + kind, "Foreign", unit=True,
                links=["Bindings"], reject="Conflicting foreign binding")
    macro = profile("conflict-flags", macro=True)
    extract(macro, "ExplicitFlags", "ForeignSimpleConsumer",
            links=["Bindings"], reject="different declaration attributes")
    extract(mapped, "StubBindings", "FStar.Stubs.ForeignBinding", unit=True,
            entries=["FStar.Stubs.ForeignBinding.hook"])
    extract(plain, "StubApp", "ForeignStubConsumer", links=["StubBindings"])
    compile_run("StubApp")
    extract(out / "sources" / "conflict-Target", "StubConflict", "ForeignStubConsumer",
            links=["StubBindings"], reject="explicitly selects another target")

    extract(real, "LocalReal", "ForeignRealConsumer", links=["Bindings"])
    compile_run("LocalReal")
    extract(real, "Real", "Foreign", unit=True)
    for index, links in enumerate(itertools.permutations(["Bindings", "Real"])):
        name = "OwnedReal" + str(index)
        extract(plain, name, "ForeignRealConsumer", links=links)
        compile_run(name, ["Real"])

    extract(plain, "NoPrefix", "Foreign", unit=True,
            extra=["--custard_c_no_prefix", "Foreign"])
    extract(plain, "NoPrefixApp", "ForeignSimpleConsumer", links=["NoPrefix"])
    (out / "NoPrefixStub.c").write_text(
        "#include <stdint.h>\nuint32_t value = 5;\n"
        "uint32_t hook(uint32_t x) { return x + 3; }\n")
    compile_run("NoPrefixApp", ["NoPrefixStub"])
    extract(plain, "ExplicitNoPrefix", "ForeignConsumer", links=["Bindings"],
            extra=["--custard_c_no_prefix", "Foreign"],
            reject="explicitly selects another target")

    extract(matching, "NoCUI", "ForeignConsumer")
    compile_run("NoCUI")
    extract(plain, "DefaultBindings", "Foreign", unit=True)
    default_matching = profile("matching-default")
    declarations = default_matching / "Foreign.fsti"
    declarations.write_text(
        declarations.read_text().replace("val hook", '[@@custard_extern "Foreign_hook"]\nval hook')
        .replace("val value", '[@@custard_extern "Foreign_value"]\nval value'))
    (out / "DefaultStub.c").write_text(
        "#include <stdint.h>\nuint32_t Foreign_value = 5;\n"
        "uint32_t Foreign_hook(uint32_t x) { return x + 3; }\n")
    extract(default_matching, "DefaultMatching", "ForeignSimpleConsumer", links=["DefaultBindings"])
    compile_run("DefaultMatching", ["DefaultStub"])
    extract(plain, "DefaultNoCUI", "ForeignSimpleConsumer")
    compile_run("DefaultNoCUI", ["DefaultStub"])
    print("Foreign-binding inheritance, conflicts, specialization, and real implementations passed.")


if __name__ == "__main__":
    main()
