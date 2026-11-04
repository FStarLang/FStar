"""Exercise header-only output and consumers in separate translation units."""

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
common = ["-Wall", "-Wextra", "-Werror", "-I.", "-I" + str(out)]


def run(command):
    print(shlex.join(command), flush=True)
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    print(result.stdout, end="", flush=True)
    result.check_returncode()
    return result.stdout


def extract(source, roots, *options, static=True, output=None):
    command = fstar + [
        "--codegen", "C", "--custard_monomorphize_types", "true",
        "--odir", str(out),
    ]
    if static:
        command += ["--custard_static_header"]
    for root in roots:
        command += ["--custard_entry", root]
    if output:
        command += ["-o", str(out / output)]
    return run(command + list(options) + [source + ".fst"])


roots = ["StaticHeader." + n for n in
         ("limit", "plain", "api", "equal", "countdown", "get_nan", "collision")]
dump = extract("StaticHeader", roots, "--custard_unit", "StaticLib", "--custard_dump_cui")
assert "static-header: true" in dump
assert "let StaticHeader.helper" in dump
assert "let StaticHeader.internal_limit" in dump
assert "let StaticHeader.unreachable" not in dump
assert "external StaticHeader.foreign" not in dump
names = dict(re.findall(r"^  C name: (.+) = (\w+)$", dump, re.MULTILINE))
assert names["StaticHeader.helper'"] != names["StaticHeader.helper_"]
extract("StaticHeaderOther", ["StaticHeaderOther.equal"],
        "--custard_unit", "StaticOther")
extract("StaticHeaderCompare", ["StaticHeaderCompare.equal"],
        "--custard_unit", "StaticCmp", "--custard_link", str(out / "StaticLib.cui"))
header = (out / "StaticLib.h").read_text()
assert "static inline uint32_t StaticHeader_api(" in header
assert "static uint32_t StaticHeader_plain(" in header
assert "static inline uint32_t StaticHeader_plain(" not in header
assert "extern uint32_t StaticHeader_foreign(uint32_t);" in header
assert "extern uint32_t StaticHeader_foreign_value;" in header
assert '#include "StaticHeader_stubs.h"' in header
assert "static uint32_t StaticHeader_helper(" in header
assert "StaticHeader_unreachable" not in header
assert "custard_StaticLib__StaticHeader_pair__eq" in header
assert "custard_StaticCmp__StaticHeader_pair__eq" in (out / "StaticCmp.h").read_text()
for name in ("StaticLib", "StaticOther", "StaticCmp"):
    assert not (out / (name + ".c")).exists()

# Both default names, without -o, and an explicitly named header.
extract("StaticHeaderOther", ["StaticHeaderOther.equal"], output="Explicit.h")
extract("StaticHeaderOther", ["StaticHeaderOther.equal"])
assert (out / "Explicit.h").exists() and (out / "Custard.h").exists()
assert not (out / "Explicit.c").exists() and not (out / "Custard.c").exists()
extract("StaticHeaderOther", ["StaticHeaderOther.equal"],
        "--custard_c_no_prefix", "StaticHeaderOther", output="NoPrefix.h")
assert "static inline bool equal(" in (out / "NoPrefix.h").read_text()
no_prefix = out / "no-prefix.c"
no_prefix.write_text(
    '#include "NoPrefix.h"\n'
    "int main(void) { item p = {1, 2}; return !equal(p, p); }\n")
run(cc + ["-std=c11"] + common +
    [str(no_prefix), "-o", str(out / "no-prefix")])
run([str(out / "no-prefix")])
extract("StaticHeaderOther", ["StaticHeaderOther.equal"], output="123.h")
digits = out / "digits.c"
digits.write_text(
    '#include "123.h"\n'
    "int main(void) { StaticHeaderOther_item p = {1, 2}; "
    "return !StaticHeaderOther_equal(p, p); }\n")
run(cc + ["-std=c11"] + common +
    [str(digits), "-o", str(out / "digits")])
run([str(out / "digits")])

run(cc + ["-std=c11"] + common +
    ["-c", "StaticHeader_user.c", "-o", str(out / "user.o")])
run(cc + ["-std=c11"] + common +
    ["-c", "StaticHeader_stubs.c", "-o", str(out / "stubs.o")])
run(cxx + ["-std=c++17"] + common +
    ["StaticHeader_user.cpp", str(out / "user.o"), str(out / "stubs.o"),
     "-o", str(out / "consumer")])
run([str(out / "consumer")])
symbols = subprocess.check_output(
    ["nm", "-g", "--defined-only", str(out / "user.o")], text=True)
assert "StaticHeader_" not in symbols

# Normal source output may import a header-only unit; no library .c is linked.
extract("StaticHeaderApp", [], "--custard_main", "StaticHeaderApp.main",
        "--custard_link", str(out / "StaticLib.cui"),
        static=False, output="App.c")
app = (out / "App.c").read_text() + (out / "App.h").read_text()
for name in ("StaticHeader_helper", names["StaticHeader.helper'"],
             names["StaticHeader.helper_"]):
    assert name + "(" in app
    assert not re.search(r"\bstatic\s+(?:inline\s+)?uint32_t\s+" +
                         re.escape(name) + r"\(", app)
assert "#define STATICHEADER_INTERNAL_LIMIT" not in app
for compiler, standard in ((cc, "c11"), (cxx, "c++17")):
    run(compiler + ["-std=" + standard] + common +
        ["-x", "c" if standard == "c11" else "c++", str(out / "App.c"),
         "-x", "none", str(out / "stubs.o"), "-o", str(out / "app")])
    run([str(out / "app")])

# A second header reuses private helpers rather than materializing them.
# The consumer imports both its new helper and the original header's helper.
reuse_dump = extract("StaticHeaderReuse", ["StaticHeaderReuse.api"],
                    "--custard_unit", "StaticReuse", "--custard_dump_cui",
                    "--custard_c_no_prefix", "StaticHeaderReuse",
                    "--custard_link", str(out / "StaticLib.cui"))
assert "let StaticHeader.helper\n" not in reuse_dump
assert "let StaticHeaderReuse.helper" in reuse_dump
assert "C name: StaticHeaderReuse.helper = static_reuse_helper" in reuse_dump
assert "static uint32_t StaticHeader_helper(" not in (out / "StaticReuse.h").read_text()

# This helper has a different F* name but the same default C name as an
# unrequested helper in StaticLib. It must be renamed and its CUI must record
# that spelling so a third unit can call it correctly.
collision_dump = extract("StaticHeader_hidden", ["StaticHeader_hidden.api"],
                         "--custard_unit", "StaticCollision", "--custard_dump_cui",
                         "--custard_link", str(out / "StaticLib.cui"))
assert ("C name: StaticHeader_hidden.collision = StaticHeader_hidden_collision_1"
        in collision_dump)
extract("StaticHeaderReuseApp", [], "--custard_main", "StaticHeaderReuseApp.main",
        "--custard_link", str(out / "StaticLib.cui"),
        "--custard_link", str(out / "StaticReuse.cui"),
        "--custard_link", str(out / "StaticCollision.cui"),
        static=False, output="ReuseApp.c")
reuse_app = (out / "ReuseApp.c").read_text() + (out / "ReuseApp.h").read_text()
assert "static_reuse_helper(" in reuse_app
assert not re.search(r"\bstatic\s+(?:inline\s+)?uint32_t\s+static_reuse_helper\(",
                     reuse_app)
for compiler, standard in ((cc, "c11"), (cxx, "c++17")):
    run(compiler + ["-std=" + standard] + common +
        ["-x", "c" if standard == "c11" else "c++", str(out / "ReuseApp.c"),
         "-x", "none", str(out / "stubs.o"), "-o", str(out / "reuse-app")])
    run([str(out / "reuse-app")])

# A non-inline API deliberately remains non-inline. Unused-function warnings
# are the consumer's to configure, not a reason to silently change CInline.
unused = out / "unused.c"
unused.write_text('#include "StaticLib.h"\nint main(void) { return 0; }\n')
run(cc + ["-std=c11", "-Wno-unused-function"] + common +
    [str(unused), "StaticHeader_stubs.c", "-o", str(out / "unused")])


def reject(name, root, message, *options, codegen="C", filename=None,
           source="StaticHeaderReject", code=155):
    target = out / (filename or (name + ".h"))
    target.unlink(missing_ok=True)
    command = fstar + [
        "--codegen", codegen, "--custard_static_header",
        "--custard_monomorphize_types", "true",
        "--custard_entry", root, "--odir", str(out),
        "-o", str(target),
    ] + list(options) + [source + ".fst"]
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    (out / (name + ".log")).write_text(result.stdout)
    diagnostic = re.sub(r"\s+", " ", result.stdout)
    assert result.returncode != 0 and f"Error {code}" in diagnostic, result.stdout
    assert message in diagnostic, result.stdout
    assert not target.exists(), "failed extraction wrote " + str(target)


reject("global", "StaticHeaderReject.constant", "non-macro global")
reject("init", "StaticHeaderReject.computed", "non-macro global")
reject("main", "StaticHeaderReject.apply", "--custard_main",
       "--custard_main", "StaticHeaderReject.main")
reject("split", "StaticHeaderReject.apply", "--custard_split", "--custard_split")
reject("suffix", "StaticHeaderReject.apply", ".h output file", filename="bad.c")
reject("ocaml", "StaticHeaderReject.apply", "requires --codegen C", codegen="OCaml")
reject("cherry", "StaticHeaderReject.apply", "requires --codegen C", codegen="Cherry")
reject("karamel", "StaticHeaderReject.apply", "requires --codegen C", codegen="KrmlC")

# A header-only unit cannot silently inherit an initialization obligation.
extract("StaticHeaderReject", ["StaticHeaderReject.computed"],
        "--custard_unit", "StaticState", static=False, output="StaticState.c")
reject("linked-init", "StaticHeaderReject.apply", "unit with runtime initialization",
       "--custard_link", str(out / "StaticState.cui"))

# A root's specified C name cannot be changed to avoid a header's definition.
reject("root-collision", "StaticHeader_hidden.collision", "both named",
       "--custard_link", str(out / "StaticLib.cui"),
       source="StaticHeader_hidden", code=374)

# Independent producers can choose colliding private names. Fail at CUI load
# instead of handing a consumer two headers that redefine a C function.
extract("StaticHeader_hidden", ["StaticHeader_hidden.api"],
        "--custard_unit", "StaticIndependent")
reject("header-collision", "StaticHeaderReject.apply", "both define the C name",
       "--custard_link", str(out / "StaticLib.cui"),
       "--custard_link", str(out / "StaticIndependent.cui"), code=369)
print("static-header extraction, C/C++ consumers and rejection tests passed")
