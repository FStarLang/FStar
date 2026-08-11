# Cross-backend extraction tests

This directory holds a *matrix* of extraction tests: each test module is
extracted, compiled and **run** on every backend that supports it, and the
runtime result is compared against what F\* proves statically.

## Backends

| id      | pipeline                                                       |
|---------|----------------------------------------------------------------|
| `ocaml` | `fstar.exe --codegen OCaml` + `ocamlfind ocamlopt`             |
| `c`     | `fstar.exe --codegen krml` + `krml` (C backend) + `cc`         |
| `rust`  | `fstar.exe --codegen krml` + `krml -backend rust` + `rustc`    |

## How a test works

Every test module is **self-contained** (it must not depend on any other module
in this directory) and exposes

```fstar
let main () : FStar.Int32.t = ...
```

`main` returns `0l` when every check in the module passed, and otherwise the
(small, non-zero) tag of the *first* check that failed. Tags are written
literally in the source, so a failure reported as `check #7` can be found by
grepping the module for `chk 7l`.

The usual shape of a module is

```fstar
module ExtFoo
module I32 = FStar.Int32

(* boilerplate: see any other module in this directory *)
let chk (n:I32.t) (b:bool) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let main () : I32.t =
     chk 1l (...)
 &&& chk 2l (...)
```

### Why top-level constants?

F\*'s extraction constant-folds operations on *literals* (e.g. `2 + 2` is
extracted as `4`, and `"a" ^ "b"` as `"ab"`). A test written that way would be
vacuous: it would check F\*'s normalizer against itself rather than checking the
backend. Extraction does **not** unfold top-level `let`-bound names, so tests
bind their operands first:

```fstar
let x : int = -7        (* opaque to extraction, transparent to the SMT solver *)
let y : int = 2
let main () = chk 1l (x / y = -3)
```

F\* still proves `x / y = -3` (the definitions are delta-reducible for the
solver), but the *backend* has to compute it at runtime. Do not write
`chk 1l ((-7) / 2 = -3)`: that folds away and tests nothing.

Do not mark these constants `inline_for_extraction`, and do not build the test
suite with `--cmi`, for the same reason.

### Why *literal* top-level constants?

A top-level constant whose value is *computed* forces Karamel to generate a
`krmlinit_globals` initializer. C tolerates that; the Rust backend treats it as
a fatal warning 9. So bind literals, not expressions.

### Other things to avoid

* `FStar.IntN.v` / `FStar.UIntN.v` in extracted code — there is no C
  implementation, so the generated code cannot link. Use `I32.eq`, `U32.gt`,
  and friends.
* Self-comparisons such as `x <= x` — krml compiles the generated C with
  `-Wall -Werror`, and gcc rejects them under `-Wtautological-compare`. Use two
  distinct constants that happen to be equal.
* Applying a projector directly to a constructor application
  (`Circle?.radius (Circle x)`) — that crashes krml (FINDINGS.md #11). Bind the
  constructor application with `let` first.

## Expected failures

`FINDINGS.md` documents every extraction bug this directory has found, with a
severity, a `file:line` for the cause, and a minimal repro.

The `Makefile` has two kinds of exclusion:

* **`NO_<backend>`** — the cell makes no sense on that backend (closures are
  not Low\*, the Rust backend refuses mathematical integers). Not built.
* **`XFAIL_<backend>`** — the cell is *known to be broken*. It is still built
  and run, and it is **required to fail**. If it starts passing, the build
  stops with `UNEXPECTED PASS` and tells you to remove the entry, so a bug fix
  cannot silently go unrecorded.

Every `XFAIL_` entry carries a comment pointing at the relevant section of
`FINDINGS.md`.

## Adding a test

1. Drop `ExtSomething.fst` in this directory. It is picked up automatically
   (`TESTS := $(basename $(wildcard Ext*.fst))`).
2. Give it a doc comment saying *what invariant* it pins down and, if it is
   expected to fail somewhere, why.
3. If a backend cannot support the feature at all, add the module to
   `NO_<backend>`; if the backend is simply buggy, add it to
   `XFAIL_<backend>` and write the analysis up in `FINDINGS.md`.

Prefer one module per issue. A module that mixes a working feature with a
broken one has to be XFAILed wholesale, which loses the coverage of the part
that works — several modules here were split for exactly that reason.

## Running

```sh
make                     # everything
make ocaml               # only the OCaml column
make c rust              # only the Karamel columns
make ExtIntSigned.ocaml  # a single cell of the matrix
V=1 make ...             # show the commands
KRML_TIMEOUT=300 make    # two known bugs make krml loop; every krml call is
                         # bounded (120s by default)
```

This directory runs unconditionally as part of `make test`, so it degrades
gracefully on a machine that is missing a toolchain: the `c` column is skipped
if `krml` cannot be found (`$(KRML_EXE)`, then next to `fstar.exe`, then
`karamel/out/bin/krml`, then `$PATH`), and the `rust` column is skipped if
either `krml` or `rustc` is missing. Each skip prints a `NOTE:` line.

```sh
REQUIRE_BACKENDS=1 make   # turn those skips into hard errors
```

A failing cell prints the backend, the module, and the tag of the failing
check, e.g.

```
FAIL [c] ExtIntCast: check #23 (grep the module for that tag)
```

## Notes on the pipelines

* The C column links against `krmllib`, which is built once from the karamel
  distribution that ships with the compiler (`krml -locate-krmllib`).
* Karamel needs a `.krml` for every type it sees, and the F\* installation ships
  none for ulib, so `FStar.Pervasives.Native` is extracted on demand for tests
  that mention `option`, `either` or tuples (`ULIB_KRML_MODS` in the
  `Makefile`).
* Karamel emits `pub fn main() -> i32`, which rustc will not accept as a binary
  entry point, so the Rust rule renames it and appends a real `fn main`.
* krml **exits 0** even when an unhandled exception or a translation error
  stops it from emitting a definition, so both Karamel rules check that the
  output actually contains what they asked for. Without that, several of the
  bugs in `FINDINGS.md` would look like passes.
