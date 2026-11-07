# fstar-depgraph

A standalone tool that builds a **zoomable, source-cross-linked dependence viewer**
for an F\* project, plus a report of **unused definitions**.

It reads `.checked` files directly (no re-verification), so it works on any project
that has already been built.

## What it produces

A self-contained directory (optionally packaged as a `.tar.gz`) containing:

```
index.html            the viewer
assets/               viewer.css, layout.js, viewer.js
data/                 graph + source data, as plain <script>-loadable .js
unused-report.txt     text report of unused definitions
README.md             usage notes for the recipient
serve.py              optional local web server
```

The package has **no external dependencies and needs no web server** — data is
delivered through `<script>` tags rather than `fetch()`, so `index.html` opens
directly from `file://`. Ship the tarball to anyone and they can browse it offline.

### Views

| View | Shows |
| --- | --- |
| Overview | Top-level namespaces and the dependences between them |
| Namespace | Modules / sub-namespaces inside a namespace |
| Module | Every top-level definition in the module, plus boundary nodes for neighbouring modules |
| Definition | The ego network of one definition (callers and callees), depth 1–4, across module boundaries |

Double-click a node to zoom in, use the breadcrumbs (or `Esc`) to zoom out.
Selecting any definition opens the corresponding source file in the side pane,
scrolled to and highlighting the exact lines of that definition (both the `val`
in the `.fsti` and the `let` in the `.fst`, when both exist).

Keyboard: `/` search, `f` fit, `u` unused report, `?` help, `Esc` up a level.

## Building

The tool links against the **in-tree** `fstar.compiler` findlib library, so
`OCAMLPATH` must point at this repo's `out/lib` — otherwise dune may pick up an
older opam-installed `fstar.compiler` whose checked-file cache version does not
match your `.checked` files.

```sh
cd tools/depgraph
OCAMLPATH=$PWD/../../out/lib dune build
```

The executable lands at `tools/depgraph/_build/default/src/fstar_depgraph.exe`.

## Running

```sh
fstar_depgraph.exe --root <Module> [--root <Module> ...]
                   --include <dir-with-.checked-files> ...
                   --source  <dir-with-.fst/.fsti-files> ...
                   --out     <output-dir>
                   [--package [FILE.tar.gz]]
                   [--include-generated] [--quiet]
```

* `--root` — one or more root modules; reachability is computed from these.
* `--include` — directories searched for `.checked` files (repeatable).
* `--source` — directories searched for `.fst`/`.fsti` sources to bundle (repeatable, searched recursively).
* `--package` — also emit a `.tar.gz` of the output directory.
* `--include-generated` — include auto-generated projectors/discriminators/`haseq`
  lemmas in the unused report (they are hidden by default).

### Example: the F\* compiler itself

```sh
cd <fstar-repo>
./tools/depgraph/_build/default/src/fstar_depgraph.exe \
  --root FStarC.Main \
  --include stage2/fstarc.checked --include stage2/ulib.checked \
  --source src --source ulib \
  --out /tmp/fstarc-depgraph \
  --package /tmp/fstarc-depgraph.tar.gz
```

Takes ~3s and yields 263 modules / 17346 definitions / 3891 module edges,
442 bundled source files, a 14 MB directory and a 2.7 MB tarball.

## The unused-definitions report

Every definition is classified as one of:

* **live** — reachable from a root.
* **unreachable** — not reachable from any root by any chain of references.
  These are the genuine dead-code candidates.
* **implicitly live** — reachable, but with no *direct* incoming reference; kept
  alive only because it is an SMT-pattern lemma, a typeclass instance, a plugin,
  a splice, an effect/action, or an axiom. The report annotates which.

Type → data-constructor is treated as *containment*, not a reference, so a
constructor is only live if something actually mentions it (including in
patterns). Auto-generated projectors, discriminators and `__uu___haseq` lemmas
are excluded from the report unless `--include-generated` is passed.

Declared module dependences that turn out to have **zero** definition-level uses
are reported per module in the viewer as removable `open`/dependency candidates.

## Implementation notes

* `src/analyze.ml` — loads a `.checked` file via
  `FStarC.CheckedFiles.unsafe_raw_load_checked_file` and walks every `sigelt`
  with `FStarC.Syntax.Visit.visit_sigelt` to collect defined lids, source ranges
  and referenced lids.
  Note that `visit_sigelt` does **not** surface `Pat_cons` head fvs, so pattern
  constructors are harvested separately — without that, every constructor that
  is only ever matched on looks unused.
* `src/model.ml` — BFS module loading from the roots, `val`/`let` merging,
  liveness hints, reachability, in-degrees and the unused report.
* `src/emit.ml` — writes the viewer package.
* `assets/` — the viewer; `gen/gen_assets.ml` compiles these into
  `src/assets.ml` so the executable is a single self-contained binary.
* `assets/layout.js` — a small Sugiyama layered layout (cycle breaking,
  longest-path layering, virtual nodes, median ordering sweeps, bezier edges).
