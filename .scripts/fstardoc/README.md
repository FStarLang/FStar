# fstardoc

A tool for nicely extract documentation for F* files

## How to Run

```
python3 fstardoc.py {path to fst/fsti file}
```

---

# Consumers of `--export_docs`

`fstardoc.py` above reads F* source directly. The three scripts below
instead read the versioned JSON that `fstar.exe --export_docs` emits from
a checked file, and never open a checked file themselves — the boundary
the whitepaper's D4 argues for. All of them expect schema version 4.

| Script | Output | Needs |
|---|---|---|
| `docs_json_to_html.py` | one HTML page from one module's JSON | nothing |
| `fstardoc_md.py` | a Markdown tree for mkdocs or mdBook | nothing |
| `fstardoc_site.py` | a standalone site with structural search | `markdown-it-py` |

`fstardoc_md.py` and `fstardoc_site.py` make deliberately different
arguments. The site generator shows what the export makes *possible*:
signatures whose names link, and search over the names a contract
mentions and over the shape of a type. The Markdown backend shows what
it makes *cheap*: theme, navigation and full-text search come from a site
generator nobody has to write or review, so content is the only thing
left to discuss.

## `fstardoc_md.py`: Markdown for mkdocs or mdBook

Run from the F* root, with a compiler built at `stage3/out/bin/fstar.exe`.
`--cache` is where the checked files are; `--include` lets the exporter
find the sources, which is what allows a declaration to be quoted as
written.

```sh
OUT=/tmp/ulib-md

python3 .scripts/fstardoc/fstardoc_md.py \
  --fstar stage3/out/bin/fstar.exe \
  --out "$OUT" \
  --title "F* Library Reference" \
  --cache stage2/ulib.checked \
  --include ulib \
  --strict-subset \
  --module FStar.List.Tot.Base \
  --module FStar.List.Tot.Properties \
  --module FStar.Seq.Base \
  --module FStar.Seq.Properties \
  --module FStar.Classical
```

For more than a handful of modules, list them in a file instead — one per
line, `#` comments allowed — and pass `--modules-from ulib-slice.txt`.

That writes `$OUT/docs/*.md`, plus `mkdocs.yml` and `book.toml` beside
them and `SUMMARY.md` inside. Then build with either tool, or both:

```sh
cd "$OUT"
mkdocs build     # -> $OUT/site
mdbook build     # -> $OUT/book
```

`mkdocs serve` and `mdbook serve` give a live preview instead. The
generated `mkdocs.yml` names a theme that ships with mkdocs, so nothing
needs installing; pass `--mkdocs-theme readthedocs` (or `material`, if it
is installed) to change that.

### Checking the output

Three checks run on every generation, and print to stderr:

- **links** — every generated link resolves to a page and an anchor that
  exist.
- **subset** — no generated line uses a construct outside the Markdown
  subset the script's docstring lists. `--strict-subset` makes a
  violation an error. Note that *authored* documentation passes through
  untouched, so a violation usually means a doc comment used something
  the subset does not cover — which is the diagnostic D6 describes,
  sketched.
- **anchors** — `--verify-html` compares the anchors the script predicted
  against the `<h2 id=...>` each backend actually emitted. This needs the
  HTML to exist, so it is a second pass after building:

```sh
cd /path/to/FStar
python3 .scripts/fstardoc/fstardoc_md.py ... --verify-html
```

That third check is the one that matters. The first two compare the
output to the script's own rules; only this one can catch a rule that is
wrong. It found five bad anchors the first time it ran, where two F*
names differing only in an apostrophe — `rev'_append` and `rev_append` —
slugged alike, and mkdocs and mdBook disambiguated them differently.

## `docs_json_to_html.py`: one page, no dependencies

```sh
fstar.exe --export_docs Mod.fst.checked > Mod.json
python3 .scripts/fstardoc/docs_json_to_html.py Mod.json > Mod.html
```

`tests/docs` exercises this one end to end.

## Running regression tests

```
make
```

## Getting latest version of the tool

```
make update-to-latest
```

## Makefile

The snippet below used to be in ulib/Makefile

        DOC_FILES=Prims.fst FStar.Pervasives.Native.fst FStar.Pervasives.fst \
              FStar.Squash.fsti FStar.Classical.fsti FStar.BigOps.fsti \
              FStar.BitVector.fst FStar.BV.fsti \
              FStar.Char.fsti FStar.Date.fsti FStar.DependentMap.fsti \
              FStar.Dyn.fsti FStar.Exn.fst FStar.Fin.fst FStar.Float.fsti \
              FStar.FunctionalExtensionality.fsti FStar.Float.fsti \
              FStar.Ghost.fsti FStar.IFC.fsti FStar.IndefiniteDescription.fst \
              FStar.UInt8.fst FStar.UInt16.fst FStar.UInt32.fst FStar.UInt64.fst

        DOC_DIR=./doc

        fstardoc: $(DOC_DIR) $(addprefix $(DOC_DIR)/, $(addsuffix .md, $(DOC_FILES)))

        $(DOC_DIR):
            mkdir -p $@

        $(DOC_DIR)/%.md: %
            ../bin/fstar --print_in_place $^
            python3 ../.scripts/fstardoc/fstardoc.py $^ > $@
