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
| `fstardoc_mcp.py` | the same index, served to an agent over MCP | nothing to serve |

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

## `fstardoc_mcp.py`: the same index, for an agent

A reader gets the structural index behind a search box. An agent gets it
over MCP. The question is the same one — *which lemma guarantees
something about `slice`?* — and it is a question no text search can
express, which is why `grep -rn` over `ulib` is the wrong tool for it.

Build the index once, then serve it:

```sh
python3 .scripts/fstardoc/fstardoc_mcp.py index \
  --fstar stage3/out/bin/fstar.exe \
  --out ulib.index.json \
  --cache stage2/ulib.checked \
  --include ulib \
  --modules-from ulib-slice.txt

python3 .scripts/fstardoc/fstardoc_mcp.py serve --index ulib.index.json
```

`serve` speaks line-delimited JSON-RPC on stdin and stdout, and uses the
standard library only, so it runs wherever an agent runs with nothing to
install. `index` borrows the contract and type-shape analysis from
`fstardoc_site.py`, so it needs `markdown-it-py`; the import is deferred,
and it is a build step run once.

| Tool | Answers |
|---|---|
| `find_by_contract` | which declarations assume or guarantee something about a name |
| `find_by_type` | which have a type of a given shape, e.g. `seq a -> nat -> a` |
| `lookup` | one declaration in full |
| `used_by` | which declarations mention this one — worked uses of a lemma |
| `list_module` | a module's public surface |
| `modules` | what the index holds, with documented counts |

To register it with Claude Code, add it as a stdio server:

```json
{ "mcpServers": {
    "fstardoc": { "command": "python3",
                  "args": [".scripts/fstardoc/fstardoc_mcp.py", "serve",
                           "--index", "ulib.index.json"] } } }
```

Or drive it by hand, which is how it was tested:

```sh
{ echo '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2025-06-18"}}'
  echo '{"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"find_by_contract","arguments":{"name":"slice"}}}'
} | python3 .scripts/fstardoc/fstardoc_mcp.py serve --index ulib.index.json
```

### What it does not do, on purpose

- **Only a module's public surface**, because that is what the export
  reports. This is the right scope, not a shortfall: an agent working
  inside a module already has the file open, and across modules only the
  public surface is referenceable.
- **No guessing.** A short name matching several declarations is reported
  as ambiguous, with the candidates. Silently choosing one would send a
  proof after the wrong lemma.
- **No empty documentation.** An undocumented declaration reports
  `documented: false` and says so, rather than an empty string an agent
  would read as filled and describe in the author's voice. Its type is
  checked, so the signature and contract are what to rely on.
- **Definitions are truncated** unless `include_definition` is passed. A
  proof term can be long enough to fill a context window.

This is not a replacement for FStarLang/fstar-mcp and does not overlap it.
That server is session-oriented — create a session, typecheck a buffer,
`lookup_symbol` at a file, line and column — and answers "what is this
thing I am pointing at". Every tool here answers "what should I be
pointing at", over a library, with no session.

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
