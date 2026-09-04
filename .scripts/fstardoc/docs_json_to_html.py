#!/usr/bin/env python3
"""Render an F* module documentation index as a static HTML page.

    fstar.exe --export_docs Mod.fst.checked > Mod.docs.json
    python3 docs_json_to_html.py Mod.docs.json > Mod.docs.html

This tool is EXPERIMENTAL, and deliberately tiny. Its only input is the
versioned JSON produced by `fstar.exe --export_docs`: it never reads a
checked file, never runs F*, and knows nothing about F* internals. If it
has to change because the compiler changed, the schema version below
should have changed too.

Everything the JSON carries -- names, kinds, signatures, ranges and
documentation text -- originates in a source file, and is therefore
untrusted as far as this renderer is concerned. All of it is HTML
escaped; in particular the documentation payload is a list of opaque
strings -- one per line, joined here and nowhere else -- emitted as
text, never as markup. There is intentionally no markdown, no linking
and no search.
"""

import html
import json
import sys

SCHEMA = "fstar-module-docs"
VERSION = 2

STYLE = """\
body { font-family: sans-serif; margin: 2em auto; max-width: 50em; }
h1 { font-size: 1.4em; }
.decl { border-top: 1px solid #ddd; padding: 0.6em 0; }
.name { font-family: monospace; font-weight: bold; }
.kind { color: #666; font-size: 0.85em; margin-left: 0.5em; }
.sig { font-family: monospace; white-space: pre-wrap; color: #333; }
.where { color: #888; font-size: 0.8em; }
.doc { margin-top: 0.4em; white-space: pre-wrap; }
.empty { color: #888; font-style: italic; }
"""


def esc(s):
    return html.escape(str(s), quote=True)


def render_range(rng):
    if not rng:
        return ""
    return '<div class="where">%s(%s,%s-%s,%s)</div>' % (
        esc(rng["file"]),
        esc(rng["start_line"]), esc(rng["start_col"]),
        esc(rng["end_line"]), esc(rng["end_col"]),
    )


def render_decl(decl):
    return "".join([
        '<div class="decl">',
        '<div><span class="name">%s</span>' % esc(decl["name"]),
        '<span class="kind">%s</span></div>' % esc(decl["kind"]),
        '<div class="sig">%s</div>' % esc(decl["signature"]),
        render_range(decl.get("range")),
        '<div class="doc">%s</div>' % esc("\n".join(decl["doc"])),
        "</div>",
    ])


def render(index):
    schema = index.get("schema")
    version = index.get("version")
    if schema != SCHEMA or version != VERSION:
        sys.stderr.write(
            "docs_json_to_html.py: expected schema %s version %d, got %r version %r\n"
            % (SCHEMA, VERSION, schema, version))
        return None

    module = index["module"]
    decls = index["declarations"]
    body = [
        "<!DOCTYPE html>",
        '<html><head><meta charset="utf-8">',
        "<title>%s</title>" % esc(module),
        "<style>%s</style>" % STYLE,
        "</head><body>",
        "<h1>%s</h1>" % esc(module),
        '<p class="where">%s, schema %s version %d</p>' % (
            "interface" if index.get("interface") else "implementation",
            esc(schema), version),
    ]
    if decls:
        body.extend(render_decl(d) for d in decls)
    else:
        body.append('<p class="empty">No documented declarations.</p>')
    body.append("</body></html>")
    return "\n".join(body) + "\n"


def main(argv):
    if len(argv) != 2:
        sys.stderr.write("usage: docs_json_to_html.py Mod.docs.json\n")
        return 2
    with open(argv[1], encoding="utf-8") as f:
        index = json.load(f)
    out = render(index)
    if out is None:
        return 1
    sys.stdout.write(out)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
