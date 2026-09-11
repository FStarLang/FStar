#!/usr/bin/env python3
"""Build a static documentation site from `fstar.exe --export_docs`.

This is an EXPERIMENTAL consumer of the versioned JSON export (schema
"fstar-module-docs", version 3). It lives outside the compiler, as the
whitepaper's D4 recommends: it runs `--export_docs` on checked files and
never looks inside them.

    fstardoc_site.py --fstar out/bin/fstar.exe --out site \
        --project DIR:MODULE,MODULE,...  [--project ...] \
        --include DIR ... --library-cache DIR ... [--title T]

For each project module it exports the documentation index, follows the
fully qualified names the export lists in `refs` to the library modules
they belong to, exports those too (one hop, no further), and renders:

  * one page per module, listing every exported declaration with its
    elaborated signature, documentation (Markdown), and definition;
  * links from every qualified name in a signature to its page;
  * a client-side search over names, over the names a declaration's
    pre- and postconditions mention, and over the shapes of their types.

The search is a demonstration that the export carries enough structure
for an external index (whitepaper D7). It is not proposed as a search
engine.

Documentation text is untrusted: Markdown is rendered with raw HTML
disabled.
"""

import argparse
import html
import json
import os
import re
import subprocess
import sys

from markdown_it import MarkdownIt

SCHEMA, VERSION = "fstar-module-docs", 3

MD = MarkdownIt("commonmark", {"html": False, "linkify": False, "typographer": False})

# ---------------------------------------------------------------- export --


def find_checked(module, dirs):
    for d in dirs:
        for ext in (".fsti.checked", ".fst.checked"):
            p = os.path.join(d, module + ext)
            if os.path.exists(p):
                return p
    return None


def export(fstar, checked, cwd, includes):
    cmd = [fstar]
    for i in includes:
        cmd += ["--include", i]
    cmd += ["--export_docs", os.path.abspath(checked)]
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if r.returncode != 0:
        sys.stderr.write("export failed for %s:\n%s\n" % (checked, r.stderr))
        return None
    d = json.loads(r.stdout)
    if d.get("schema") != SCHEMA or d.get("version") != VERSION:
        sys.exit("unexpected schema %r version %r" % (d.get("schema"), d.get("version")))
    return d


# ------------------------------------------------------------ type trees --

STT_HEADS = ("Pulse.Lib.Core.stt",)

# Names that say nothing to a reader looking for what a contract is about.
BORING = re.compile(
    r"^Prims\.(b2t|l_and|l_or|l_imp|l_iff|l_not|l_True|l_False|eq2|squash|"
    r"auto_squash|l_Forall|l_Exists|op_\w+|unit|bool|int|nat|pos|prop|Nil|Cons|"
    r"logical|hasEq|equals|list|string)$"
    r"|^FStar\.Pervasives\.(pattern|smt_pat|smt_pat_or)$"
    r"|^FStar\.Ghost\.(reveal|hide|erased)$"
    r"|^Pulse\.Lib\.Core\.(op_Star_Star|pure|op_exists_Star|emp|slprop)$"
    r"|\.op_\w+$")


def short(fqn):
    parts = fqn.split(".")
    if len(parts) >= 2 and parts[-1] == "t":
        return parts[-2] + ".t"
    return parts[-1]


def peel(t):
    """The type a reader would name: refinements, erasure and ghost
    wrappers removed."""
    while True:
        k = t["k"]
        if k == "refine":
            t = t["t"]
        elif k == "app" and t["f"]["k"] == "fv" and t["f"]["n"] in ("FStar.Ghost.erased",):
            ex = [a["t"] for a in t["args"] if not a["imp"]]
            if not ex:
                return t
            t = ex[0]
        else:
            return t


def head(t):
    t = peel(t)
    if t["k"] == "fv":
        return t["n"]
    if t["k"] == "app":
        return head(t["f"])
    return None


def tokens(t, depth=0):
    """A type as the words a person would type to look for it."""
    t = peel(t)
    k = t["k"]
    if depth > 3:
        return []
    if k == "fv":
        return [short(t["n"])]
    if k == "var":
        return ["*"]
    if k == "type":
        return ["Type"]
    if k == "arrow":
        return ["(->)"]
    if k == "app":
        h = tokens(t["f"], depth + 1)
        for a in t["args"]:
            if not a["imp"]:
                h += tokens(a["t"], depth + 1)
        return h
    return []


def names(t, out):
    k = t["k"]
    if k == "fv":
        if not BORING.search(t["n"]):
            out.add(t["n"])
    elif k == "app":
        names(t["f"], out)
        for a in t["args"]:
            names(a["t"], out)
    elif k == "arrow":
        for b in t["bs"]:
            names(b["t"], out)
        names(t["c"]["res"], out)
        for a in t["c"]["args"]:
            names(a, out)
    elif k == "refine":
        names(t["t"], out)
        names(t["phi"], out)
    elif k == "abs":
        for b in t["bs"]:
            names(b["t"], out)
        names(t["body"], out)
    return out


def analyse(t):
    """Effect, explicit argument shapes, result shape, and the names that
    the pre- and postcondition mention."""
    info = {"eff": None, "args": [], "res": tokens(t), "pre": set(), "post": set()}
    if t["k"] == "refine":
        names(t["phi"], info["post"])
    if t["k"] != "arrow":
        return info
    for b in t["bs"]:
        if b["t"]["k"] == "refine":
            names(b["t"]["phi"], info["pre"])
        if b["q"] == "explicit":
            info["args"].append(tokens(b["t"]))
    c = t["c"]
    res = c["res"]
    eff = c["eff"]
    h = head(res)
    if eff == "FStar.Pervasives.Lemma":
        info["eff"] = "Lemma"
        info["res"] = ["unit"]
        if len(c["args"]) >= 2:
            names(c["args"][0], info["pre"])
            names(c["args"][1], info["post"])
    elif h and h.startswith(STT_HEADS):
        info["eff"] = short(h)
        ex = [a["t"] for a in peel(res)["args"] if not a["imp"]]
        info["res"] = tokens(ex[0]) if ex else []
        if len(ex) >= 3:
            names(ex[1], info["pre"])
            names(ex[2], info["post"])
    else:
        info["eff"] = {"Prims.Tot": "Tot", "Prims.GTot": "GTot"}.get(eff, short(eff))
        info["res"] = tokens(res)
        if res["k"] == "refine":
            names(res["phi"], info["post"])
    return info


# -------------------------------------------------------------- rendering --

KEYWORDS = {
    "val", "let", "rec", "fun", "forall", "exists", "exists*", "requires",
    "ensures", "returns", "fn", "match", "with", "if", "then", "else",
    "decreases", "type", "and", "in", "of", "Lemma", "Tot", "GTot", "Pure",
    "Ghost", "Type", "Type0", "noeq", "unfold", "inline_for_extraction",
    "assume", "open", "module", "private",
}

TOKEN = re.compile(
    r"(?P<q>[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)+)"
    r"|(?P<w>[A-Za-z_][\w']*\*?)"
    r"|(?P<c>//[^\n]*|\(\*.*?\*\))"
    r"|(?P<o>.)",
    re.S)


class Site:
    def __init__(self, title, modules, project):
        self.title = title
        self.modules = modules          # name -> export json
        self.project = project          # ordered [(group, [module names])]
        self.decls = {}                 # fqn -> (module, anchor)
        for m, d in modules.items():
            for x in d["declarations"]:
                self.decls[x["name"]] = (m, anchor(x["name"]))

    def module_of(self, fqn):
        parts = fqn.split(".")
        for i in range(len(parts) - 1, 0, -1):
            m = ".".join(parts[:i])
            if m in self.modules:
                return m
        return None

    def href(self, fqn, here):
        if fqn in self.decls:
            m, a = self.decls[fqn]
            return ("" if m == here else page(m)) + "#" + a
        if fqn in self.modules:
            return page(fqn)
        return None

    def code(self, text, here, aliases=None):
        """Escape F* text, shorten and link fully qualified names, and
        mark keywords. `aliases` maps a name as the author wrote it (e.g.
        `Seq.index` or `sorted`) to the declaration it denotes."""
        out = []
        for m in TOKEN.finditer(text):
            if m.group("q") or m.group("w"):
                tok = m.group(0)
                fqn = tok if m.group("q") else None
                if aliases and tok in aliases:
                    fqn = aliases[tok]
                if tok in KEYWORDS:
                    cls = {"requires": "kw kw-req", "ensures": "kw kw-ens"}.get(tok, "kw")
                    out.append('<span class="%s">%s</span>' % (cls, html.escape(tok)))
                    continue
                if fqn:
                    disp = short(fqn) if m.group("q") else tok
                    h = self.href(fqn, here)
                    if h:
                        out.append('<a class="ref" href="%s" title="%s">%s</a>' % (
                            html.escape(h), html.escape(fqn), html.escape(disp)))
                    else:
                        out.append('<span class="ref-ext" title="%s">%s</span>' % (
                            html.escape(fqn), html.escape(disp)))
                    continue
                out.append(html.escape(tok))
            elif m.group("c"):
                out.append('<span class="cm">%s</span>' % html.escape(m.group(0)))
            else:
                out.append(html.escape(m.group(0)))
        return "".join(out)

    def doc_html(self, lines, here, aliases):
        body = MD.render("\n".join(lines))

        def link(m):
            txt = html.unescape(m.group(1))
            fqn = aliases.get(txt) or (txt if (txt in self.decls or txt in self.modules) else None)
            h = self.href(fqn, here) if fqn else None
            if not h:
                return m.group(0)
            return '<a class="ref" href="%s" title="%s"><code>%s</code></a>' % (
                html.escape(h), html.escape(fqn), m.group(1))
        # A code span naming a declaration becomes a link to it. This is a
        # renderer convention for the demo: which names a documentation
        # reference may use, and how the compiler resolves and checks
        # them, is decision D6.
        return re.sub(r"<code>([^<]+)</code>", link, body)


def anchor(fqn):
    return re.sub(r"[^\w'-]", "_", fqn.split(".")[-1])


def page(m):
    return m + ".html"


def aliases_for(site, here, decl):
    """Names a declaration's text may use unqualified: its module's own
    declarations, and the short and module-alias forms of what it refers
    to, where those are unambiguous."""
    al = {}
    for x in site.modules[here]["declarations"]:
        al[short(x["name"])] = x["name"]
    counts = {}
    for r in decl.get("refs", []):
        counts[short(r)] = counts.get(short(r), 0) + 1
    for r in decl.get("refs", []):
        s = short(r)
        parts = r.split(".")
        # As an author may write it through a module abbreviation:
        # FStar.Seq.Base.index as Base.index, Seq.index or Seq.Base.index.
        for i in range(1, len(parts) - 1):
            for j in range(i, len(parts) - 1):
                al.setdefault(".".join(parts[i:j + 1]) + "." + parts[-1], r)
            al.setdefault(parts[i] + "." + parts[-1], r)
        if counts[s] == 1:
            al.setdefault(s, r)
    return al


def first_sentence(lines):
    text = " ".join(l.strip() for l in lines).strip()
    m = re.match(r"(.+?[.!?])(\s|$)", text)
    return m.group(1) if m else text


# ------------------------------------------------------------------ pages --


def layout(site, title, here, main, toc=""):
    tpl = TEMPLATE
    if site.bare:
        # For a host that supplies the document skeleton itself.
        tpl = re.sub(r"<!DOCTYPE html>\n<html[^>]*><head>|</head><body>|</body></html>", "", tpl)
    groups = []
    for group, mods in site.project + [("Library, as referenced", site.library)]:
        items = "".join(
            '<li><a href="%s"%s>%s</a></li>' % (
                page(m), ' aria-current="page"' if m == here else "",
                html.escape(m))
            for m in mods)
        groups.append('<div class="nav-group"><h2>%s</h2><ul>%s</ul></div>' % (
            html.escape(group), items))
    return tpl.format(
        title=html.escape(title),
        badge=('<span class="badge">%s</span>' % html.escape(site.badge)) if site.badge else "",
        site=html.escape(site.title),
        nav="".join(groups),
        main=main,
        toc=toc,
        style=STYLE,
        script=SCRIPT,
    )


def render_decl(site, here, x):
    a = anchor(x["name"])
    al = aliases_for(site, here, x)
    info = analyse(x["type"])
    chips = ['<span class="kind">%s</span>' % html.escape(x["kind"])]
    if info["eff"] and x["kind"] != "type":
        chips.append('<span class="eff eff-%s">%s</span>' % (
            re.sub(r"\W", "", info["eff"]), html.escape(info["eff"])))
    if x.get("parent"):
        chips.append('<span class="parent">of <a href="%s">%s</a></span>' % (
            html.escape(site.href(x["parent"], here) or "#"), html.escape(short(x["parent"]))))
    parts = [
        '<section class="decl" id="%s">' % a,
        '<header class="decl-head"><h3><a class="self" href="#%s">%s</a></h3>%s</header>' % (
            a, html.escape(x["name"].split(".")[-1]),
            "".join(chips)),
        '<pre class="sig">%s</pre>' % site.code(x["signature"], here),
    ]
    if x.get("doc") is not None:
        parts.append('<div class="doc">%s</div>' % site.doc_html(x["doc"], here, al))
    else:
        parts.append('<p class="undoc">No documentation.</p>')
    if x.get("definition_source"):
        parts.append('<details class="defn" open><summary>Definition</summary><pre>%s</pre></details>' %
                     site.code(x["definition_source"], here, al))
    elif x.get("source") and x["source"].strip() != x["signature"].strip():
        parts.append('<details class="defn"><summary>As written</summary><pre>%s</pre></details>' %
                     site.code(x["source"], here, al))
    r = x.get("range")
    if r:
        parts.append('<p class="where">%s, line %d</p>' % (html.escape(r["file"]), r["start_line"]))
    parts.append("</section>")
    return "\n".join(parts)


def render_module(site, m):
    d = site.modules[m]
    decls = d["declarations"]
    documented = sum(1 for x in decls if x.get("doc") is not None)
    kind = "Interface" if d["interface"] else "Module without an interface"
    lib = m in site.library
    meta = '<p class="meta"><span>%s</span><span>%d declarations</span><span>%d documented</span></p>' % (
        kind, len(decls), documented)
    note = ""
    if lib:
        note = ('<p class="libnote">A library module, shown because the project refers to it. '
                'Its existing <code>(** … *)</code> comments are ordinary comments under the '
                'fresh-marker rule, so this is what the library looks like before any conversion: '
                'every declaration and its elaborated signature, and no text.</p>')
    body = "\n".join(render_decl(site, m, x) for x in decls) or '<p class="undoc">No exported declarations.</p>'
    main = '<h1 class="modname">%s</h1>%s%s<div class="decls">%s</div>' % (
        html.escape(m), meta, note, body)
    toc = '<h2>On this page</h2><ul>%s</ul>' % "".join(
        '<li><a href="#%s">%s</a></li>' % (anchor(x["name"]), html.escape(short(x["name"])))
        for x in decls)
    return layout(site, "%s · %s" % (m, site.title), m, main, toc)


def render_index(site, intro):
    rows = []
    for group, mods in site.project:
        items = []
        for m in mods:
            d = site.modules[m]
            decls = d["declarations"]
            documented = sum(1 for x in decls if x.get("doc") is not None)
            lead = next((first_sentence(x["doc"]) for x in decls if x.get("doc")), "")
            items.append(
                '<li><a href="%s">%s</a><span class="count">%d of %d documented</span>'
                '<p>%s</p></li>' % (
                    page(m), html.escape(m), documented, len(decls),
                    site.doc_html([lead], m, {}) if lead else ""))
        rows.append('<h2>%s</h2><ul class="modlist">%s</ul>' % (html.escape(group), "".join(items)))
    mods = "".join(rows)
    main = intro.replace("<!--MODULES-->", mods) if "<!--MODULES-->" in intro else intro + mods
    return layout(site, site.title, None, main)


def search_index(site):
    out = []
    for m, d in site.modules.items():
        for x in d["declarations"]:
            info = analyse(x["type"])
            out.append({
                "n": x["name"], "s": short(x["name"]), "m": m, "k": x["kind"],
                "e": info["eff"], "lib": m in site.library,
                "sig": re.sub(r"\s+", " ", site_short_text(x["signature"])).strip(),
                "a": info["args"], "r": info["res"],
                # Fully qualified: two modules' `sorted` are different
                # names, and the export says which one a contract means.
                "pre": sorted(info["pre"]),
                "post": sorted(info["post"]),
                "doc": first_sentence(x["doc"]) if x.get("doc") else "",
                "h": page(m) + "#" + anchor(x["name"]),
            })
    return out


def site_short_text(s):
    return TOKEN.sub(lambda m: short(m.group(0)) if m.group("q") else m.group(0), s)


# ------------------------------------------------------------------- main --


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("--fstar", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--title", default="F* Reference")
    ap.add_argument("--intro", help="HTML file with the landing page's text")
    ap.add_argument("--project", action="append", default=[],
                    help="GROUP=DIR:Mod1,Mod2,...  (DIR holds the checked files; exports run there)")
    ap.add_argument("--include", action="append", default=[])
    ap.add_argument("--library-cache", action="append", default=[])
    ap.add_argument("--badge", help="a short label shown next to the title on every page")
    ap.add_argument("--bare", action="store_true",
                    help="omit the doctype, html, head and body tags")
    args = ap.parse_args(argv[1:])

    modules, project = {}, []
    for spec in args.project:
        group, rest = spec.split("=", 1)
        pdir, mods = rest.split(":", 1)
        mods = mods.split(",")
        for m in mods:
            ck = find_checked(m, [os.path.join(pdir, "_cache")])
            if not ck:
                sys.exit("no checked file for %s in %s" % (m, pdir))
            modules[m] = export(args.fstar, ck, pdir, args.include)
        project.append((group, mods))

    # One hop into the library: the modules the project's declarations name.
    wanted = set()
    for m in list(modules):
        for x in modules[m]["declarations"]:
            for r in x.get("refs", []):
                parts = r.split(".")
                for i in range(len(parts) - 1, 0, -1):
                    cand = ".".join(parts[:i])
                    if cand in modules:
                        break
                    if find_checked(cand, args.library_cache):
                        wanted.add(cand)
                        break
    library = sorted(wanted - set(modules))
    for m in library:
        d = export(args.fstar, find_checked(m, args.library_cache), os.getcwd(), [])
        if d:
            modules[m] = d
    library = [m for m in library if m in modules]

    site = Site(args.title, modules, project)
    site.library = library
    site.bare = args.bare
    site.badge = args.badge
    os.makedirs(args.out, exist_ok=True)
    for m in modules:
        with open(os.path.join(args.out, page(m)), "w", encoding="utf-8") as f:
            f.write(render_module(site, m))
    intro = open(args.intro, encoding="utf-8").read() if args.intro else "<h1>%s</h1>" % html.escape(args.title)
    with open(os.path.join(args.out, "index.html"), "w", encoding="utf-8") as f:
        f.write(render_index(site, intro))
    with open(os.path.join(args.out, "search-index.js"), "w", encoding="utf-8") as f:
        f.write("window.FSTARDOC_INDEX = %s;\n" % json.dumps(search_index(site), separators=(",", ":")))
    print("%d pages (%d project, %d library) in %s" % (
        len(modules) + 1, len(modules) - len(library), len(library), args.out))
    return 0


# --------------------------------------------------------------- template --

TEMPLATE = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{title}</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=IBM+Plex+Sans:wght@400;500;600&family=JetBrains+Mono:wght@400;500&family=Source+Serif+4:ital,opsz,wght@0,8..60,400;0,8..60,600;1,8..60,400&display=swap">
<style>{style}</style>
</head><body>
<header class="top">
  <a class="brand" href="index.html">{site}</a>{badge}
  <div class="search">
    <label for="q" class="sr">Search declarations</label>
    <input id="q" type="search" autocomplete="off" spellcheck="false"
      placeholder="Search: a name, sorted, seq int -> prop">
    <div id="results" class="results" hidden></div>
  </div>
</header>
<div class="shell">
  <nav class="side" aria-label="Modules">{nav}</nav>
  <main class="content">{main}</main>
  <aside class="toc">{toc}</aside>
</div>
<script src="search-index.js"></script>
<script>{script}</script>
</body></html>
"""

STYLE = r"""
:root {
  --ground: #F6F8FB; --surface: #FFFFFF; --code: #E9F0F8; --line: #D5DEE9;
  --ink: #172335; --muted: #5A6778; --faint: #8592A3;
  --accent: #254C7A; --accent-soft: #DCE7F4;
  --ensures: #2E6B55; --ensures-soft: #DDEEE6;
  --requires: #8A6415; --requires-soft: #F3E9D2;
  --kw: #6B3F8E; --cm: #7A8595; --mark: #FFF3C4;
  --serif: "Source Serif 4", "Iowan Old Style", Georgia, serif;
  --sans: "IBM Plex Sans", "Segoe UI", system-ui, sans-serif;
  --mono: "JetBrains Mono", "SFMono-Regular", Menlo, Consolas, monospace;
}
@media (prefers-color-scheme: dark) {
  :root:not([data-theme="light"]) {
    --ground: #0E1520; --surface: #131C29; --code: #17233A; --line: #26344A;
    --ink: #DCE5F0; --muted: #9AA8BA; --faint: #6F7E92;
    --accent: #8DB5E6; --accent-soft: #1C2D46;
    --ensures: #7CC5A6; --ensures-soft: #173229;
    --requires: #D9B25E; --requires-soft: #33291A;
    --kw: #C3A1E0; --cm: #7D8B9E; --mark: #3A3318;
  }
}
:root[data-theme="dark"] {
  --ground: #0E1520; --surface: #131C29; --code: #17233A; --line: #26344A;
  --ink: #DCE5F0; --muted: #9AA8BA; --faint: #6F7E92;
  --accent: #8DB5E6; --accent-soft: #1C2D46;
  --ensures: #7CC5A6; --ensures-soft: #173229;
  --requires: #D9B25E; --requires-soft: #33291A;
  --kw: #C3A1E0; --cm: #7D8B9E; --mark: #3A3318;
}
* { box-sizing: border-box; }
html { scroll-padding-top: 5rem; }
body { margin: 0; background: var(--ground); color: var(--ink); font: 15px/1.55 var(--sans); }
a { color: var(--accent); text-decoration: none; }
a:hover { text-decoration: underline; text-underline-offset: 2px; }
a:focus-visible, input:focus-visible, summary:focus-visible { outline: 2px solid var(--accent); outline-offset: 2px; border-radius: 3px; }
code, pre, #q { font-family: var(--mono); font-size: 0.86em; font-variant-ligatures: none; }
.sr { position: absolute; width: 1px; height: 1px; overflow: hidden; clip: rect(0 0 0 0); }

.top { position: sticky; top: 0; z-index: 10; display: flex; gap: 1.5rem; align-items: center;
  padding-block: 0.7rem; padding-inline: max(16px, 2vw); background: var(--surface);
  border-bottom: 1px solid var(--line); }
.brand { font-weight: 600; letter-spacing: 0.01em; color: var(--ink); white-space: nowrap; }
.brand::before { content: "F\2605"; color: var(--accent); margin-right: 0.45em; font-family: var(--mono); font-weight: 500; }
.badge { font: 500 0.68rem var(--sans); letter-spacing: 0.08em; text-transform: uppercase; color: var(--requires);
  background: var(--requires-soft); border-radius: 3px; padding: 0.15rem 0.45rem; margin-left: -1rem; white-space: nowrap; }
.search { position: relative; flex: 1; max-width: 42rem; }
#q { width: 100%; font: 0.95rem var(--mono); color: var(--ink); background: var(--ground);
  border: 1px solid var(--line); border-radius: 6px; padding: 0.5rem 0.75rem; }
#q::placeholder { color: var(--faint); }
.results { position: absolute; left: 0; right: 0; top: calc(100% + 6px); max-height: 70vh; overflow-y: auto;
  background: var(--surface); border: 1px solid var(--line); border-radius: 8px;
  box-shadow: 0 12px 32px rgb(15 30 55 / 0.16); padding: 0.4rem 0; }
.results h4 { margin: 0.6rem 1rem 0.2rem; font: 600 0.72rem var(--sans); letter-spacing: 0.08em;
  text-transform: uppercase; color: var(--muted); display: flex; gap: 0.5rem; align-items: baseline; }
.results h4 small { font-weight: 400; letter-spacing: 0; text-transform: none; color: var(--faint); }
.hit { display: grid; gap: 0.1rem; padding: 0.45rem 1rem; color: var(--ink); }
.hit:hover, .hit.sel { background: var(--accent-soft); text-decoration: none; }
.hit .l1 { display: flex; gap: 0.5rem; align-items: baseline; flex-wrap: wrap; }
.hit .nm { font: 500 0.92rem var(--mono); color: var(--accent); }
.hit .md { font-size: 0.78rem; color: var(--muted); }
.hit .sg { font-variant-ligatures: none; font: 0.78rem var(--mono); color: var(--muted); overflow-wrap: anywhere;
  display: -webkit-box; -webkit-line-clamp: 2; -webkit-box-orient: vertical; overflow: hidden; }
.hit .dc { font: 0.85rem var(--serif); color: var(--ink); }
.empty { padding: 0.6rem 1rem; color: var(--muted); }

.shell { display: grid; grid-template-columns: 17rem minmax(0, 1fr) 13rem; gap: 2.5rem;
  padding-inline: max(16px, 2vw); max-width: 90rem; margin: 0 auto; }
.side, .toc { position: sticky; top: 4.2rem; align-self: start; max-height: calc(100vh - 5rem);
  overflow-y: auto; padding-block: 1.5rem; }
.nav-group + .nav-group { margin-top: 1.4rem; }
.side h2, .toc h2 { font: 600 0.72rem var(--sans); letter-spacing: 0.08em; text-transform: uppercase;
  color: var(--muted); margin: 0 0 0.5rem; }
.side ul, .toc ul { list-style: none; margin: 0; padding: 0; display: grid; gap: 0.1rem; }
.side a { display: block; font: 0.8rem var(--mono); color: var(--ink); padding: 0.2rem 0.5rem;
  border-radius: 4px; overflow-wrap: anywhere; }
.side a[aria-current] { background: var(--accent-soft); color: var(--accent); font-weight: 500; }
.toc a { font: 0.8rem var(--mono); color: var(--muted); overflow-wrap: anywhere; }
.content { padding-block: 1.8rem 5rem; min-width: 0; }

h1 { font: 600 1.9rem/1.2 var(--sans); margin: 0 0 0.4rem; text-wrap: balance; letter-spacing: -0.01em; }
.modname { font-family: var(--mono); font-weight: 500; font-size: 1.55rem; overflow-wrap: anywhere; }
.meta { display: flex; flex-wrap: wrap; gap: 0.3rem 1.2rem; margin: 0 0 1.6rem; color: var(--muted); font-size: 0.85rem; }
.libnote { font: 0.95rem/1.6 var(--serif); color: var(--muted); max-width: 65ch; margin: -0.6rem 0 1.6rem; }

.decls { display: grid; gap: 0; }
.decl { padding-block: 1.3rem; border-top: 1px solid var(--line); scroll-margin-top: 5rem; }
.decl:target { background: linear-gradient(90deg, var(--mark), transparent 70%); margin-inline: -0.8rem; padding-inline: 0.8rem; border-radius: 4px; }
.decl-head { display: flex; flex-wrap: wrap; align-items: baseline; gap: 0.35rem 0.6rem; margin-bottom: 0.55rem; }
.decl-head h3 { margin: 0; font: 500 1.08rem var(--mono); overflow-wrap: anywhere; }
.decl-head .self { color: var(--ink); }
.kind, .eff, .parent { font: 500 0.7rem var(--sans); letter-spacing: 0.04em; padding: 0.1rem 0.45rem;
  border-radius: 3px; color: var(--muted); border: 1px solid var(--line); }
.eff { color: var(--accent); border-color: var(--accent-soft); background: var(--accent-soft); font-family: var(--mono); letter-spacing: 0; }
.eff-Lemma { color: var(--ensures); background: var(--ensures-soft); border-color: var(--ensures-soft); }
.eff-stt, .eff-stt_ghost, .eff-stt_atomic { color: var(--requires); background: var(--requires-soft); border-color: var(--requires-soft); }
.parent { border: 0; padding: 0; letter-spacing: 0; font-size: 0.8rem; }
pre { margin: 0; overflow-x: auto; }
.sig { background: var(--code); padding: 0.75rem 0.95rem; border-radius: 6px; line-height: 1.5; color: var(--ink); }
.kw { color: var(--kw); }
.kw-req { color: var(--requires); font-weight: 500; }
.kw-ens { color: var(--ensures); font-weight: 500; }
.cm { color: var(--cm); font-style: italic; }
.ref-ext { border-bottom: 1px dotted var(--faint); }
.doc { font: 1.02rem/1.65 var(--serif); max-width: 68ch; margin-top: 0.8rem; }
.doc p { margin: 0 0 0.7rem; }
.doc code { background: var(--code); padding: 0.05em 0.3em; border-radius: 3px; font-size: 0.82em; }
.undoc { margin: 0.7rem 0 0; color: var(--faint); font-size: 0.85rem; font-style: italic; }
.defn { margin-top: 0.8rem; }
.defn summary { cursor: pointer; font: 600 0.72rem var(--sans); letter-spacing: 0.08em; text-transform: uppercase; color: var(--muted); }
.defn pre { margin-top: 0.45rem; padding: 0.7rem 0.95rem; border-left: 3px solid var(--accent-soft); background: var(--surface); }
.where { margin: 0.6rem 0 0; font: 0.75rem var(--mono); color: var(--faint); }

.lede { font: 1.15rem/1.6 var(--serif); max-width: 62ch; color: var(--ink); margin: 0.6rem 0 1.6rem; }
.tryit { display: flex; flex-wrap: wrap; gap: 0.5rem; margin: 0.4rem 0 2rem; padding: 0; list-style: none; }
.tryit button { font: 0.85rem var(--mono); color: var(--accent); background: var(--accent-soft); border: 1px solid transparent;
  border-radius: 999px; padding: 0.3rem 0.8rem; cursor: pointer; }
.tryit button:hover { border-color: var(--accent); }
.tryit button:focus-visible { outline: 2px solid var(--accent); outline-offset: 2px; }
.content > h2 { font: 600 0.78rem var(--sans); letter-spacing: 0.08em; text-transform: uppercase; color: var(--muted); margin: 2.2rem 0 0.7rem; }
.modlist { list-style: none; padding: 0; margin: 0; display: grid; gap: 0; }
.modlist li { padding-block: 0.8rem; border-top: 1px solid var(--line); display: grid; grid-template-columns: minmax(0, 1fr) auto; gap: 0.2rem 1rem; }
.modlist a { font: 500 0.92rem var(--mono); overflow-wrap: anywhere; }
.modlist .count { font-size: 0.8rem; color: var(--muted); font-variant-numeric: tabular-nums; }
.modlist p { grid-column: 1 / -1; margin: 0; font: 0.98rem/1.55 var(--serif); color: var(--muted); }
.modlist p p { margin: 0; }
.about { max-width: 68ch; font: 1rem/1.65 var(--serif); }
.about h3 { font: 600 0.95rem var(--sans); margin: 1.6rem 0 0.4rem; }
.about ul { padding-left: 1.2rem; }
.about li { margin-bottom: 0.35rem; }
.pipeline { font: 0.85rem/1.6 var(--mono); background: var(--code); padding: 0.8rem 1rem; border-radius: 6px; overflow-x: auto; white-space: pre; }

@media (max-width: 1100px) { .shell { grid-template-columns: 15rem minmax(0, 1fr); } .toc { display: none; } }
@media (max-width: 760px) {
  .shell { grid-template-columns: minmax(0, 1fr); gap: 0; }
  .side { position: static; max-height: none; padding-block: 1rem 0; border-bottom: 1px solid var(--line); }
  .top { flex-wrap: wrap; gap: 0.6rem; }
  .search { flex-basis: 100%; }
}
@media (prefers-reduced-motion: reduce) { * { scroll-behavior: auto !important; } }
"""

SCRIPT = r"""
(function () {
  var IDX = window.FSTARDOC_INDEX || [];
  var q = document.getElementById('q'), box = document.getElementById('results');
  var ALIAS = { nat: 'int', pos: 'int' };
  function esc(s) { return String(s).replace(/[&<>"']/g, function (c) {
    return {'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]; }); }
  function words(s) {
    return s.replace(/[(){}\[\],]/g, ' ').split(/\s+/).filter(Boolean).map(function (w) {
      w = w.replace(/^'/, '');
      if (/^[a-z]$/.test(w)) return '*';
      var p = w.split('.'); if (p.length > 1 && p[p.length-1] !== 't') w = p[p.length-1];
      return w;
    });
  }
  function shortOf(n) { var p = n.split('.'); return p.length > 1 && p[p.length-1] === 't' ? p[p.length-2] + '.t' : p[p.length-1]; }
  function tokEq(a, b, loose) {
    if (a === '*' || b === '*') return true;
    if (a === b) return true;
    return loose && (ALIAS[a] || a) === (ALIAS[b] || b);
  }
  function partMatch(qt, dt, loose) {
    if (!qt.length) return true;
    if (qt.length !== dt.length) return false;
    for (var i = 0; i < qt.length; i++) if (!tokEq(qt[i], dt[i], loose)) return false;
    return true;
  }
  function shapeScore(parts, d) {
    var res = parts[parts.length - 1], args = parts.slice(0, -1);
    var best = -1;
    [false, true].forEach(function (loose) {
      if (best >= 0) return;
      if (!partMatch(res, d.r, loose)) return;
      var used = d.a.map(function () { return false; }), ok = true;
      args.forEach(function (qa) {
        var j = d.a.findIndex(function (da, k) { return !used[k] && partMatch(qa, da, loose); });
        if (j < 0) ok = false; else used[j] = true;
      });
      if (!ok) return;
      best = 100 - 10 * (d.a.length - args.length) - (loose ? 5 : 0) - (d.lib ? 3 : 0);
    });
    return best;
  }
  function hit(d) {
    return '<a class="hit" href="' + esc(d.h) + '"><span class="l1"><span class="nm">' + esc(d.s) +
      '</span><span class="md">' + esc(d.m) + (d.e ? ' · ' + esc(d.e) : '') + '</span></span>' +
      (d.doc ? '<span class="dc">' + esc(d.doc) + '</span>' : '') +
      '<span class="sg">' + esc(d.sig) + '</span></a>';
  }
  function group(title, note, items) {
    if (!items.length) return '';
    return '<h4>' + esc(title) + (note ? ' <small>' + esc(note) + '</small>' : '') + '</h4>' +
      items.slice(0, 12).map(hit).join('');
  }
  function search(s) {
    s = s.trim();
    if (!s) return '';
    if (s.indexOf('->') >= 0) {
      var parts = s.split('->').map(function (p) { return words(p); });
      var scored = IDX.map(function (d) { return [shapeScore(parts, d), d]; })
        .filter(function (x) { return x[0] >= 0; })
        .sort(function (a, b) { return b[0] - a[0] || a[1].s.localeCompare(b[1].s); })
        .map(function (x) { return x[1]; });
      return group('Type shape', 'explicit arguments in any order; nat and pos also match int', scored) ||
        '<p class="empty">No declaration has a type of that shape. Try fewer arguments, or a letter such as a for any type.</p>';
    }
    var w = s.toLowerCase();
    var byName = IDX.filter(function (d) { return d.s.toLowerCase().indexOf(w) >= 0; })
      .sort(function (a, b) {
        var ea = a.s.toLowerCase() === w, eb = b.s.toLowerCase() === w;
        return (eb - ea) || (a.lib - b.lib) || a.s.length - b.s.length; });
    // Contracts name declarations by their resolved identity, so each
    // `sorted` gets its own groups, the project's first.
    var fq = {};
    IDX.forEach(function (d) {
      [['post', 'e'], ['pre', 'r']].forEach(function (pr) {
        d[pr[0]].forEach(function (n) {
          if (shortOf(n).toLowerCase() !== w) return;
          (fq[n] = fq[n] || { e: [], r: [] })[pr[1]].push(d);
        });
      });
    });
    var byN = {}; IDX.forEach(function (d) { byN[d.n] = d; });
    var html = group('Names', '', byName);
    Object.keys(fq).sort(function (a, b) {
      return ((byN[a] || {}).lib ? 1 : 0) - ((byN[b] || {}).lib ? 1 : 0) || a.localeCompare(b);
    }).forEach(function (n) {
      var from = n.split('.').slice(0, -1).join('.');
      html += group('Guarantee ' + shortOf(n), 'in the postcondition · ' + from, fq[n].e) +
              group('Require ' + shortOf(n), 'in the precondition · ' + from, fq[n].r);
    });
    return html || '<p class="empty">Nothing is named ' + esc(s) + ', and no contract mentions it.</p>';
  }
  var sel = -1;
  function update() {
    var h = search(q.value); box.innerHTML = h; box.hidden = !h; sel = -1;
  }
  function move(delta) {
    var hits = box.querySelectorAll('.hit'); if (!hits.length) return;
    if (sel >= 0) hits[sel].classList.remove('sel');
    sel = (sel + delta + hits.length) % hits.length;
    hits[sel].classList.add('sel'); hits[sel].scrollIntoView({ block: 'nearest' });
  }
  q.addEventListener('input', update);
  q.addEventListener('focus', function () { if (q.value.trim()) update(); });
  q.addEventListener('keydown', function (e) {
    if (e.key === 'ArrowDown') { e.preventDefault(); move(1); }
    else if (e.key === 'ArrowUp') { e.preventDefault(); move(-1); }
    else if (e.key === 'Enter') { var hits = box.querySelectorAll('.hit'); var t = hits[sel >= 0 ? sel : 0]; if (t) location.href = t.href; }
    else if (e.key === 'Escape') { box.hidden = true; q.blur(); }
  });
  document.addEventListener('click', function (e) { if (!e.target.closest('.search')) box.hidden = true; });
  document.addEventListener('keydown', function (e) {
    if (e.key === '/' && document.activeElement !== q) { e.preventDefault(); q.focus(); }
  });
  document.querySelectorAll('[data-query]').forEach(function (b) {
    b.addEventListener('click', function () { q.value = b.getAttribute('data-query'); q.focus(); update(); });
  });
})();
"""

if __name__ == "__main__":
    sys.exit(main(sys.argv))
