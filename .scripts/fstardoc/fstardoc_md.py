#!/usr/bin/env python3
"""Turn `fstar.exe --export_docs` into Markdown for an off-the-shelf site
generator: mkdocs, mdBook, or anything else that reads a tree of Markdown.

This is a second, deliberately duller consumer of the versioned JSON
export (schema "fstar-module-docs", version 4), alongside
`fstardoc_site.py`. The two make different points.

`fstardoc_site.py` shows what the export makes *possible*: linked
signatures, and search by the names a contract mentions and by the shape
of a type (whitepaper D7). It owns its HTML, CSS and search.

This script shows what the export makes *cheap*: it emits Markdown and
stops. Theme, layout, navigation, mobile rendering, dark mode and
full-text search all come from a site generator nobody has to write or
argue about. Documentation content is then the only open question, which
is the point -- there is no theme to review.

    fstardoc_md.py --fstar out/bin/fstar.exe --out docs-md \\
        --cache DIR ... --module FStar.List.Tot.Base ... \\
        [--include DIR ...] [--title T] [--backend mkdocs|mdbook|both]

THE MARKDOWN SUBSET
-------------------
Every construct this script emits, and nothing else:

  * ATX headings (`#`, `##`)
  * paragraphs of text
  * fenced code blocks with an info string (```` ```fsharp ````)
  * inline code spans (`` `x` ``)
  * inline links (`[text](target)`), including links whose text is an
    inline code span
  * bullet lists (`-`), nested one level in the mdBook summary
  * emphasis (`*text*`)

Not emitted: raw HTML, reference links, setext headings, tables, block
quotes, images, footnotes, autolinks, hard line breaks, ordered lists,
HTML entities, thematic breaks, and every site-generator extension
(admonitions, tabs, `{#custom-id}` heading attributes).

That list is a promise about output, not an assumption about input: a
doc comment's own text is whatever its author wrote, and passes through
this script unexamined. Constraining *authored* documentation to a
subset is a validation question (whitepaper D6), not something a
renderer can decide.

The subset exists so the emitted Markdown is portable across site
generators without extensions -- and so that a Markdown parser verified
in F* has a bounded target to aim at, rather than all of CommonMark. It
is why nothing here emits raw HTML, even where HTML would render better:
raw HTML blocks and inline HTML are among the most intricate parts of
the CommonMark specification, and a signature with clickable names is
not worth that cost. The names a declaration mentions are listed under
it instead, as ordinary links.

No third-party library is needed. Rendering Markdown is the site
generator's job, so this script never parses any.
"""

import argparse
import json
import os
import re
import subprocess
import sys

SCHEMA, VERSION = "fstar-module-docs", 4

# Deliberately duplicated from fstardoc_site.py rather than shared: that
# module imports markdown-it at load time, and a consumer that only
# writes Markdown should need no Markdown library at all.


def find_checked(module, dirs):
    for d in dirs:
        for ext in (".fsti.checked", ".fst.checked"):
            p = os.path.join(d, module + ext)
            if os.path.exists(p):
                return p
    return None


def export(fstar, checked, includes):
    cmd = [fstar]
    for i in includes:
        cmd += ["--include", i]
    cmd += ["--export_docs", os.path.abspath(checked)]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        sys.stderr.write("export failed for %s:\n%s\n" % (checked, r.stderr))
        return None
    d = json.loads(r.stdout)
    if d.get("schema") != SCHEMA or d.get("version") != VERSION:
        sys.exit("unexpected schema %r version %r" % (d.get("schema"), d.get("version")))
    return d


def short(fqn):
    parts = fqn.split(".")
    # A bare `t` says nothing, so an abstract type keeps its module.
    if len(parts) >= 2 and parts[-1] == "t":
        return parts[-2] + ".t"
    return parts[-1]


# Signatures arrive fully qualified, which is precise and unreadable: a
# lemma's contract becomes a wall of `FStar.List.Tot.Base.`. Names are
# shortened for display, and the resolved name stays available as the
# target of the Mentions links under the declaration. Shortening cannot
# be reversed from the text alone -- two modules' `sorted` look alike --
# which is the cost of not linking inside the fence.
QUALIFIED = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)+")


def short_text(s):
    return QUALIFIED.sub(lambda m: short(m.group(0)), s)


# ------------------------------------------------------------- anchors --

# Both backends derive a heading's anchor from its text, and neither is
# configured here, so the anchor has to be predicted rather than chosen:
# the subset excludes `{#custom-id}`.
#
# mkdocs (Python-Markdown's toc extension) lowercases, drops characters
# that are neither word characters nor spaces nor hyphens, then turns
# runs of spaces and hyphens into a single hyphen. mdBook lowercases,
# keeps alphanumerics, `_` and `-`, and turns spaces into hyphens. For a
# heading that is a single F* identifier the two agree, and the rule
# below is the intersection: it is what both produce.
#
# The one place they could differ is a character F* allows in a name and
# neither backend keeps -- an apostrophe, as in `lemma'`. Both drop it,
# so `lemma'` and `lemma` would collide; `anchors_for` resolves any
# collision explicitly rather than letting one heading shadow another.
def slug(text):
    s = text.lower()
    s = re.sub(r"[^\w\s-]", "", s, flags=re.UNICODE)
    s = re.sub(r"[\s-]+", "-", s)
    return s.strip("-")


def anchors_for(decls):
    """A stable anchor per declaration, disambiguating any collision.

    Returns {fully qualified name: anchor}. Collisions are real: `lemma`
    and `lemma'` slug alike, and so do a type `t` and anything else
    whose name differs only in case.
    """
    out, used = {}, {}
    for x in decls:
        base = slug(short(x["name"])) or "decl"
        n = used.get(base, 0)
        used[base] = n + 1
        out[x["name"]] = base if n == 0 else "%s-%d" % (base, n + 1)
    return out


# ----------------------------------------------------------- rendering --

# A fence long enough to contain the text, so a signature or definition
# that itself contains backticks cannot end the block early. CommonMark
# allows any run of three or more.
def fence(text, info=""):
    longest = max((len(m) for m in re.findall(r"`+", text)), default=0)
    bar = "`" * max(3, longest + 1)
    return "%s%s\n%s\n%s" % (bar, info, text.rstrip("\n"), bar)


def code(text):
    """An inline code span, with a fence long enough for its content."""
    longest = max((len(m) for m in re.findall(r"`+", text)), default=0)
    bar = "`" * (longest + 1)
    pad = " " if text.startswith("`") or text.endswith("`") else ""
    return "%s%s%s%s%s" % (bar, pad, text, pad, bar)


# Markdown link destinations: parentheses and whitespace would end the
# destination early, and our destinations are generated paths and
# anchors, so percent-encoding the few characters that matter is enough.
def dest(target):
    return target.replace("(", "%28").replace(")", "%29").replace(" ", "%20")


def link(text, target):
    return "[%s](%s)" % (text, dest(target))


class Book:
    """The set of modules being rendered, and how to link between them."""

    def __init__(self, title, modules, backend, note=None):
        self.title = title
        self.modules = modules
        self.backend = backend
        self.note = note
        self.anchors = {m: anchors_for(d["declarations"]) for m, d in modules.items()}
        # Fully qualified name -> (module, anchor), for resolving refs.
        self.index = {}
        for m, d in modules.items():
            for x in d["declarations"]:
                self.index[x["name"]] = (m, self.anchors[m][x["name"]])

    def page(self, module):
        return module + ".md"

    def href(self, fqn, here):
        """A link to a declaration, or None when it is outside this book."""
        if fqn not in self.index:
            return None
        m, a = self.index[fqn]
        if m == here:
            return "#" + a
        return "%s#%s" % (self.page(m), a)


def render_module(book, module):
    d = book.modules[module]
    decls = d["declarations"]
    documented = sum(1 for x in decls if x.get("doc") is not None)
    out = ["# %s" % module, ""]

    kind = "Interface" if d["interface"] else "Module without an interface"
    out += ["%s. %d declarations, %d documented." % (kind, len(decls), documented), ""]

    # A module written before this proposal reports nothing documented,
    # and saying so without explanation misrepresents it: its `(** ... *)`
    # comments are ordinary comments under the fresh-marker rule, not
    # missing documentation. The caller supplies the wording.
    if book.note and documented == 0:
        out += [book.note, ""]

    if not decls:
        out += ["*No exported declarations.*", ""]

    for x in decls:
        out += render_decl(book, module, x)
    return "\n".join(out).rstrip("\n") + "\n"


def render_decl(book, module, x):
    # The heading text is what both backends turn into this declaration's
    # anchor; `Book.anchors` predicts the same slug so that links from
    # other pages land here. `check_anchors` verifies the two agree.
    out = ["## %s" % short(x["name"]), ""]

    # The kind, the effect's name when there is one, and the type a
    # constructor belongs to: a short paragraph rather than a table,
    # which the subset excludes.
    facts = [x["kind"]]
    t = x.get("type") or {}
    if t.get("k") == "arrow":
        eff = t["c"]["eff"]
        facts.append({"Prims.Tot": "Tot", "Prims.GTot": "GTot"}.get(eff, short(eff)))
    if x.get("parent"):
        target = book.href(x["parent"], module)
        name = code(short(x["parent"]))
        facts.append("of " + (link(name, target) if target else name))
    out += [" · ".join(facts), ""]

    out += [fence(short_text(x["signature"]), "fsharp"), ""]

    # The author's own Markdown, passed through untouched. An
    # undocumented declaration says so, rather than being silently
    # empty: a null doc is a fact about the declaration, and a reader
    # and a coverage count should see the same one.
    if x.get("doc") is not None:
        out += ["\n".join(x["doc"]), ""]
    else:
        out += ["*No documentation.*", ""]

    if x.get("definition_source"):
        out += ["Definition:", "", fence(x["definition_source"], "fsharp"), ""]

    # Names this declaration mentions, as links. This is what replaces
    # linking inside the signature, which would need raw HTML. Only
    # names that resolve within this book are listed -- an unresolvable
    # name is not useful to a reader and cannot be linked.
    mentions = []
    for r in x.get("refs", []):
        if r == x["name"]:
            continue
        target = book.href(r, module)
        if target:
            mentions.append(link(code(short(r)), target))
    if mentions:
        # Dedupe, keeping first-seen order.
        seen, ordered = set(), []
        for m in mentions:
            if m not in seen:
                seen.add(m)
                ordered.append(m)
        out += ["Mentions: " + ", ".join(ordered), ""]

    where = x.get("range")
    if where:
        out += ["*%s, line %d*" % (where["file"], where["start_line"]), ""]

    return out


def render_index(book):
    out = ["# %s" % book.title, ""]
    out += ["Generated from `fstar.exe --export_docs`, schema %s version %d."
            % (SCHEMA, VERSION), ""]
    out += ["## Modules", ""]
    for m in sorted(book.modules):
        d = book.modules[m]
        decls = d["declarations"]
        documented = sum(1 for x in decls if x.get("doc") is not None)
        out.append("- %s — %d of %d documented"
                   % (link(code(m), book.page(m)), documented, len(decls)))
    out.append("")
    return "\n".join(out)


# ---------------------------------------------------------- self-check --


def check_anchors(out_dir, book):
    """Verify every generated link resolves, by reading the files back.

    Anchors are predicted from heading text rather than written down (the
    subset has no `{#id}`), so a wrong prediction would break links
    silently and uniformly. This reads each page, recomputes the anchors
    its headings will produce, and resolves every link destination
    against them. Returns a list of problems, empty when all is well.
    """
    heads, bad = {}, []
    for name in os.listdir(out_dir):
        if not name.endswith(".md"):
            continue
        text = open(os.path.join(out_dir, name), encoding="utf-8").read()
        seen, anchors = {}, set()
        in_fence = False
        for line in text.splitlines():
            # A `##` inside a fenced block is not a heading.
            if re.match(r"^(`{3,}|~{3,})", line):
                in_fence = not in_fence
                continue
            if in_fence or not line.startswith("## "):
                continue
            base = slug(line[3:].strip()) or "decl"
            n = seen.get(base, 0)
            seen[base] = n + 1
            anchors.add(base if n == 0 else "%s-%d" % (base, n + 1))
        heads[name] = anchors

    for name in sorted(heads):
        text = open(os.path.join(out_dir, name), encoding="utf-8").read()
        for target in re.findall(r"\]\(([^)]*)\)", text):
            page, _, frag = target.partition("#")
            page = page or name
            if page not in heads:
                bad.append("%s: link to missing page %s" % (name, page))
            elif frag and frag not in heads[page]:
                bad.append("%s: link to missing anchor %s#%s" % (name, page, frag))
    return bad


# The subset, as checks rather than prose. Each entry is a construct the
# subset excludes, and a pattern matching a line that uses it. Applied to
# the generated Markdown outside fenced code blocks, with inline code
# spans blanked first so that a `<` or `|` inside `` `...` `` is not
# mistaken for markup.
#
# This is the machine-checkable form of the docstring's promise, and it is
# also a sketch of the diagnostic D6 describes: run over *authored*
# documentation rather than generated pages, it says which doc comments
# leave the supported subset.
OUT_OF_SUBSET = [
    ("raw HTML",             re.compile(r"<[A-Za-z/!?]")),
    ("HTML entity",          re.compile(r"&(?:#\d+|#[xX][0-9A-Fa-f]+|[A-Za-z][A-Za-z0-9]*);")),
    ("image",                re.compile(r"!\[")),
    ("footnote",             re.compile(r"\[\^")),
    ("link reference",       re.compile(r"^\s{0,3}\[[^\]]+\]:\s")),
    ("block quote",          re.compile(r"^\s{0,3}>")),
    ("ordered list",         re.compile(r"^\s{0,3}\d+[.)]\s")),
    ("table delimiter",      re.compile(r"^\s{0,3}\|?[\s:-]*\|[\s:|-]*$")),
    ("thematic break",       re.compile(r"^\s{0,3}([-*_])[ \t]*(?:\1[ \t]*){2,}$")),
    ("hard line break",      re.compile(r"(?:  |\\)$")),
    ("heading attributes",   re.compile(r"\{#[^}]*\}\s*$")),
]

INLINE_CODE = re.compile(r"(`+)(?:.*?)\1")


def check_subset(out_dir):
    """Report generated lines that use a construct outside the subset.

    Authored documentation passes through this script untouched, so a
    violation usually means a doc comment used something the subset does
    not cover -- which is a fact worth knowing, not necessarily a bug.
    """
    bad = []
    for name in sorted(os.listdir(out_dir)):
        if not name.endswith(".md"):
            continue
        in_fence, fence_bar = False, ""
        for n, line in enumerate(
                open(os.path.join(out_dir, name), encoding="utf-8").read().splitlines(), 1):
            m = re.match(r"^\s{0,3}(`{3,}|~{3,})", line)
            if m and not in_fence:
                in_fence, fence_bar = True, m.group(1)[0] * 3
                continue
            if in_fence:
                if m and line.strip().startswith(fence_bar):
                    in_fence = False
                continue
            probe = INLINE_CODE.sub(lambda mm: " " * len(mm.group(0)), line)
            # Setext headings are excluded, but a run of `-` is also how a
            # thematic break looks; the pattern above already covers it.
            for what, pat in OUT_OF_SUBSET:
                if pat.search(probe):
                    bad.append("%s:%d: %s: %s" % (name, n, what, line.strip()[:70]))
    return bad


# ------------------------------------------------------------- backends --

# Only the navigation file differs between backends. mkdocs reads YAML;
# mdBook reads a Markdown bullet list of links, which is inside the
# subset.


def write_mkdocs(out_dir, book):
    lines = ["site_name: %s" % json.dumps(book.title),
             "docs_dir: .",
             "site_dir: ../_site_mkdocs",
             "theme:",
             "  name: material",
             "markdown_extensions: []",
             "nav:",
             "  - Index: index.md"]
    for m in sorted(book.modules):
        lines.append("  - %s: %s" % (json.dumps(m), book.page(m)))
    with open(os.path.join(out_dir, "mkdocs.yml"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")


def write_mdbook(out_dir, book):
    lines = ["# Summary", "", "- " + link("Index", "index.md")]
    for m in sorted(book.modules):
        lines.append("- " + link(code(m), book.page(m)))
    with open(os.path.join(out_dir, "SUMMARY.md"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")
    toml = ['[book]', 'title = %s' % json.dumps(book.title),
            'src = "."', '', '[output.html]', '']
    with open(os.path.join(out_dir, "book.toml"), "w", encoding="utf-8") as f:
        f.write("\n".join(toml) + "\n")


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("--fstar", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--title", default="F* Reference")
    ap.add_argument("--module", action="append", default=[],
                    help="a module to document; repeatable")
    ap.add_argument("--modules-from",
                    help="file with one module name per line (# comments allowed)")
    ap.add_argument("--cache", action="append", default=[],
                    help="directory holding checked files; repeatable")
    ap.add_argument("--include", action="append", default=[])
    ap.add_argument("--backend", choices=["mkdocs", "mdbook", "both"], default="both")
    ap.add_argument("--strict-subset", action="store_true",
                    help="fail when any generated line leaves the subset")
    ap.add_argument("--note",
                    help="a paragraph added to every module page that has no "
                         "documented declaration, explaining why")
    args = ap.parse_args(argv[1:])

    wanted = list(args.module)
    if args.modules_from:
        for line in open(args.modules_from, encoding="utf-8"):
            line = line.split("#", 1)[0].strip()
            if line:
                wanted.append(line)
    if not wanted:
        sys.exit("no modules given: pass --module or --modules-from")

    modules = {}
    for m in wanted:
        ck = find_checked(m, args.cache)
        if not ck:
            sys.stderr.write("no checked file for %s\n" % m)
            continue
        d = export(args.fstar, ck, args.include)
        if d:
            modules[m] = d
    if not modules:
        sys.exit("nothing exported")

    book = Book(args.title, modules, args.backend, args.note)
    os.makedirs(args.out, exist_ok=True)
    for m in modules:
        with open(os.path.join(args.out, book.page(m)), "w", encoding="utf-8") as f:
            f.write(render_module(book, m))
    with open(os.path.join(args.out, "index.md"), "w", encoding="utf-8") as f:
        f.write(render_index(book))

    if args.backend in ("mkdocs", "both"):
        write_mkdocs(args.out, book)
    if args.backend in ("mdbook", "both"):
        write_mdbook(args.out, book)

    sys.stderr.write("%d modules, %d declarations -> %s\n" % (
        len(modules), sum(len(d["declarations"]) for d in modules.values()), args.out))

    rc = 0
    bad = check_anchors(args.out, book)
    if bad:
        sys.stderr.write("broken links (%d):\n" % len(bad))
        for b in bad[:20]:
            sys.stderr.write("  %s\n" % b)
        rc = 1
    else:
        sys.stderr.write("all links resolve\n")

    out_of = check_subset(args.out)
    if out_of:
        sys.stderr.write("outside the Markdown subset (%d):\n" % len(out_of))
        for b in out_of[:20]:
            sys.stderr.write("  %s\n" % b)
        if args.strict_subset:
            rc = 1
    else:
        sys.stderr.write("every line is inside the Markdown subset\n")
    return rc


if __name__ == "__main__":
    sys.exit(main(sys.argv))
