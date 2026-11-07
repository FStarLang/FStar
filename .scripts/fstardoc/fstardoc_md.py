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
# Where they differ is in what they do about a *collision*, and F* makes
# collisions ordinary: an apostrophe is legal in a name and neither
# backend keeps it, so `lemma` and `lemma'` slug alike. mkdocs then
# appends `_1` and mdBook `-1`, which no single Markdown tree can link to
# at once. `layout_for` therefore makes the heading text itself unique, so
# neither backend has anything left to disambiguate.
def slug(text):
    s = text.lower()
    s = re.sub(r"[^\w\s-]", "", s, flags=re.UNICODE)
    s = re.sub(r"[\s-]+", "-", s)
    return s.strip("-")


def layout_for(decls):
    """The heading text and anchor for each declaration.

    Returns {fully qualified name: (heading, anchor)}.

    Collisions are real and common: `rev_append` and `rev_append'` slug
    alike, because both backends drop the apostrophe, and `ulib` is full
    of primed variants.

    A colliding heading is made unique *in its text*, so that neither
    backend has to disambiguate it. That matters because they disambiguate
    differently -- mkdocs appends `_1`, mdBook appends `-1` -- and one
    Markdown tree has to link correctly under both. The heading
    `rev_append (2)` makes both produce `rev_append-2`, since each strips
    the parentheses and turns the remaining space into a hyphen. Verified
    against the HTML both backends generate, not assumed.

    Two further rules make the result worth linking to:

    *Every* member of a colliding group is numbered, so none silently owns
    the bare `#rev_append`. `FStar.List.Tot.Properties` really does declare
    both `rev'_append` and `rev_append`, and letting whichever comes first
    answer `#rev_append` would send a reader to the other one.

    The numbering follows the sorted names, not the order of declaration,
    so an anchor does not change when someone moves a declaration within
    its module. Documentation anchors end up in other people's links.
    """
    names = {}
    for x in decls:
        base = slug(short(x["name"])) or "decl"
        names.setdefault(base, []).append(x["name"])

    out = {}
    for base, group in names.items():
        if len(group) == 1:
            out[group[0]] = (short(group[0]), base)
            continue
        for i, fqn in enumerate(sorted(group), 1):
            heading = "%s (%d)" % (short(fqn), i)
            out[fqn] = (heading, slug(heading))
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
        self.layout = {m: layout_for(d["declarations"]) for m, d in modules.items()}
        # Fully qualified name -> (module, anchor), for resolving refs.
        self.index = {}
        for m, d in modules.items():
            for x in d["declarations"]:
                self.index[x["name"]] = (m, self.layout[m][x["name"]][1])

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
    # anchor; `Book.layout` chose text whose slug both produce, so links
    # from other pages land here. `check_anchors` verifies that, and
    # `--verify-html` checks it against what the backends really emit.
    heading, _ = book.layout[module][x["name"]]
    out = ["## %s" % heading, ""]

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
        anchors = set()
        in_fence = False
        for line in text.splitlines():
            # A `##` inside a fenced block is not a heading.
            if re.match(r"^(`{3,}|~{3,})", line):
                in_fence = not in_fence
                continue
            if in_fence or not line.startswith("## "):
                continue
            anchors.add(slug(line[3:].strip()) or "decl")
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


H2_ID = re.compile(r"<h2[^>]*\bid=\"([^\"]+)\"")


def verify_html(out_dir, book, built):
    """Compare the anchors we predicted with the ones a backend emitted.

    `check_anchors` only proves the generated links agree with our own
    slug rule. That is self-consistency: if the rule is wrong, every link
    is wrong together and nothing notices. This reads the HTML a backend
    actually produced and compares heading ids against the prediction,
    which is the only check that can catch a wrong rule.

    [built] maps a backend name to its output directory. Backends that
    were not built are skipped.
    """
    problems = []
    for backend, root in sorted(built.items()):
        if not os.path.isdir(root):
            continue
        for m in sorted(book.modules):
            path = os.path.join(root, book.page(m)[:-3] + ".html")
            if not os.path.exists(path):
                problems.append("%s: %s not built" % (backend, m))
                continue
            actual = H2_ID.findall(open(path, encoding="utf-8", errors="replace").read())
            expect = [a for _, a in
                      (book.layout[m][x["name"]] for x in book.modules[m]["declarations"])]
            if len(actual) != len(expect):
                problems.append("%s: %s has %d headings, expected %d"
                                % (backend, m, len(actual), len(expect)))
            for e, a in zip(expect, actual):
                if e != a:
                    problems.append("%s: %s: predicted %r, emitted %r" % (backend, m, e, a))
    return problems


# ------------------------------------------------------------- backends --

# Only the navigation file differs between backends. mkdocs reads YAML;
# mdBook reads a Markdown bullet list of links, which is inside the
# subset.


def write_mkdocs(out_dir, book, theme="mkdocs"):
    # `mkdocs` and `readthedocs` ship with mkdocs itself, so the generated
    # configuration builds with no theme to install. The subset uses no
    # extensions, hence the empty list rather than a default set.
    lines = ["site_name: %s" % json.dumps(book.title),
             "docs_dir: docs",
             "site_dir: site",
             "use_directory_urls: false",
             "theme:",
             "  name: %s" % theme,
             "markdown_extensions: []",
             # SUMMARY.md is mdBook's navigation; mkdocs should ignore it.
             "exclude_docs: |",
             "  SUMMARY.md",
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
    with open(os.path.join(out_dir, "docs", "SUMMARY.md"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")
    toml = ['[book]', 'title = %s' % json.dumps(book.title),
            'src = "docs"', '', '[output.html]', '']
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
    ap.add_argument("--verify-html", action="store_true",
                    help="after generating, compare predicted anchors with the "
                         "HTML each backend emitted in site/ and book/")
    ap.add_argument("--mkdocs-theme", default="mkdocs",
                    help="theme named in the generated mkdocs.yml; "
                         "mkdocs and readthedocs need no install")
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
    docs = os.path.join(args.out, "docs")
    os.makedirs(docs, exist_ok=True)
    for m in modules:
        with open(os.path.join(docs, book.page(m)), "w", encoding="utf-8") as f:
            f.write(render_module(book, m))
    with open(os.path.join(docs, "index.md"), "w", encoding="utf-8") as f:
        f.write(render_index(book))

    if args.backend in ("mkdocs", "both"):
        write_mkdocs(args.out, book, args.mkdocs_theme)
    if args.backend in ("mdbook", "both"):
        write_mdbook(args.out, book)

    sys.stderr.write("%d modules, %d declarations -> %s\n" % (
        len(modules), sum(len(d["declarations"]) for d in modules.values()), args.out))

    rc = 0
    bad = check_anchors(docs, book)
    if bad:
        sys.stderr.write("broken links (%d):\n" % len(bad))
        for b in bad[:20]:
            sys.stderr.write("  %s\n" % b)
        rc = 1
    else:
        sys.stderr.write("all links resolve\n")

    out_of = check_subset(docs)
    if out_of:
        sys.stderr.write("outside the Markdown subset (%d):\n" % len(out_of))
        for b in out_of[:20]:
            sys.stderr.write("  %s\n" % b)
        if args.strict_subset:
            rc = 1
    else:
        sys.stderr.write("every line is inside the Markdown subset\n")

    if args.verify_html:
        built = {"mkdocs": os.path.join(args.out, "site"),
                 "mdbook": os.path.join(args.out, "book")}
        found = {k: v for k, v in built.items() if os.path.isdir(v)}
        if not found:
            sys.stderr.write("no built HTML to verify; run mkdocs/mdbook first\n")
        else:
            problems = verify_html(args.out, book, found)
            if problems:
                sys.stderr.write("anchor predictions wrong (%d):\n" % len(problems))
                for b in problems[:20]:
                    sys.stderr.write("  %s\n" % b)
                rc = 1
            else:
                sys.stderr.write("anchors match the emitted HTML in %s\n"
                                 % ", ".join(sorted(found)))
    return rc


if __name__ == "__main__":
    sys.exit(main(sys.argv))
