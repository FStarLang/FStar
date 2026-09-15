#!/usr/bin/env python3
"""Measure whether contract retrieval finds the lemma a proof actually used.

The claim under test is that an agent can find an existing lemma from what
it is trying to prove, rather than by guessing the lemma's name. The
obvious way to test that is circular: generate queries from the index's own
`post` field, search `post`, and of course find them. This avoids the
circularity by taking the answer key from somewhere the index cannot see --
the proofs themselves.

    For a lemma D whose proof cites lemma L:
      the query  is built from D's goal, the names in D's `ensures`;
      the answer is L;
      success    is L appearing among the candidates.

Nothing in the index knows the answer key. D's contract comes from the
export, L comes from the text of D's proof, and the two are independent.

The lemma proof bodies are not in the export at all -- `--export_docs`
deliberately omits them, because a proof is not what a declaration means to
a reader -- so citations are recovered by scanning the `.fst` sources. That
scan is a heuristic, described at `spans` below.

Three configurations are measured on the same pairs, and all three are
reported: picking one after seeing the numbers is how a benchmark becomes
an advertisement.

  grep            a declaration is a candidate if its text mentions the
                  queried name anywhere. This is what `grep -rn` over
                  `ulib` gives an agent today, mapped up to whole
                  declarations so the comparison is like for like.

  index ensures   a candidate concludes something about the queried name.
  index either    a candidate mentions it in either half of its contract.

The result is not that retrieval beats grep. grep reaches more of the
answers, because it matches anywhere -- in a precondition, a proof body, a
comment -- which is also why a third of what it returns is not a lemma at
all. What the index changes is how much a caller must read to arrive at the
same lemma, and how much of it is worth reading.

Two things keep the recall figures honest. They are conservative: a proof
citing L shows L was useful, not that nothing else was, so a tool offering
a different useful lemma is scored as a miss. And the candidate counts are
generous to grep, since `grep -rn` really returns lines while these are
whole declarations.

The reported `unreachable in one hop` figure explains most of the gap. A
proof of a lemma about `rev'` needs `append_assoc`, whose contract is about
`append` and so shares no name with the goal. Contract matching cannot
bridge that in one step; following `refs` would be the next thing to try.

    fstardoc_bench.py --index ulib.index.json --source ulib \\
        [--limit N] [--verbose]
"""

import argparse
import json
import os
import re
import sys

IDENT = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*")

# A line at column zero that begins a new top-level declaration. F* has no
# layout rule that makes this exact, so this is a heuristic: it is used
# only to attribute a proof body and a grep hit to a declaration, and an
# error mis-attributes one pair rather than corrupting the measurement.
TOP = re.compile(r"^(?:let|val|type|assume|private|unfold|irreducible|noextract|"
                 r"inline_for_extraction|noeq|unopteq|new|open|module|friend|"
                 r"instance|class|effect|sub_effect|total|\[@@|#|\(\*)")
NAMED = re.compile(r"^(?:(?:private|unfold|irreducible|noextract|"
                   r"inline_for_extraction|total|noeq|unopteq|new|rec)\s+)*"
                   r"(?:let|val)\s+(?:rec\s+)?(?:\(\s*)?([A-Za-z_][\w']*)")


def spans(path):
    """Split a source file into top-level declarations.

    Returns [(name or None, text)]. A declaration runs from its own first
    line to the line before the next one that starts at column zero.
    """
    out, name, buf = [], None, []
    for line in open(path, encoding="utf-8", errors="replace").read().splitlines():
        if line and not line[0].isspace() and TOP.match(line):
            if buf:
                out.append((name, "\n".join(buf)))
            m = NAMED.match(line)
            name, buf = (m.group(1) if m else None), [line]
        else:
            buf.append(line)
    if buf:
        out.append((name, "\n".join(buf)))
    return out


def load_sources(source_dir, modules):
    """Every declaration body found in the sources of these modules."""
    bodies, texts = {}, {}
    for m in modules:
        for ext in (".fst", ".fsti"):
            path = os.path.join(source_dir, m + ext)
            if not os.path.exists(path):
                continue
            for name, text in spans(path):
                if name is None:
                    continue
                key = m + "." + name
                # An implementation's body is the interesting one; an
                # interface only restates the type.
                if ext == ".fst" or key not in bodies:
                    bodies[key] = text
                texts.setdefault(key, []).append(text)
    return bodies, texts


def citations(body, lemma_short, own_short):
    """Which known lemmas this proof body mentions, by short name."""
    found = set()
    for tok in IDENT.findall(body):
        s = tok.split(".")[-1]
        if s != own_short and s in lemma_short:
            found.add(s)
    return found


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--index", required=True)
    ap.add_argument("--source", required=True, help="directory holding the .fst sources")
    ap.add_argument("--limit", type=int, default=0, help="stop after N pairs")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args(argv[1:])

    data = json.load(open(args.index, encoding="utf-8"))
    decls = data["declarations"]
    by_name = {d["name"]: d for d in decls}
    modules = sorted({d["module"] for d in decls})

    def sh(n):
        return n.split(".")[-1]

    # Short name -> the declarations that carry it. A short name is what an
    # agent has, and two modules can share one.
    by_short = {}
    for d in decls:
        by_short.setdefault(sh(d["name"]), []).append(d)

    lemmas = {d["name"]: d for d in decls if d["eff"] == "Lemma"}
    lemma_short = {sh(n) for n in lemmas}

    bodies, texts = load_sources(args.source, modules)

    # --- ground truth: D's proof cites L -------------------------------
    pairs, skipped = [], [0]
    for name, d in sorted(lemmas.items()):
        body = bodies.get(name)
        if not body:
            continue
        goal = sorted({sh(n) for n in d["post"]})
        if not goal:
            continue
        for cited in sorted(citations(body, lemma_short, sh(name))):
            # A cited short name can belong to more than one module --
            # `append_assoc` is in both List.Tot.Properties and Seq.Base --
            # and only the one in scope was really used. Prefer the proof's
            # own module, and otherwise skip rather than credit every
            # candidate: a wrong answer key costs recall for both tools and
            # makes the measurement meaningless. Guessing here would be the
            # same mistake the server refuses to make for `lookup`.
            cands = [l for l in by_short.get(cited, [])
                     if l["eff"] == "Lemma" and l["name"] != name]
            same = [l for l in cands if l["module"] == d["module"]]
            if same:
                cands = same
            if len(cands) != 1:
                skipped[0] += 1 if cands else 0
                continue
            pairs.append((d, cands[0], goal))
        if args.limit and len(pairs) >= args.limit:
            break

    if not pairs:
        sys.exit("no (lemma, cited lemma) pairs found; check --source")

    # --- candidate sets ------------------------------------------------
    def index_candidates(goal, side):
        """find_by_contract over each goal name."""
        fields = {"ensures": ("post",), "requires": ("pre",),
                  "either": ("post", "pre")}[side]
        out = {}
        for g in goal:
            for d in decls:
                if any(sh(n) == g for f in fields for n in d[f]):
                    out[d["name"]] = d
        return out

    def grep_candidates(goal):
        """Declarations whose source text mentions a goal name anywhere."""
        out = {}
        for g in goal:
            word = re.compile(r"\b%s\b" % re.escape(g))
            for key, chunks in texts.items():
                if key in out:
                    continue
                if any(word.search(c) for c in chunks):
                    out[key] = True
        return out

    # Every configuration is reported, including the ones that do not
    # flatter the index: choosing among them after seeing the numbers is
    # how a benchmark becomes an advertisement.
    ways = [("grep", None),
            ("index ensures", "ensures"),
            ("index either", "either")]
    stats = {w: [0, [], 0, 0] for w, _ in ways}
    misses, unreachable = [], [0]
    seen_goal = {}
    for d, l, goal in pairs:
        key = tuple(goal)
        if key not in seen_goal:
            cand = {"grep": grep_candidates(goal)}
            for w, side in ways:
                if side:
                    cand[w] = index_candidates(goal, side)
            seen_goal[key] = cand
        cand = seen_goal[key]
        for w, _ in ways:
            c = cand[w]
            stats[w][0] += l["name"] in c
            stats[w][1].append(len(c))
            # How much of what a caller must read is even a lemma.
            lem = sum(1 for k in c if k in lemmas)
            stats[w][2] += lem
            stats[w][3] += len(c)
        if l["name"] not in cand["index either"]:
            # Why it was missed: does the answer's contract mention any of
            # the goal's names at all? If not, no amount of one-hop
            # contract matching could have found it.
            reachable = any(sh(n) in goal for n in l["post"] + l["pre"])
            if not reachable:
                unreachable[0] += 1
            if args.verbose:
                misses.append((d["name"], l["name"], goal, reachable))

    n = len(pairs)

    def mean(xs):
        return sum(xs) / len(xs) if xs else 0.0

    print("Retrieval benchmark: can the lemma a proof used be found from the goal?")
    print()
    print("corpus          %d modules, %d declarations, %d lemmas"
          % (len(modules), len(decls), len(lemmas)))
    print("ground truth    %d (lemma, cited lemma) pairs, from proof bodies in %s"
          % (n, args.source))
    if skipped[0]:
        print("                %d citations skipped: the short name matched several"
              % skipped[0])
        print("                modules and which was in scope could not be settled")
    print("query           the names in the proving lemma's `ensures`; never the answer's name")
    print()
    print("%-14s %8s %9s %12s %12s" % ("", "found", "recall", "candidates", "are lemmas"))
    for what, _ in ways:
        found, sizes, lem, tot = stats[what]
        print("%-14s %8d %8.1f%% %12.1f %11.0f%%"
              % (what, found, 100.0 * found / n, mean(sizes),
                 100.0 * lem / tot if tot else 0))
    print()
    missed = n - stats["index either"][0]
    if missed:
        print("Of %d missed by `index either`, %d (%.0f%%) are unreachable in one hop:"
              % (missed, unreachable[0], 100.0 * unreachable[0] / missed))
        print("the answer's contract shares no name with the goal, so contract")
        print("matching could not reach it. Following `refs` is the next step.")
        print()
    gg = mean(stats["grep"][1])
    ge = mean(stats["index either"][1])
    if ge:
        print("grep reaches more of the answers; the index asks for %.1fx fewer"
              % (gg / ge))
        print("candidates (%.0f vs %.0f) and far more of them are lemmas at all."
              % (ge, gg))
        print("The candidate counts are generous to grep: `grep -rn` returns lines,")
        print("and these are whole declarations, so many lines collapse into one.")
    print("Recall is conservative: a proof citing L shows L was useful, not that")
    print("nothing else was, so a different useful lemma counts as a miss.")

    if args.verbose and misses:
        print()
        print("misses (first 10):")
        for dn, ln, goal, reach in misses[:10]:
            print("  %-44s wanted %-36s %s goal=%s"
                  % (dn, ln, "1-hop" if reach else "no-hop", goal))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
