#!/usr/bin/env python3
"""Section 121.5.  Every `Section N(.M)*' cited from src/custard resolves.

The Custard sources carry around nine hundred citations into
doc/ref/custard.md, and they are load-bearing: the doc is where a decision is
written down and the citation is the only link from the code to it.  A
citation that does not resolve is therefore not a typo, it is a dead end --
and there is no way to notice one by reading, because the number looks just
as plausible as any other.

Round 4 found exactly one (`Section 18.4', cited twice, where the material
had gone into 19.2 and 19.3).  One in nine hundred is a good rate to hold, so
it is held here rather than by discipline.

What counts as a heading is a Markdown ATX heading whose text begins with a
number: `## 19. What the retest found', `### 19.2 An empty classification...'.
A citation resolves if its number is a heading, or an ancestor of one: the
doc numbers several sections only at the subsection level (`## 66.0', `##
66.1', with no bare `## 66'), and `section 66' is then a citation of the
group and not a mistake.  A number that is neither -- `18.4', where the doc
stops at 18.3 -- is what this rejects, which is exactly the case round 4
found.
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DOC = os.path.join(HERE, "..", "..", "doc", "ref", "custard.md")
SRC = os.path.join(HERE, "..", "..", "src", "custard")

# `## 19.' or `### 19.2 ' -- the trailing dot of a top-level heading is not
# part of the number.
HEADING = re.compile(r"^#+\s+(\d+(?:\.\d+)*)\.?\s")
# `Section 19.2', `section 19.2', `sections 19.2 and ...' -- and not a
# trailing sentence dot: `section 19.' cites 19, not 19-dot-nothing.
CITATION = re.compile(r"\b[Ss]ections?\s+(\d+(?:\.\d+)*?)(?=\D|$)")


def main() -> int:
    if not os.path.isfile(DOC):
        print("checkrefs: no %s, skipping" % DOC)
        return 0

    headings = set()
    with open(DOC, encoding="utf-8") as f:
        for line in f:
            m = HEADING.match(line)
            if m:
                parts = m.group(1).split(".")
                for i in range(1, len(parts) + 1):
                    headings.add(".".join(parts[:i]))

    if not headings:
        print("checkrefs: no numbered headings found in %s, skipping" % DOC)
        return 0

    bad = {}
    total = 0
    for name in sorted(os.listdir(SRC)):
        if not (name.endswith(".fst") or name.endswith(".fsti")):
            continue
        path = os.path.join(SRC, name)
        with open(path, encoding="utf-8") as f:
            for lineno, line in enumerate(f, 1):
                for m in CITATION.finditer(line):
                    n = m.group(1)
                    total += 1
                    if n not in headings:
                        bad.setdefault(n, []).append("%s:%d" % (name, lineno))

    if bad:
        print("ERROR: %d section reference(s) in src/custard do not resolve"
              " against doc/ref/custard.md:" % len(bad))
        for n in sorted(bad, key=lambda s: [int(p) for p in s.split(".")]):
            print("  Section %s, cited from %s" % (n, ", ".join(bad[n])))
        print("A citation is the only link from the code to the decision it")
        print("records, so one that does not resolve is a dead end.  Either")
        print("the number is wrong, or the section was never written.")
        return 1

    print("checkrefs: %d section references, all resolved" % total)
    return 0


if __name__ == "__main__":
    sys.exit(main())
