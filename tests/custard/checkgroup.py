#!/usr/bin/env python3
"""Section 35.2.  Report a parenthesis group whose whole content is another
group, i.e. `((X))`, anywhere in a generated C file.

Section 32.10 removed the extraneous pair that `if (` used to add around a
condition `c_expr` had already parenthesized, and the check on that fix was
that clang stopped emitting `-Wparentheses-equality`.  Round 40's reporter
showed that check is weaker than it looks: clang's warning is *shape*
sensitive, and says nothing at all when the left operand is a call.

    int t1(int a,int b){ if ((a==b)) return 1; return 0; }    /* warns  */
    int t2(void)       { if ((g()==1)) return 1; return 0; }  /* silent */

So a surviving redundant pair around a call-comparison would pass a
`-Werror` build, and `-Werror` is what the suite had.  The property itself is
not shape sensitive and does not need a compiler to check, which is what this
does: it is the same paren matcher they ran over the 198 KB `CBORDet.c`,
generalized from `if` to every position and run on every C file the suite
generates.

Comments and string and character literals are skipped, since a paren inside
one is not a paren.

Section 37.1.  A cast's closing parenthesis looks exactly like a call's, and
the group after a cast is grouping rather than syntax, so telling them apart
needs the *content* of the preceding group and not just its last character.
`--self-test` runs the distinguishing cases; it is part of the suite, because
a gate with a hole in it reads like coverage that is not there.
"""

import re
import sys

# A parenthesis that is part of C's *syntax* rather than a grouping: an
# argument list, a parameter list, a cast's type.  `f((x))` is one argument
# that happens to be a group, not two pairs.  The keywords are the ones whose
# own parentheses do enclose an expression, so those are checked.
CHECKED_KEYWORDS = frozenset(['if', 'while', 'switch', 'return', 'do'])
IDENT = frozenset('abcdefghijklmnopqrstuvwxyz'
                  'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_$')

# The content of a cast's parentheses: optional type keywords, a name, and
# any number of stars.  Anything else before a `(` that itself ends in `)` is
# a call through an expression -- `(*fp)(x)`, `(a ? f : g)(x)` -- whose
# argument list is syntax.
TYPEISH = re.compile(r"""\A(?:(?:const|volatile|unsigned|signed|struct|union
                             |enum|long|short|static|_Bool)\s+)*
                          [A-Za-z_$][A-Za-z0-9_$]*
                          (?:\s*\*)*\s*\Z""", re.X)

def is_syntactic(text, at, opens=None):
    """Is the `(` at `at` part of C's syntax rather than a grouping?"""
    j = at - 1
    while j >= 0 and text[j] in ' \t\n':
        j -= 1
    if j < 0:
        return False
    if text[j] == ']':
        return True
    if text[j] == ')':
        # Section 37.1: a cast ends in `)` too, and what follows a cast is
        # its operand.  `(size_t)((x))` has a redundant pair; `(*fp)((x))`
        # has one grouped argument.  The difference is inside the group.
        open_at = (opens or {}).get(j)
        if open_at is None:
            return True
        return not TYPEISH.match(text[open_at + 1:j])
    if text[j] not in IDENT:
        return False
    k = j
    while k >= 0 and text[k] in IDENT:
        k -= 1
    return text[k + 1:j + 1] not in CHECKED_KEYWORDS

def scan(text):
    """Yield (offset, close_offset) for every group whose content is a group."""
    stack = []
    pairs = {}
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == '/' and i + 1 < n and text[i + 1] == '*':
            j = text.find('*/', i + 2)
            i = n if j < 0 else j + 2
            continue
        if c == '/' and i + 1 < n and text[i + 1] == '/':
            j = text.find('\n', i)
            i = n if j < 0 else j + 1
            continue
        if c in '"\'':
            j = i + 1
            while j < n and text[j] != c:
                j += 2 if text[j] == '\\' else 1
            i = j + 1
            continue
        if c == '(':
            stack.append(i)
        elif c == ')':
            if stack:
                pairs[stack.pop()] = i
        i += 1
    opens = dict((close, open_at) for open_at, close in pairs.items())
    for open_at, close_at in pairs.items():
        if is_syntactic(text, open_at, opens):
            continue
        inner = text[open_at + 1:close_at].strip()
        if not inner.startswith('(') or not inner.endswith(')'):
            continue
        # The leading paren has to be the one the trailing paren closes:
        # `(a) && (b)` also starts and ends with one and is not a group.
        first = open_at + 1 + text[open_at + 1:close_at].index('(')
        if pairs.get(first) is not None and text[pairs[first] + 1:close_at].strip() == '':
            yield open_at, close_at

# Section 37.1.  The cases that distinguish a cast from a call, including the
# three real bugs round 40's fix removed -- the third of which this matcher
# used to miss, and it is the shape a recurrence would take.
SELF_TEST = [
    ('if (!((i < n))) { }', 1),
    ('void *p = malloc((((size_t)1ULL)) * n);', 1),
    ('for (size_t i = 0; i < (size_t)(((size_t)1ULL)); i++) { }', 1),
    ('int m = (int)((5));', 1),
    ('int q = ((5));', 1),
    ('int r = (*fp)((0));', 0),
    ('int r = foo((x));', 0),
    ('if ((a) && (b)) { }', 0),
    ('int r = (size_t)(x);', 0),
    ('char *s = "((x))"; /* ((y)) */', 0),
    # Section 41.2, round 42.  Every case above has the redundant group behind
    # `!`, `=`, `(` or a cast, so CHECKED_KEYWORDS was the one table nothing
    # here exercised -- emptying it hid all three of these and the self-test
    # still passed.  Which is to say: this file was a faithful regression test
    # for the bug it was written for and had no opinion about the bug the
    # matcher was written for.
    ('if ((a == b)) { }', 1),
    ('while ((a)) { }', 1),
    ('return ((a));', 1),
    # A call through an array of function pointers: `]` ends a group whose
    # contents are not a type, so the `(` after it is a call and not grouping.
    ('int r = fp[i]((0));', 0),
    # The two literal skips, each of which hides a `((` that is not code, and
    # the escape that decides where a string literal ends.
    ('int q = (x); // ((y))', 0),
    ('char *s = "\\"((x))\\"";', 0),
]

def self_test():
    bad = 0
    for text, want in SELF_TEST:
        got = len(list(scan(text)))
        if got != want:
            print('ERROR: checkgroup self-test: expected %d finding(s), got %d,'
                  ' in: %s' % (want, got, text))
            bad += 1
    return 1 if bad else 0

def main(argv):
    if '--self-test' in argv[1:]:
        return self_test()
    bad = 0
    for path in argv[1:]:
        try:
            text = open(path, encoding='utf-8', errors='replace').read()
        except OSError:
            continue
        for open_at, close_at in sorted(scan(text)):
            line = text.count('\n', 0, open_at) + 1
            snippet = text[open_at:close_at + 1]
            if len(snippet) > 70:
                snippet = snippet[:67] + '...'
            print('ERROR: %s:%d: redundant parenthesis group %s'
                  % (path, line, snippet.replace('\n', ' ')))
            bad += 1
    return 1 if bad else 0

if __name__ == '__main__':
    sys.exit(main(sys.argv))
