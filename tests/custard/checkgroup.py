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
"""

import sys

# A parenthesis that is part of C's *syntax* rather than a grouping: an
# argument list, a parameter list, a cast's type.  `f((x))` is one argument
# that happens to be a group, not two pairs.  The keywords are the ones whose
# own parentheses do enclose an expression, so those are checked.
CHECKED_KEYWORDS = frozenset(['if', 'while', 'switch', 'return', 'do'])
IDENT = frozenset('abcdefghijklmnopqrstuvwxyz'
                  'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_$')

def is_syntactic(text, at):
    j = at - 1
    while j >= 0 and text[j] in ' \t\n':
        j -= 1
    if j < 0:
        return False
    if text[j] in ')]':
        return True
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
    for open_at, close_at in pairs.items():
        if is_syntactic(text, open_at):
            continue
        inner = text[open_at + 1:close_at].strip()
        if not inner.startswith('(') or not inner.endswith(')'):
            continue
        # The leading paren has to be the one the trailing paren closes:
        # `(a) && (b)` also starts and ends with one and is not a group.
        first = open_at + 1 + text[open_at + 1:close_at].index('(')
        if pairs.get(first) is not None and text[pairs[first] + 1:close_at].strip() == '':
            yield open_at, close_at

def main(argv):
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
