#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""Rebuild README.rst from README.template.rst."""

import re
from os import sys, path

script_dir = path.dirname(path.abspath(__file__))
if __name__ == "__main__" and __package__ is None:
    sys.path.append(path.dirname(script_dir))

import fslit.docutils4fstar
from codecs import open

README_DIRECTIVES_MARKER = "[DIRECTIVES]"
README_ROLES_MARKER = "[ROLES]"

FIRST_LINE_BLANKS = re.compile("^(.*)\n *\n")
def format_docstring(template, key, obj):
    docstring = obj.__doc__.strip()
    return template.format(key, FIRST_LINE_BLANKS.sub(r"\1\n", docstring))

def regen_readme():
    roles_docs = [format_docstring("``:{}:`` {}", r.role, r)
                  for r in fslit.docutils4fstar.ROLES]
    directives_docs = [format_docstring("``.. {}::`` {}", d.directive, d)
                       for d in fslit.docutils4fstar.DIRECTIVES]
    with open(path.join(script_dir, "README.template.rst"), encoding="utf-8") as readme:
        contents = readme.read()
    with open(path.join(script_dir, "README.rst"), mode="w", encoding="utf-8") as readme:
        readme.write(contents
                     .replace(README_ROLES_MARKER, "\n\n".join(roles_docs))
                     .replace(README_DIRECTIVES_MARKER, "\n\n".join(directives_docs)))

if __name__ == '__main__':
    regen_readme()
