#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""Compile a single literate F* document to HTML."""

from __future__ import unicode_literals

import locale
from os import sys, path

from docutils.core import publish_cmdline, default_description
from docutils.writers.html4css1 import HTMLTranslator

if __name__ == "__main__" and __package__ is None:
    sys.path.append(path.dirname(path.dirname(path.abspath(__file__))))

from fslit import docutils4fstar # pylint: disable=wrong-import-position

try:
    locale.setlocale(locale.LC_ALL, '')
except locale.Error:
    pass

docutils4fstar.register()
docutils4fstar.add_nodes(HTMLTranslator)
parser = docutils4fstar.LiterateFStarParser()
reader = docutils4fstar.StandaloneLiterateFStarReader(parser)
stylesheets = [path.join(docutils4fstar.ASSETS_PATH, "fslit.css"),
               "https://cdn.rawgit.com/matthiaseisen/docutils-css/master/docutils_basic.css"]
MATHJAX_URL = "https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.0/MathJax.js?config=TeX-AMS_HTML-full"

publish_cmdline(writer_name='html',
                reader=reader, parser=parser,
                settings_overrides={'embed_stylesheet': False,
                                    'syntax_highlight': 'none',
                                    'stylesheet_path': None,
                                    'math_output': "MathJax " + MATHJAX_URL,
                                    'stylesheet': ",".join(stylesheets)},
                description='Build an HTML document from a literate F* file. ' + default_description)
