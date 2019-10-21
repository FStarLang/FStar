#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""Check an fslit file for syntax errors.

Use ``./lint.py --help`` to show the documentation."""

import argparse
import codecs

try:
    from docutils.parsers.rst import Parser
    from docutils.readers.standalone import Reader
    from docutils.frontend import OptionParser
    from docutils.utils import new_document
except ImportError:
    import sys
    sys.exit(0)

if __name__ == "__main__" and __package__ is None:
    from os import sys, path
    sys.path.append(path.dirname(path.dirname(path.abspath(__file__))))

from fslit import docutils4fstar

def parse_arguments():
    parser = argparse.ArgumentParser(description='Check an F* literate file for syntax errors')
    parser.add_argument('--dialect', choices=["rst", "fst-rst"], required=True,
                        help="Language of the input file (reStructuredText or literate F*).")
    parser.add_argument('--stdin-filename', default="<stdin>",
                        help="Name of the F* file (useful when passing the input on stdin.")
    parser.add_argument('filename', help="F* file to check, or '-' for stdin.")
    return parser.parse_args()

def init_parser(dialect):
    if dialect == "rst":
        return Parser(), None
    if dialect == "fst-rst":
        parser = docutils4fstar.LiterateFStarParser()
        line_translator = parser.rstline2fstline
        return parser, line_translator
    assert False

def init_settings(components):
    settings = OptionParser(components=components).get_default_values()
    settings.warning_stream = False # Disable textual reporting
    settings.syntax_highlight = 'none'
    return settings

def read_input(filename):
    if filename == "-":
        return docutils4fstar.wrap_stream(sys.stdin, codecs.getreader).read()
    else:
        with codecs.open(filename, encoding='utf-8') as f:
            return f.read()

def main():
    args = parse_arguments()
    real_filename = args.stdin_filename if args.filename == "-" else args.filename

    docutils4fstar.register()
    settings = init_settings((Parser, Reader))
    parser, line_translator = init_parser(args.dialect)
    reader = docutils4fstar.StandaloneLiterateFStarReader(parser)
    document = new_document(real_filename, settings)
    document.transformer.populate_from_components((parser, reader))
    document.reporter.attach_observer(docutils4fstar.JsErrorPrinter(line_translator, settings))

    parser.parse(read_input(args.filename), document)
    document.transformer.apply_transforms()

if __name__ == '__main__':
    main()
