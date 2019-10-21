#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import re
import os
import sys
import codecs
import argparse
from collections import namedtuple

try:
    from typing import Iterable, Tuple, Match, Any, TypeVar
    T = TypeVar("T")
except ImportError:
    pass

# Utilities
# ---------

def wrap_stream(stream, wrapper):
    return wrapper("utf-8")(stream) if sys.version_info.major == 2 else stream

FST_DIRECTIVE_RE = re.compile("^ *.. fst::")
INDENTATION_RE = re.compile("^ *")

def measure_indent(line): # type: (str,) -> int
    return INDENTATION_RE.match(line).end()

Line = namedtuple('Line', 'raw marker_pos clean')

def empty(line):
    return line.clean == ""

def mkLine(raw, marker): # type: (str, str) -> Line
    if marker:
        return Line(raw, raw.find(marker), raw.replace(marker, "", 1))
    else:
        return Line(raw, -1, raw)

def strip_prefix(line, marker, prefix_len): # type: (Line, str, int) -> str
    if line.marker_pos >= 0 and line.marker_pos < prefix_len:
        return marker + line.raw[prefix_len + len(marker):]
    else:
        return line.raw[prefix_len:]

# reStructuredText → F*
# ---------------------

def rst2fst(rawlines, marker): # type: (Iterable[str], str) -> Iterable[str]
    idx, lines = 0, [mkLine(raw.rstrip(), marker) for raw in rawlines]

    # Each iteration processes a sequence of text + optional header + code
    first_round = True
    while idx < len(lines):
        output = [] # type: List[Tuple[Line, str]]
        fst_directive = None # type: Match[str]
        prev_indentation, indentation = None, None # type: Tuple[int, int]

        # Skip until start of code block
        while idx < len(lines):
            line = lines[idx]
            if not empty(line):
                prev_indentation = indentation
                indentation = measure_indent(line.clean)
            fst_directive = FST_DIRECTIVE_RE.match(line.clean)
            if fst_directive:
                break
            output.append((line, "///" + (" " + line.raw if line.raw else "")))
            idx += 1

        if idx >= len(lines):
            for _, o in output:
                yield o
            break

        # Skip until actual code
        dropped_lines = []
        has_direct_opts = fst_directive.end() < len(lines[idx].clean)
        has_further_opts = idx + 1 < len(lines) and not empty(lines[idx + 1])
        is_top_of_file = first_round and prev_indentation is None
        has_distinct_indentation = indentation != prev_indentation and not is_top_of_file
        keep_header = has_direct_opts or has_further_opts or has_distinct_indentation
        while idx < len(lines):
            line = lines[idx]
            if empty(line):
                break
            if keep_header:
                output.append((line, "/// " + line.raw))
            elif line.marker_pos >= 0:
                dropped_lines.append(marker)
            idx += 1

        # Get rid of extra empty lines
        while output and empty(output[-1][0]):
            dropped_lines.append(output.pop()[0].raw)
        while idx < len(lines):
            line = lines[idx]
            if not empty(line):
                break
            dropped_lines.append(line.raw)
            idx += 1
        dropped_markers = "".join(dropped_lines)

        # Stream partial results
        for _, o in output:
            yield o

        # Dump markers found in dropped lines (whitespace and ‘.. fst::’)
        if not is_top_of_file:
            yield dropped_markers
            dropped_markers = ""

        # Dump actual code, dedented
        code_block_offset = indentation + 3
        while idx < len(lines):
            line = lines[idx]
            indentation = measure_indent(line.clean)
            if indentation < code_block_offset and not empty(line):
                break
            yield dropped_markers + strip_prefix(line, marker, code_block_offset)
            dropped_markers = ""
            idx += 1

        if dropped_markers:
            yield dropped_markers
        first_round = False

# F* → reStructuredText
# ---------------------

RST_LINE_MARKER_RE = re.compile("^///( |$)")
F2R_LITERATE_COMMENT, F2R_FST_DIRECTIVE, F2R_CODE = range(3)

def fst2rst_classify(line, is_rst): # type: (Line, bool) -> int
    if is_rst:
        if FST_DIRECTIVE_RE.match(line.clean):
            return F2R_FST_DIRECTIVE
        return F2R_LITERATE_COMMENT
    return F2R_CODE

def fst2rst_annotate(raw, marker): # type: (str, str) -> Tuple[int, Line]
    line = mkLine(raw.rstrip(), marker)
    rst_prefix = RST_LINE_MARKER_RE.match(line.clean)
    if rst_prefix:
        clean = line.clean[rst_prefix.end():]
        raw = strip_prefix(line, marker, rst_prefix.end())
        line = Line(raw, line.marker_pos, clean)
    kind = fst2rst_classify(line, bool(rst_prefix))
    return kind, line

def fst2rst_linums(rawlines, marker): # type: Iterable[str] -> Iterable[Tuple[int, str]]
    if not rawlines:
        return

    idx = 0
    kinds, lines = zip(*(fst2rst_annotate(raw, marker) for raw in rawlines))

    # Each iteration processes a sequence of text + optional header + code
    while idx < len(lines):
        rst_indentation = 0
        existing_header_indentation = None # type: int

        # Uncomment literate comments
        while idx < len(lines):
            kind, line = kinds[idx], lines[idx]
            if kind == F2R_CODE:
                break
            indentation = measure_indent(line.clean)
            if kind == F2R_FST_DIRECTIVE:
                existing_header_indentation = indentation
            if not empty(line):
                rst_indentation = indentation
            yield idx, line.raw
            idx += 1

        # Skip blank lines
        while idx < len(lines) and empty(lines[idx]):
            yield idx, lines[idx].raw
            idx += 1

        if idx >= len(lines):
            break

        # Was this an empty code section?
        if kinds[idx] != F2R_CODE:
            continue

        # Emit code header
        prev_line_empty = idx == 0 or empty(lines[idx - 1])
        if existing_header_indentation is None:
            if not prev_line_empty:
                yield idx, "" # Empty line before ‘.. fst::’
            yield idx, " " * rst_indentation + ".. fst::"
            prev_line_empty = False
            existing_header_indentation = rst_indentation
        if not empty(lines[idx]) and not prev_line_empty:
            yield idx, "" # Empty line after ‘.. fst::’

        # Emit actual code
        while idx < len(lines):
            kind, line = kinds[idx], lines[idx]
            if kind != F2R_CODE:
                break
            indent = "" if empty(line) else " " * (3 + existing_header_indentation)
            yield idx, indent + line.raw
            idx += 1

        if not empty(lines[idx - 1]):
            yield idx - 1, "" # Empty line after the code block

def fst2rst(rawlines, markers): # type: Iterable[str] -> Iterable[str]
    for _, line in fst2rst_linums(rawlines, markers):
        yield line

# Command-line interface
# ----------------------

def parse_args():
    parser = argparse.ArgumentParser(description="Convert a literate F* file to reStructuredText, and vice-versa.")
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--fst2rst", dest="fn",
                       action="store_const", const=fst2rst,
                       help="Convert from F* to reStructuredText.")
    group.add_argument("--rst2fst", dest="fn",
                       action="store_const", const=rst2fst,
                       help="Convert from reStructuredText to F*.")
    parser.add_argument("--marker",
                        help="Special string to ignore while analyzing INPUT.")
    parser.add_argument("input", nargs="?", default="-")

    args = parser.parse_args()
    if args.input == "-":
        if not args.fn:
            parser.error("Reading from standard input requires one of --fst2rst, --rst2fst.")
    else:
        _, ext = os.path.splitext(args.input)
        args.fn = {".fst": fst2rst, ".rst": rst2fst}.get(ext)
        if not args.fn:
            parser.error("Unexpected file extension: "
                         "expected '.rst' or '.fst', got '{}'.".format(ext))

    return args

def writeout(lines):
    stdout = wrap_stream(sys.stdout, codecs.getwriter)
    for line in lines:
        stdout.write(line)
        stdout.write("\n")

def run(translator, fname, marker):
    if fname == "-":
        writeout(translator(wrap_stream(sys.stdin, codecs.getreader), marker))
    else:
        with codecs.open(fname, encoding="utf-8") as fstream:
            writeout(translator(fstream, marker))

def main():
    args = parse_args()
    run(args.fn, args.input, args.marker)

if __name__ == '__main__':
    main()
