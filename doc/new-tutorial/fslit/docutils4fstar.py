#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# pylint: disable=too-few-public-methods,too-many-ancestors

from __future__ import unicode_literals

import re
import os
import itertools
import fnmatch
import sys
import codecs

import docutils
from docutils import nodes, DataError
from docutils.transforms import Transform
from docutils.parsers.rst import Directive, directives, roles
from docutils.parsers.rst.directives import admonitions
from docutils.readers.standalone import Reader

from .translate import fst2rst_linums

# Constants
# =========

SCRIPT_PATH = os.path.dirname(os.path.realpath(__file__))
ASSETS_PATH = os.path.join(SCRIPT_PATH, "assets")

# Utilities
# =========

def wrap_stream(stream, wrapper):
    return wrapper("utf-8")(stream) if sys.version_info.major == 2 else stream

INDENTATION_RE = re.compile("^ *")
def measure_indentation(line):
    return INDENTATION_RE.match(line).end()

def recompute_contents(directive, real_indentation):
    block_lines = directive.block_text.splitlines()
    block_header_len = directive.content_offset - directive.lineno + 1
    block_indentation = measure_indentation(directive.block_text)
    code_indentation = block_indentation + real_indentation
    lines = [ln[code_indentation:] for ln in block_lines[block_header_len:]]
    return lines

def parents(node):
    current = node.parent
    while current is not None:
        yield current
        current = current.parent

def find_parent(node, parent_class):
    return next((parent for parent in parents(node) if isinstance(parent, parent_class)), None)

def assert_attached_to(node, parent_class):
    if find_parent(node, parent_class) is None:
        raise DataError("'{}' blocks must appear in '{}' blocks."
                        .format(node.__class__.__name__, parent_class.__name__))

def set_source_info(directive, node):
    node.source, node.line = directive.state_machine.get_source_and_line(directive.lineno)

def mkdir(absdir):
    try:
        os.makedirs(absdir)
    except OSError:
        if not os.path.isdir(absdir):
            raise

def skip_blanks(iterator):
    while True:
        line = next(iterator)
        if line != "":
            return line

def join_blocks(blocks):
    for block in blocks:
        yield ""
        for line in block:
            yield line

# Directives
# ==========

# .. fixme
# --------

class Env(object):
    pass

def getenv(directive):
    return directive.state.document.settings.ensure_value('env', Env())

class FixmeAuthorsDirective(Directive):
    """A list of author aliases used in ``.. fixme ::`` directives.

    For example::

       .. fixme-authors::

          CN Chuck Norris
          AH Alyssa P. Hacker

       .. fixme:: CN

          Clarify this part
    """
    directive = "fixme-authors"

    has_content = True
    required_arguments = 0
    final_argument_whitespace = False
    option_spec = {}

    def run(self):
        env = getenv(self)
        if not hasattr(env, "fixme_authors"):
            setattr(env, "fixme_authors", {})
        for line in self.content:
            nick, name = line.split(None, 1)
            env.fixme_authors[nick] = name
        return []

class FixmeDirective(admonitions.BaseAdmonition):
    """A note indicating a problem with the surrounding code or text.

    Takes one argument: the name of the note's author.  Name abbreviations can
    be declared using the `.. fixme-authors::` annotation.

    For example::

       .. fixme:: CN

          Clarify this part
    """

    directive = "fixme"
    node_class = nodes.admonition
    node_css_class = "admonition-fixme"

    has_content = True
    required_arguments = 1
    optional_arguments = 0
    final_argument_whitespace = False
    option_spec = {}

    def run(self):
        env = getenv(self)
        nicknames = getattr(env, "fixme_authors", {})
        author = nicknames.get(self.arguments[0], self.arguments[0])
        self.options["class"] = [FixmeDirective.node_css_class]
        self.arguments[0] = "FIXME ({})".format(author)
        return super(FixmeDirective, self).run()

def strip_fixmes(doctree):
    """Remove all FIXME nodes in `doctree`."""
    cls = FixmeDirective.node_css_class
    for node in doctree.traverse(docutils.nodes.admonition):
        if cls in node.attributes.get("classes", ()):
            node.parent.remove(node)

# .. exercise, .. solution
# ------------------------

class standalone_editor_reference_node(nodes.reference):
    @staticmethod
    def visit(visitor, node):
        return visitor.visit_reference(node)
    @staticmethod
    def depart(visitor, node):
        return visitor.depart_reference(node)

class Artifact(object):
    PREAMBLE_END_MARKER = [["/" * 60]]
    MODNAME_FORBIDDEN_RE = re.compile("[^A-Za-z0-9_.]")
    MODULE_LINE_RE = re.compile("^ *module [A-Za-z0-9_.]+ *$")

    def __init__(self, docname, name, subdir, preamble, own_code):
        self.modname = Artifact.clean_modname(docname) + "." + name
        self.subdir, self.preamble, self.own_code = subdir, preamble, own_code

    @property
    def filename(self):
        return self.modname + ".fst"

    @staticmethod
    def clean_modname(name):
        modname = Artifact.MODNAME_FORBIDDEN_RE.sub("", name)
        if not modname:
            raise DataError("Can't make an F* module name from '{}'".format(name))
        return modname[0].upper() + modname[1:]

    @staticmethod
    def assemble_fstar_document(blocks, modname):
        yield "module {}".format(modname)
        module_line_found = False
        lines = join_blocks(blocks)
        try:
            while True:
                line = next(lines)
                if (not module_line_found) and Artifact.MODULE_LINE_RE.match(line):
                    module_line_found = True
                    line = skip_blanks(lines)
                yield line
        except StopIteration:
            pass

    def writeout(self, outdir):
        abspath = os.path.abspath(os.path.join(outdir, self.subdir, self.filename))
        with codecs.open(abspath, mode="w", encoding="utf-8") as out:
            sep = Artifact.PREAMBLE_END_MARKER
            blocks = itertools.chain(self.preamble, sep, self.own_code)
            for line in Artifact.assemble_fstar_document(blocks, self.modname):
                out.write(line)
                out.write("\n")

    def make_link(self):
        TEXT = "→ Open in standalone editor"
        CLASS = "fstar-standalone-editor-link"
        node = standalone_editor_reference_node('', TEXT, classes=[CLASS])
        node["docpath"] = os.path.join(self.subdir, self.filename)
        return nodes.paragraph('', '', node, classes=["fstar-standalone-editor-link-box"])

class TitledBlockBaseDirective(Directive):
    required_arguments = 0
    optional_arguments = 1
    final_argument_whitespace = True
    option_spec = { "class": directives.class_option,
                    "name": directives.unchanged }
    has_content = True

    label = None
    directive = None
    node_class = nodes.container

    def run(self):
        self.assert_has_content()

        mk_class = lambda name: self.directive + "-" + name
        contents = "\n".join(self.content)

        header_nodes = [nodes.inline(text=self.label, classes=[mk_class("label")])]
        if self.arguments:
            header_nodes.append(nodes.inline(text=self.arguments[0], classes=[mk_class("title")]))

        header_node = nodes.inline('', '', *header_nodes, classes=[mk_class("header")])
        body_node = nodes.container(contents, classes=[mk_class("body")])

        container_node = self.node_class(contents, header_node, body_node)
        container_node.header = header_node
        container_node["fname"] = self.options.get("save-as", None)
        container_node["classes"] = [self.directive] + self.options.get("class", [])
        self.add_name(container_node) # target
        set_source_info(self, container_node)

        self.state.nested_parse(self.content, self.content_offset, body_node)
        return [container_node]

# .. exercise
# ~~~~~~~~~~~

class exercise_node(nodes.container):
    subdir = "exercises"
    @staticmethod
    def visit(visitor, node):
        return visitor.visit_container(node)
    @staticmethod
    def depart(visitor, node):
        return visitor.depart_container(node)

class IncludeExcludeFilter(object):
    def __init__(self, include_re, exclude_re):
        self.include_re, self.exclude_re = include_re, exclude_re

    @staticmethod
    def parse(patterns_str):
        if patterns_str:
            regexes = (fnmatch.translate(pat) for pat in patterns_str.split())
            return re.compile(r"^(" + r"|".join(regexes) + r")$")

    @staticmethod
    def from_strings(includes, excludes):
        include_re = IncludeExcludeFilter.parse(includes)
        exclude_re = IncludeExcludeFilter.parse(excludes)
        return IncludeExcludeFilter(include_re, exclude_re)

    def match_tag(self, tag):
        return self.include_re.match(tag) and (not self.exclude_re.match(tag))

    def match_node(self, node):
        # print("Applying {} to {}".format((self.include_re, self.exclude_re), node))
        # ‘*’ filters need at least one tag, so use "?" as a default
        tags = node.get("tags") or ["?"]
        keep = True
        if self.include_re:
            keep = keep and any(self.include_re.match(t) for t in tags)
        if self.exclude_re:
            keep = keep and not any(self.exclude_re.match(t) for t in tags)
        return keep

    def apply(self, nodes_collection):
        return [n for n in nodes_collection if self.match_node(n)]

class ExerciseDirective(TitledBlockBaseDirective):
    """An exercise.

    Takes one optional argument: the exercise's title.  Accepts the following
    options:

    - ``:name:`` An identifier to refer to this exercise.
    - ``:class:`` A class to apply to the corresponding output node.
    - ``:save-as:`` A file name.  Specifying this argument causes Sphinx to save
      code snippets preceding the ``exercise`` directive into a file of that name.
    - ``:include:`` A filter expression that snippets must satisfy to be included
      in files generated by ``:save-as:`` (default: include all).
    - ``:exclude:`` A filter expression that snippets must not satisfy to be
      included in files generated by ``:save-as:`` (default: reject none).

    For example::

       .. exercise:: Big-step interpretation
          :save-as: BigStep
          :exclude: pairs

          Define a big-step interpreter for STLC as a recursive function ``eval``.
    """

    option_spec = { "class": directives.class_option,
                    "name": directives.unchanged,
                    "save-as": directives.unchanged,
                    "include": directives.unchanged,
                    "exclude": directives.unchanged }

    label = "Exercise"
    directive = "exercise"
    node_class = exercise_node

    def run(self):
        [node] = super(ExerciseDirective, self).run()
        includes = self.options.get("include")
        excludes = self.options.get("exclude")
        node.filters = IncludeExcludeFilter.from_strings(includes, excludes)
        return [node]

# .. solution
# ~~~~~~~~~~~

class solution_node(nodes.container):
    subdir = "solutions"
    @staticmethod
    def visit(visitor, node):
        return visitor.visit_container(node)
    @staticmethod
    def depart(visitor, node):
        return visitor.depart_container(node)

class SolutionDirective(TitledBlockBaseDirective):
    """A solution to an exercise.

    This directive must appear within the body of an ``.. exercise::`` node.

    Takes one optional argument, the solution's title. Accepts the following
    options:

    - ``:name:`` An identifier to refer to this exercise.
    - ``:class:`` A class to apply to the corresponding output node.

    For example::

       .. exercise:: Big-step interpretation
          :save-as: BigStep
          :exclude: pairs

          Define a big-step interpreter for STLC as a recursive function ``eval``.

          .. solution::

             Here is a solution that only uses ``typed_step``:

             .. fst::

                let rec eval e =
                  if is_value e then e else eval (typed_step e)
    """
    label = "Solution"
    directive = "solution"
    node_class = solution_node

# F* listings
# -----------

class FStarListingBaseDirective(Directive):
    EXPECTED_INDENTATION = 3
    option_spec = { "class": directives.class_option,
                    "name": directives.unchanged,
                    "tags": directives.unchanged }
    has_content = True
    node_class = nodes.literal_block

    def run(self):
        self.assert_has_content()

        roles.set_classes(self.options)
        classes = ["code"] + self.options.get("classes", [])

        lines = recompute_contents(self, FStarBlockDirective.EXPECTED_INDENTATION)
        code = "\n".join(lines)

        # Sphinx highlights code when ``node.raw == node.astext()``. We don't
        # want highlighting here, so we use a dummy ``raw`` value
        node = self.node_class("<no-highlighting>", code, classes=classes)
        node["tags"] = self.options.get("tags", "").split()
        node.lines = lines

        self.add_name(node)
        set_source_info(self, node)

        return [node]

# .. tag-all
# ~~~~~~~~~~
class tag_all_node(nodes.literal_block):
    pass

class TagAllDirective(Directive):
    """A utility to tag subsequent ``fst`` blocks at the current indentation level.

    Accepts one argument: a space-separate list of tags.  These tags are applied
    to all ``fst`` blocks descended from this directive parent and appearing
    after this directive.

    For example::

       .. exercise:: Pairs

          .. tag-all:: pairs

          We add the following definitions:

          .. fst::

             ...
    """
    directive = "tag-all"
    option_spec = {}
    has_content = False
    optional_arguments = 1
    final_argument_whitespace = True

    def run(self):
        tags = self.arguments[0].split() if self.arguments else []
        node = tag_all_node('', '', tags=tags)
        return [node]

# .. fst
# ~~~~~~

class fst_node(nodes.literal_block):
    @staticmethod
    def visit(visitor, node):
        return visitor.visit_literal_block(node)
    @staticmethod
    def depart(visitor, node):
        return visitor.depart_literal_block(node)

class FStarBlockDirective(FStarListingBaseDirective):
    """A block of F* code.

    This directive is automatically inserted when translating a literate F*
    document to reStructuredText.  As such, it is not usually useful to include
    this directive explicitly when writing literate F* programs, except in two
    cases:

    - To specify custom options.
    - To specify an explicit indentation level for the following code.

    Accepts the following options:

    - ``:name:`` An identifier to refer to this code snippet.
    - ``:class:`` A class to apply to the corresponding output node.
    - ``:tags:`` A list of space-separated tags, useful for including or excluding snippets.

    For example::

       .. fst::
          :eval:

          let rec eval e =
            if is_value e then e else eval (typed_step e)
    """
    directive = "fst"
    node_class = fst_node

# .. exercise-code
# ~~~~~~~~~~~~~~~~

class exercise_code_node(nodes.literal_block):
    @staticmethod
    def visit(visitor, node):
        return visitor.visit_literal_block(node)
    @staticmethod
    def depart(visitor, node):
        return visitor.depart_literal_block(node)

class ExerciseCodeDirective(FStarListingBaseDirective):
    """An exercise-specific snippet of code.

    This directive must appear within the body of an ``.. exercise::`` node.  It
    behaves like ``.. code``, but unlike ``.. code::`` blocks its contents are
    included in files generated by the ``:save-as:`` option.

    For example::

       .. exercise:: Big-step interpretation

          Define a big-step interpreter for STLC as a recursive function ``eval``.
          Here is a template:

          .. exercise-code::

             let rec eval x = _
    """
    directive = "exercise-code"
    node_class = exercise_code_node

# Transforms
# ----------

class CheckExerciseSubNodesTransform(Transform):
    default_priority = 400

    def apply(self):
        for node in self.document.traverse(exercise_code_node):
            assert_attached_to(node, exercise_node)
        for node in self.document.traverse(solution_node):
            assert_attached_to(node, exercise_node)
        for node in self.document.traverse(standalone_editor_reference_node):
            assert_attached_to(node, exercise_node)

class ApplyTagsVisitor(nodes.GenericNodeVisitor):
    def __init__(self, document):
        nodes.GenericNodeVisitor.__init__(self, document)
        self.tags, self.tags_expiry_marker = [], None

    def visit_fst_node(self, node):
        node["tags"].extend(self.tags)

    def visit_tag_all_node(self, node):
        self.tags = node["tags"]
        self.tags_expiry_marker = node.parent

    def depart_tag_all_node(self, node): # pylint: disable=no-self-use
        node.parent.remove(node)

    def default_visit(self, _):
        pass

    def default_departure(self, node):
        if node is self.tags_expiry_marker:
            self.tags = []

class ApplyTagsTransform(Transform):
    default_priority = 401
    def apply(self):
        self.document.walkabout(ApplyTagsVisitor(self.document))

class ExerciseSnippetsVisitor(nodes.SparseNodeVisitor):
    def __init__(self, document):
        nodes.SparseNodeVisitor.__init__(self, document)
        self.code_blocks = [] # type: List[str]

    def visit_exercise_code_node(self, node):
        self.code_blocks.append(node)

    def visit_fst_node(self, node):
        self.code_blocks.append(node)

    def visit_solution_node(self, _): # pylint: disable=no-self-use
        raise nodes.StopTraversal()

# This is Sphinx-specific (because of env.docname and env.app.builder.outdir)
class BuildFStarArtifactsTransform(Transform):
    default_priority = 402

    def apply(self):
        docname = self.document.settings.env.docname
        rootdir = self.document.settings.env.app.builder.outdir

        for cls in [exercise_node, solution_node]:
            mkdir(os.path.abspath(os.path.join(rootdir, cls.subdir)))

        code_blocks = []
        for node in self.document.traverse():
            if isinstance(node, fst_node):
                code_blocks.append(node)
            elif isinstance(node, exercise_node):
                if node.get("fname"):
                    visitor = ExerciseSnippetsVisitor(self.document)
                    node.walk(visitor)
                    # Write the artifact
                    node.artifact = Artifact(
                        docname, node["fname"], node.subdir,
                        [fst.lines for fst in node.filters.apply(code_blocks)],
                        [fst.lines for fst in visitor.code_blocks])
                    node.artifact.writeout(rootdir)
                    # Add a link
                    link = node.artifact.make_link()
                    solution = next(iter(node.traverse(solution_node)), None)
                    if solution:
                        # Insert the editor link right before the solution
                        parent = solution.parent
                        index = parent.index(solution)
                        parent.insert(index, link)
                    else:
                        node.append(link)
            elif isinstance(node, solution_node):
                exercise = find_parent(node, exercise_node)
                if exercise.get("fname"):
                    node["fname"] = exercise["fname"] + ".Solution"
                    node.filters = exercise.filters
                    # Write the artifact
                    node.artifact = Artifact(
                        docname, node["fname"], node.subdir,
                        [fst.lines for fst in node.filters.apply(code_blocks)],
                        [fst.lines for fst in node.traverse(fst_node)])
                    node.artifact.writeout(rootdir)
                    # Add a link
                    node.append(node.artifact.make_link())

# :type:`…`
# ---------

def FStarTypeRole(typ, rawtext, text, lineno, inliner, options={}, content=[]):
    """An inline role to highlight F* types."""
    #pylint: disable=dangerous-default-value, unused-argument
    return nodes.literal(typ, rawtext, text, lineno, inliner, options=options, content=content)
FStarTypeRole.role = "type"

# FST parser
# ==========

class JsErrorPrinter(object):
    @staticmethod
    def json_of_message(level, message, source, line):
        js = { "level": level,
               "message": message,
               "source": source,
               "line": line }
        return js

    def __init__(self, line_translator, settings):
        import sys
        self.stream = sys.stderr
        self.line_translator = line_translator or (lambda s, l: l)
        self.report_level = settings.report_level

    def __call__(self, msg):
        import json
        message = msg.children[0].astext() if msg.children else "Unknown error"
        level, source, line = msg['level'], msg['source'], msg.get('line', 1)
        if level >= self.report_level:
            line = self.line_translator(source, line)
            level = docutils.utils.Reporter.levels[level].lower()
            js = JsErrorPrinter.json_of_message(level, message, source, line)
            json.dump(js, self.stream)
            self.stream.write('\n')

class WrappedWarningStream(object):
    """A wrapper around error streams to fix line numbers in error messages."""
    RE = re.compile(r'^(?P<source>.*?):(?P<line>[0-9]+):', re.MULTILINE)

    def __init__(self, stream, source, linemap):
        self.raw_stream = stream
        self.source = source
        self.linemap = linemap

    def rstline2fstline(self, match):
        """Adjust line numbers in `match`."""
        line, source = int(match.group('line')), match.group('source')
        if source == self.source and self.linemap and line < len(self.linemap):
            line = self.linemap[line]
        return "{}:{}:".format(source, line)

    def write(self, text):
        if hasattr(self.raw_stream, 'write'):
            self.raw_stream.write(WrappedWarningStream.RE.sub(self.rstline2fstline, text))

class LiterateFStarParser(docutils.parsers.Parser):
    """A wrapper around the reStructuredText parser for F* literate files.

    It's hard to systematically translate reStructuredText line numbers into F*
    line numbers (line numbers are pretty deeply baked into reStructuredText's
    state machine), so we just translate them in error messages.
    """

    supported = ('fst', 'fsti')
    """Aliases this parser supports."""

    settings_spec = ('Literate F* Parser Options', None,
                     docutils.parsers.rst.Parser.settings_spec[2])
    config_section = 'Literate F* parser'
    config_section_dependencies = ('parsers',)

    def __init__(self):
        self.source = None
        self.linemap = None # type: List[int]
        self.parser = docutils.parsers.rst.Parser()

    @staticmethod
    def fst2rst(fst_string):
        if fst_string == "":
            return [], ""
        linemap, rst_lines = zip(*fst2rst_linums(fst_string.splitlines(), None))
        return list(linemap), "\n".join(rst_lines)

    def rstline2fstline(self, source, line):
        """Translate an RST line number into an F* line number.

        This method only produces correct results during calls to
        ``LiterateFStarParser.parse``.
        """
        if source == self.source and self.linemap and line < len(self.linemap):
            return self.linemap[line]
        return line

    def parse(self, fst_string, document):
        """Parse `fst_string` and populate `document`, a document tree."""
        self.source = document['source']
        self.linemap, rst_string = LiterateFStarParser.fst2rst(fst_string)
        document.reporter.stream = WrappedWarningStream(document.reporter.stream, self.source, self.linemap)
        self.parser.parse(rst_string, document)
        document.reporter.stream = document.reporter.stream.raw_stream
        self.linemap, self.source = None, None

class StandaloneLiterateFStarReader(Reader):
    def __init__(self, parser=None, parser_name=None, extra_transforms=None):
        Reader.__init__(self, parser, parser_name)
        self.extra_transforms = extra_transforms or []

    def get_transforms(self):
        return Reader.get_transforms(self) + DOCUTILS_TRANSFORMS + self.extra_transforms


# Main entry point
# ================

def register():
    for role in ROLES:
        roles.register_local_role(role.role, role)
    for directive in DIRECTIVES:
        directives.register_directive(directive.directive, directive)

    # See docutils.nodes._add_node_class_names
    default_visit = lambda self, node: self.default_visit(node)
    default_departure = lambda self, node: self.default_departure(node)
    noop = lambda _self, _node: None

    for node in NODES:
        name = node.__name__
        setattr(nodes.GenericNodeVisitor, "visit_" + name, default_visit)
        setattr(nodes.GenericNodeVisitor, "depart_" + name, default_departure)
        setattr(nodes.SparseNodeVisitor, 'visit_' + name, noop)
        setattr(nodes.SparseNodeVisitor, 'depart_' + name, noop)

def add_nodes(translator_class):
    for node in NODES:
        setattr(translator_class, 'visit_' + node.__name__, node.visit)
        setattr(translator_class, 'depart_' + node.__name__, node.depart)

# Index
# =====

ROLES = [FStarTypeRole]
NODES = [exercise_node, solution_node, fst_node, exercise_code_node,
         standalone_editor_reference_node]
DIRECTIVES = [FStarBlockDirective, ExerciseDirective, SolutionDirective,
              ExerciseCodeDirective, FixmeAuthorsDirective, FixmeDirective,
              TagAllDirective]
DOCUTILS_TRANSFORMS = [CheckExerciseSubNodesTransform, ApplyTagsTransform]
SPHINX_TRANSFORMS = [BuildFStarArtifactsTransform]
TRANSFORMS = DOCUTILS_TRANSFORMS + SPHINX_TRANSFORMS
