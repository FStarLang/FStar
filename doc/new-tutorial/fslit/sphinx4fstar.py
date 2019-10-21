# -*- coding: utf-8 -*-

from sphinx.domains import Domain
from sphinx.util.osutil import relative_uri
from . import docutils4fstar

# Export here so config files can refer to just this module
LiterateFStarParser = docutils4fstar.LiterateFStarParser

# Sphinx domain
# =============

class FStarDomain(Domain):
    """A domain to document F* code.

    Sphinx has a notion of “domains”, used to tailor it to a specific language.
    Domains mostly consist in descriptions of the objects that we wish to
    describe, as well as domain-specific roles and directives.

    Each domain is responsible for tracking its objects, and resolving
    references to them.
    """

    name = 'fstar'
    label = 'F*'

    object_types = dict() # ObjType (= directive type) → (Local name, *xref-roles)

    directives = dict() # Directive → Object

    roles = dict()

    indices = []

    data_version = 1
    initial_data = {
        # Collect everything under a key that we control, since Sphinx adds
        # others, such as “version”
        'objects' : {}
    }

# Event handlers
# ==============

def process_external_editor_references(app, doctree, fromdocname):
    """Adjust links to the external editor.
    In HTML mode, set the refuri appropriately; in other modes, remove them."""
    for node in doctree.traverse(docutils4fstar.standalone_editor_reference_node):
        if app.builder.name == "html":
            node['refuri'] = relative_uri(app.builder.get_target_uri(fromdocname), node['docpath'])
        else:
            node.parent.remove(node)

def process_fixmes(app, doctree, _fromdocname):
    """Keep or remove FIXME nodes (depending on the ``fslit_include_fixme`` setting."""
    if not app.config.fslit_include_fixme:
        docutils4fstar.strip_fixmes(doctree)

def process_rst(app, doctree, _fromdocname):
    """Process an RST with extra nodes"""
    pass

# Setup
# =====

def register_fst_parser(app):
    app.add_source_parser(LiterateFStarParser)
    app.add_source_suffix('.fst', 'fst')
    app.add_source_suffix('.fsti', 'fsti')

def add_html_assets(app):
    if app.builder.name == "html":
        app.config.html_static_path.append(docutils4fstar.ASSETS_PATH)

        app.add_javascript("https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.36.0/codemirror.min.js")
        app.add_stylesheet("https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.36.0/codemirror.min.css")

        app.add_javascript("fstar.cm.js")
        app.add_stylesheet("cm.tango.css")

        app.add_javascript("fslit.js")
        app.add_stylesheet("fslit.css")

        app.add_javascript("https://cdnjs.cloudflare.com/ajax/libs/ace/1.4.6/ace.js")
        app.add_javascript("https://cdnjs.cloudflare.com/ajax/libs/ace/1.4.6/ext-static_highlight.js")
        app.add_javascript("mode-fstar.js")
        app.add_javascript("theme-github.js")
        app.add_javascript("tl.js")

def setup(app):
    """Register the F* domain"""

    app.add_domain(FStarDomain)
    app.add_config_value('fslit_include_fixme', True, 'html')

    for role in docutils4fstar.ROLES:
        app.add_role(role.role, role)

    for node in docutils4fstar.NODES:
        app.add_node(node,
                     html=(node.visit, node.depart),
                     latex=(node.visit, node.depart),
                     text=(node.visit, node.depart))

    for directive in docutils4fstar.DIRECTIVES:
        getattr(directive, "setup", lambda _: None)(app.srcdir)
        app.add_directive(directive.directive, directive)

    for transform in docutils4fstar.TRANSFORMS:
        app.add_transform(transform)

    app.connect('builder-inited', add_html_assets)
    app.connect('builder-inited', register_fst_parser)
    app.connect('doctree-resolved', process_rst)
    app.connect('doctree-resolved', process_external_editor_references)
    app.connect('doctree-resolved', process_fixmes)

    return {'version': '0.1', "parallel_read_safe": True}
