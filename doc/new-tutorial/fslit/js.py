#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import docutils

from sphinx.errors import ExtensionError

MISSING_FSTARJS_MESSAGE = "Directory '{}/fstar.js/' not found. Please \
download an fstar.js build from GitHub and decompress it into your \
'_static' folder."

def ensure_fstar_js(static_path):
    """Ensure that fstar.js was downloaded."""
    for pth in static_path:
        candidate = os.path.join(pth, 'fstar.js')
        if os.path.isdir(candidate):
            return candidate
    raise ExtensionError(MISSING_FSTARJS_MESSAGE)

def setup_js_assets(app): # type: Sphinx -> ()
    if app.builder.name == "html":
        fstar_js_path = ensure_fstar_js(app.config.html_static_path)

        # The pattern below tells Sphinx to copy files in ``fstar.js/`` without
        # processing them (converting them to HTML).  It works because the
        # document finder checks absolute paths against `exclude_patterns`,
        # whereas the assets-copying code checks paths relative to ``_static/``.
        app.config.exclude_patterns.append(fstar_js_path)

        # This configures FStar.{IDE,CLI}.WORKER_DIRECTORY, sets the file name,
        # and loads the literate client.
        app.add_javascript("fslit.fstarjs-config.js")

        # Listed here are the scripts that need to be directly included in the
        # HTML (not the ones that run in web workers)
        app.add_stylesheet("fstar.js/fstar.ide.css")
        app.add_stylesheet("fstar.js/fstar.cli.css")
        app.add_javascript("fstar.js/fstar.client.js")
        # (Sphinx adds a static “_static/” prefix to all relative paths)

        # These two are used for displaying goals
        app.add_javascript("https://cdnjs.cloudflare.com/ajax/libs/mustache.js/2.3.0/mustache.js")
        app.add_javascript("https://cdnjs.cloudflare.com/ajax/libs/codemirror/5.36.0/addon/runmode/runmode.min.js")

FSTAR_JS_CODA = """\
<!-- F*.js configuration -->
<script>
__FSTAR_JS_CURRENT_FST_FILE_NAME__ = "{{{FILENAME}}}"
</script>
<!-- End of F*.js configuration -->
"""

def insert_fstarjs_script_tags(_app, doctree, fromdocname):
    js = FSTAR_JS_CODA.replace("{{{FILENAME}}}", fromdocname + ".fst")
    doctree.append(docutils.nodes.raw("", js, format="html"))

def setup(app):
    app.connect('builder-inited', setup_js_assets)
    app.connect('doctree-resolved', insert_fstarjs_script_tags)

    return {'version': '0.1', "parallel_read_safe": True}
