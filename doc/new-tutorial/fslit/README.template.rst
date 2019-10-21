======================================================================
 ``fslit``: Utilities for writing and rendering literate F\* programs
======================================================================

Setting up
==========

Install ``docutils`` and ``sphinx``::

   pip install --user docutils sphinx

… then clone this repository.

Writing literate F\* files
==========================

Literate F\* files are interleavings of F\* code and lines prefixed with ``///``
(called literate comments).  For example::

   /// Let's start with a simple program:    ← This is a literate comment

   (** Compute the average of [nums]. **)
   let avg nums =
     sum nums / List.length nums

Literate comments are written in reStructuredText (reST): the example above maps
to the following reST document::

   Let's start with a simple program:

   .. fst::

      (** Compute the average of [nums]. **)
      let avg nums =
        sum nums / List.length nums

Consult the `reStructuredText quick start guide
<https://www.sphinx-doc.org/en/stable/rest.html>`_ for general information about
reST, and the following sections for details on F\*-specific directives.

Emacs support
-------------

``fstar-mode`` displays literate comment markers as a solid line in the margin
(┃), and highlights reST syntax errors in literate comments as you type (using
``fslit``\ 's ``lint.py`` script).

Additionally, pressing ``C-c C-S-a`` (:kbd:`Ctrl` :kbd:`c`, :kbd:`Ctrl`
:kbd:`Shift` :kbd:`a`) in ``fstar-mode`` toggles between literate F\* sources
and a reST version of the same document, suitable for large reST edits (read the
documentation of ``rst-mode`` with `C-h f rst-mode` to learn about editing reST
files in Emacs, or read the `online manual
<http://docutils.sourceforge.net/docs/user/emacs.html>`_).

Compiling literate F\* files
============================

Docutils
--------

Use the ``fslit/fst2html.py`` script to render a literate F* file as a standalone HTML file.  This works well for quick experiments::

   $ fslit/fst2html.py example.fst > example.html

From Emacs, simply run `M-x fstar-literate-preview`.

Sphinx
------

For larger examples, use Sphinx (they have a good `tutorial
<http://www.sphinx-doc.org/en/stable/tutorial.html>`_). Here is how to create a
new Sphinx project::

   $ mkdir fstar-book; cd fstar-book/

   $ git clone --depth 1 https://github.com/FStarLang/fstar-mode.el
   … Checking connectivity... done.

   $ sphinx-quickstart --ext-mathjax --extensions fslit.sphinx4fstar \
       --quiet --author '<you>' --project '<proj-name>'

Open the generated ``conf.py`` file, and insert the following after the comment saying *If extensions […] are in another directory, add these directories to sys.path here.*::

   import os
   import sys
   sys.path.insert(0, os.path.abspath('fstar-mode.el/etc/'))

You can now create literate F\* documents (e.g. ``Induction.fst``,
``RecTypes.fst``) and add them to the ``.. toctree::`` directive in
``index.rst``::

   .. toctree::

      Induction
      RecTypes

Use ``make html`` to confirm that everything is working (generated files are in
``_build/html/index.html``) and ``python3 -m http.server`` to serve the website
locally (at ``http://localhost:8000/``).

F\*.js (making your literate F* documents interactive)
------------------------------------------------------

Documents built by ``fslit`` can be turned into interactive proofs using `F\*.js
<https://github.com/cpitclaudel/fstar.js>`_, a JavaScript build of F\*.  Its
README explains how to set things up manually, but ``fslit`` comes with a Sphinx
plug-in to make it easier.

With a properly configured Sphinx project, the following steps should be enough:

- Add ``"fslit.js"`` to ``extensions`` in ``conf.py``.
- Download an F\*.js release, and copy or symlink the ``fstar.js`` folder to
  your Sphinx project's ``_static`` directory.
- Rebuild your Sphinx project.

You'll need to run ``python3 -m http.server`` to browse the results: WebWorkers
can't (as of 2018-03) run from ``file://`` addresses.

Literate F\* roles and directives
=================================

Directives
----------

[DIRECTIVES]

Roles
-----

[ROLES]

Literate F\* syntax notes
=========================

By default, code blocks are placed at the same indentation level as the last
preceding text::

   /// .. note::
   ///
   ///    The following code is captured in the note:

   let a = 1

   ↓

   .. note::

      The following code is captured in the note:

      .. fst::

         let a = 1

You can avoid this using an explicit ``.. fst::`` marker::

   /// .. note::
   ///
   ///    The following code is not captured in the note.
   ///
   /// .. fst::

   let a = 1

   ↓

   .. note::

      The following code is not captured in the note.

   .. fst::

      let a = 1

This problem can be particularly confusing with ``.. code::`` directives::

   /// .. code:: c
   ///
   ///    int main() {}

   let a = 1

   ↓ This is probably not what you want

   .. code:: c

      int main() {}

      .. fst::

         let a = 1
