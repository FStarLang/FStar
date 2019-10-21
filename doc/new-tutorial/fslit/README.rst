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

``.. fst::`` A block of F* code.
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

``.. exercise::`` An exercise.
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

``.. solution::`` A solution to an exercise.
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

``.. exercise-code::`` An exercise-specific snippet of code.
    This directive must appear within the body of an ``.. exercise::`` node.  It
    behaves like ``.. code``, but unlike ``.. code::`` blocks its contents are
    included in files generated by the ``:save-as:`` option.

    For example::

       .. exercise:: Big-step interpretation

          Define a big-step interpreter for STLC as a recursive function ``eval``.
          Here is a template:

          .. exercise-code::

             let rec eval x = _

``.. fixme-authors::`` A list of author aliases used in ``.. fixme ::`` directives.
    For example::

       .. fixme-authors::

          CN Chuck Norris
          AH Alyssa P. Hacker

       .. fixme:: CN

          Clarify this part

``.. fixme::`` A note indicating a problem with the surrounding code or text.
    Takes one argument: the name of the note's author.  Name abbreviations can
    be declared using the `.. fixme-authors::` annotation.

    For example::

       .. fixme:: CN

          Clarify this part

``.. tag-all::`` A utility to tag subsequent ``fst`` blocks at the current indentation level.
    Accepts one argument: a space-separate list of tags.  These tags are applied
    to all ``fst`` blocks descended from this directive parent and appearing
    after this directive.

    For example::

       .. exercise:: Pairs

          .. tag-all:: pairs

          We add the following definitions:

          .. fst::

             ...

Roles
-----

``:type:`` An inline role to highlight F* types.

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
