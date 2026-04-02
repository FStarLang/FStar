# Minimal makefile for Sphinx documentation
#

export FSTAR_HOME?=$(realpath ../../everest/FStar)
export PULSE_HOME?=$(FSTAR_HOME)/../pulse

FSTARLANG_ORG_ROOT?=www

# You can set these variables from the command line.
SPHINXOPTS    =
SPHINXBUILD   = sphinx-build
SPHINXPROJ    = FStarBook
SOURCEDIR     = .
BUILDDIR      = _build

prep:
	mkdir -p code/pulse
	cp -R $(FSTAR_HOME)/doc/book/code/* code
	cp -R $(PULSE_HOME)/share/pulse/examples/by-example/* code/pulse


html: Makefile
	@$(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)
	find _build -name "*.html" | xargs sed -i 's/_static/static/g'
	rm -rf _build/html/static
	mv _build/html/_static _build/html/static

LATEXFILE=proof-orientedprogramminginf.tex

pdf:
	@$(SPHINXBUILD) -M latex "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)
	sed -i -e 's|\\chapter|\\part|g' $(BUILDDIR)/latex/$(LATEXFILE)
	sed -i -e 's|\\section|\\chapter|g' $(BUILDDIR)/latex/$(LATEXFILE)
	sed -i -e 's|\\subsection|\\section|g' $(BUILDDIR)/latex/$(LATEXFILE)
	sed -i -e 's|\\subsubsection|\\subsection|g' $(BUILDDIR)/latex/$(LATEXFILE)
	sed -i -e 's|\\sphinxhref{../code/|\\sphinxhref{https://fstar-lang.org/tutorial/book/code/|g' $(BUILDDIR)/latex/$(LATEXFILE)
	sed -i -e 's|\\part{Structure of this book}|\\begin{center}\\bigskip{\\Large \\textbf{Structure of this book}}\\bigskip\\end{center}|g' $(BUILDDIR)/latex/$(LATEXFILE)
	$(MAKE) -C $(BUILDDIR)/latex

# Put it first so that "make" without argument is like "make help".
help:
	@$(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

deploy:
	rm -rf $(FSTARLANG_ORG_ROOT)/tutorial/book/
	cp -R _build/html $(FSTARLANG_ORG_ROOT)/tutorial/book/
	cp -R code $(FSTARLANG_ORG_ROOT)/tutorial/book/
	cp _build/latex/proof-orientedprogramminginf.pdf $(FSTARLANG_ORG_ROOT)/tutorial/proof-oriented-programming-in-fstar.pdf

.PHONY: help Makefile

# Catch-all target: route all unknown targets to Sphinx using the new
# "make mode" option.  $(O) is meant as a shortcut for $(SPHINXOPTS).
%: Makefil
	@$(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)
