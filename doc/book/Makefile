# Minimal makefile for Sphinx documentation
#

export FSTAR_HOME?=$(realpath ../..)

# You can set these variables from the command line.
SPHINXOPTS    = -W
SPHINXBUILD   = sphinx-build
SPHINXPROJ    = EverParseDoc
SOURCEDIR     = .
BUILDDIR      = _build

# Put it first so that "make" without argument is like "make help".
help:
	@$(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

.PHONY: help Makefile test all 3d clean 3d-do-tests %.diff 3d-snapshot

# Catch-all target: route all unknown targets to Sphinx using the new
# "make mode" option.  $(O) is meant as a shortcut for $(SPHINXOPTS).
%: Makefile
	@$(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

3d: $(3D_DIFF)

3d-do-tests:
	mkdir -p out
	$(3D) --odir out --batch $(3D_FILES)
	cp $(AUX_HEADERS) out
	+$(MAKE) -C out -f Makefile.basic USER_TARGET=test USER_CFLAGS='-Wno-ignored-qualifiers' test

$(3D_OUT): out/%: 3d-do-tests

$(3D_SNAPSHOT): 3d-snapshot/%: out/%
	mkdir -p 3d-snapshot
	if diff -w -B $^ $@ ; then touch $@ ; else cp $^ $@ ; fi

3d-snapshot: $(3D_SNAPSHOT)

all-diffs: $(3D_DIFF)

%.diff: 3d-do-tests
	diff -w -B out/$(basename $@) 3d-snapshot/$(basename $@)

clean:
	rm -rf out _build
