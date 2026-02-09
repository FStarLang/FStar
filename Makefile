export FSTAR_ROOT=$(CURDIR)
# ^ This variable is only used by internal makefiles.
# Do NOT rely on it in client code. It is not what FSTAR_HOME was.
include mk/common.mk

# NOTE: If you are changing any of install rules, run a macos build too.
# The behavior of cp, find, etc, can differ in subtle ways from that of GNU tools.

FSTAR_DEFAULT_GOAL ?= build
.DEFAULT_GOAL := $(FSTAR_DEFAULT_GOAL)

all: stage1 stage2 1.tests 2.tests stage3-bare lib-fsharp
all-packages: package-1 package-2 package-src-1 package-src-2

### STAGES

# For developers: you can set this variable externally, pointing
# to a local build of stage0, to avoid recompiling it every time.
ifneq ($(FSTAR_EXTERNAL_STAGE0),)
FSTAR0_EXE := $(abspath $(FSTAR_EXTERNAL_STAGE0))
_ != mkdir -p stage0/out/bin
_ != ln -Tsf $(FSTAR0_EXE) stage0/out/bin/fstar.exe
# ^ Setting this link allows VS code to work seamlessly.
endif

FSTAR0_EXE ?= stage0/out/bin/fstar.exe

# This is hardcoding some dune paths, with internal (non-public) names.
# This is motivated by dune installing packages as a unit, so I could not
# install simply the bare compiler and then use it to build the full compiler
# without splitting into many packages, which complicates the namespaces.
#
# Also, when we want to extract src/ for stage 2, we must call FSTAR1_FULL_EXE,
# but it's in a bad location (without a library next to it). So, we must
# pass FSTAR_LIB explicitly. This is the only case where this is needed, the rest
# of stages don't need a library. The alternative is to install it, and use
# $(INSTALLED_FSTAR1_FULL_EXE), but that introduces a spurious dependency to the
# stage 1 libraries for the stage 2, which does not need them at all (currently?).
#
# I'd love a better alternative.
FSTAR1_BARE_EXE           := stage1/dune/_build/default/fstarc-bare/fstarc1_bare.exe
FSTAR1_FULL_EXE           := stage1/dune/_build/default/fstarc-full/fstarc1_full.exe
INSTALLED_FSTAR1_FULL_EXE := stage1/out/bin/fstar.exe
FSTAR2_BARE_EXE           := stage2/dune/_build/default/fstarc-bare/fstarc2_bare.exe
FSTAR2_FULL_EXE           := stage2/dune/_build/default/fstarc-full/fstarc2_full.exe
INSTALLED_FSTAR2_FULL_EXE := stage2/out/bin/fstar.exe
TESTS1_EXE                := stage1/dune/_build/default/tests/fstarc1_tests.exe
TESTS2_EXE                := stage2/dune/_build/default/tests/fstarc2_tests.exe

.PHONY: .force
.force:

# Pass FORCE=1 to make this makefile less smart, and trigger more
# rebuilds. Useful if you suspect the logic is wrong.
ifdef FORCE
MAYBEFORCE=.force
else
MAYBEFORCE=
endif

build: 2

0: $(FSTAR0_EXE)
1.bare:  $(FSTAR1_BARE_EXE)
1.tests: $(TESTS1_EXE)
1.full:  $(FSTAR1_FULL_EXE)
2.bare:  $(FSTAR2_BARE_EXE)
2.tests: $(TESTS2_EXE)
2.full:  $(FSTAR2_FULL_EXE)

# This file's timestamp is updated whenever anything in stage0/
# (excluding some build directories)
# changes, forcing rebuilds downstream. Note that deleting a file
# will bump the directories timestamp, we also catch that.
# This is copied from generic.mk.
.stage0.touch: .force
	mkdir -p $(dir $@)
	[ -e $@ ] || touch $@
	# I would like to *not* have -type f below, but dune
	# will create and delete lock files, which bumps
	# the timestamp of directories, and we would keep triggering
	# rebuilds.
	find stage0/ \
	  \( -path stage0/dune/_build -prune -exec false \; \) -o \
	  \( -path stage0/out -prune -exec false \; \) -o \
	  -type f -newer $@ -exec touch $@ \; -quit

stage0/out/bin/fstar.exe: .stage0.touch
	$(call bold_msg, "STAGE 0")
	mkdir -p stage0/ulib/.cache # prevent warnings
	$(MAKE) -C stage0 minimal # build: only fstar.exe and set-up lib sources
	$(MAKE) -C stage0 trim # We don't need OCaml build files.

.bare1.src.touch: $(FSTAR0_EXE) .force
	$(call bold_msg, "EXTRACT", "STAGE 1 FSTARC-BARE")
	env \
	  SRC=src/ \
	  FSTAR_EXE=$(FSTAR0_EXE) \
	  CACHE_DIR=stage1/fstarc.checked/ \
	  OUTPUT_DIR=stage1/fstarc.ml/ \
	  CODEGEN=OCaml \
	  TAG=fstarc \
	  TOUCH=$@ \
	  $(MAKE) -f mk/fstar-01.mk ocaml

.tests1.src.touch: .bare1.src.touch $(FSTAR0_EXE) .force
	$(call bold_msg, "EXTRACT", "STAGE 1 TESTS")
	env \
	  SRC=src/ \
	  FSTAR_EXE=$(FSTAR0_EXE) \
	  CACHE_DIR=stage1/tests.checked/ \
	  OUTPUT_DIR=stage1/tests.ml/ \
	  CODEGEN=PluginNoLib \
	  TAG=fstarc \
	  TOUCH=$@ \
	  $(MAKE) -f mk/tests-1.mk ocaml

# These files are regenerated as soon as *any* ml file reachable from
# stage*/dune changes. This makes sure we trigger dune rebuilds when we
# modify base ML files. However this will not catch deletion of a file.
.src.ml.touch: .force
	[ -e $@ ] || touch $@
	find -L src/ml -newer $@ -exec touch $@ \; -quit

$(FSTAR1_BARE_EXE): .bare1.src.touch .src.ml.touch $(MAYBEFORCE)
	$(call bold_msg, "BUILD", "STAGE 1 FSTARC-BARE")
	$(MAKE) -C stage1 fstarc-bare
	touch -c $@

$(TESTS1_EXE): .tests1.src.touch .src.ml.touch $(MAYBEFORCE)
	$(call bold_msg, "BUILD", "STAGE 1 TESTS")
	$(MAKE) -C stage1 tests BUILD_FSTAR_OCAML_TESTS=true
	touch -c $@

stage1-unit-tests: $(TESTS1_EXE)
	FSTAR_LIB=$(CURDIR)/ulib $(TESTS1_EXE)

.full1.src.touch: $(FSTAR1_BARE_EXE) .force
	$(call bold_msg, "EXTRACT", "STAGE 1 PLUGINS")
	env \
	  SRC=ulib/ \
	  FSTAR_EXE=$(FSTAR1_BARE_EXE) \
	  CACHE_DIR=stage1/plugins.checked/ \
	  OUTPUT_DIR=stage1/plugins.ml/ \
	  CODEGEN=PluginNoLib \
	  TAG=plugins \
	  TOUCH=$@ \
	  $(MAKE) -f mk/plugins.mk ocaml

$(FSTAR1_FULL_EXE): .bare1.src.touch .full1.src.touch .src.ml.touch $(MAYBEFORCE)
	$(call bold_msg, "BUILD", "STAGE 1 FSTARC")
	$(MAKE) -C stage1 fstarc-full
	touch -c $@

.alib1.src.touch: $(FSTAR1_FULL_EXE) .force
	$(call bold_msg, "EXTRACT", "STAGE 1 LIB")
	+env \
	  SRC=ulib/ \
	  FSTAR_EXE=$(FSTAR1_FULL_EXE) \
	  CACHE_DIR=stage1/ulib.checked/ \
	  OUTPUT_DIR=stage1/ulib.ml/ \
	  CODEGEN=OCaml \
	  TAG=lib \
	  TOUCH=$@ \
	  $(MAKE) -f mk/lib.mk ocaml verify
	# ^ NB: also verify files we don't extract

.alib1.touch: .alib1.src.touch .src.ml.touch $(MAYBEFORCE)
	$(call bold_msg, "BUILD", "STAGE 1 LIB")
	$(MAKE) -C stage1/ libapp
	touch $@

.plib1.src.touch: $(FSTAR1_FULL_EXE) .alib1.src.touch .force
	# NB: shares .depend and checked from alib1.src,
	# hence the dependency, though it is not quite precise.
	$(call bold_msg, "EXTRACT", "STAGE 1 PLUGLIB")
	env \
	  SRC=ulib/ \
	  FSTAR_EXE=$(FSTAR1_FULL_EXE) \
	  CACHE_DIR=stage1/ulib.checked/ \
	  OUTPUT_DIR=stage1/ulib.pluginml/ \
	  CODEGEN=PluginNoLib \
	  TAG=pluginlib \
	  DEPFLAGS='--extract +FStar.Tactics,+FStar.Reflection,+FStar.Sealed,-FStar.SizeT,-FStar.PtrDiffT' \
	  TOUCH=$@ \
	  $(MAKE) -f mk/lib.mk ocaml
	  # NOTE: not extracting SizeT/PtrDiff in stage 1 as that is currently broken but
	  # to requiring some staging (it uses FStar.UInt64.ne, which is not there
	  # in the parent compiler). Remove after bumping stage0.

.plib1.touch: .plib1.src.touch .src.ml.touch $(MAYBEFORCE)
	$(call bold_msg, "BUILD", "STAGE 1 PLUGLIB")
	$(MAKE) -C stage1/ libplugin
	touch $@

.bare2.src.touch: $(FSTAR1_FULL_EXE) .force
	$(call bold_msg, "EXTRACT", "STAGE 2 FSTARC")
	# NOTE: see the explanation for FSTAR_LIB near top of file.
	env \
	  SRC=src/ \
	  FSTAR_LIB=$(abspath ulib) \
	  FSTAR_EXE=$(FSTAR1_FULL_EXE) \
	  CACHE_DIR=stage2/fstarc.checked/ \
	  OUTPUT_DIR=stage2/fstarc.ml/ \
	  CODEGEN=OCaml \
	  TAG=fstarc \
	  TOUCH=$@ \
	  $(MAKE) -f mk/fstar-12.mk ocaml

.tests2.src.touch: .bare2.src.touch $(FSTAR1_FULL_EXE) .force
	$(call bold_msg, "EXTRACT", "STAGE 2 TESTS")
	env \
	  SRC=src/ \
	  FSTAR_EXE=$(FSTAR1_FULL_EXE) \
	  FSTAR_LIB=$(abspath ulib) \
	  CACHE_DIR=stage2/tests.checked/ \
	  OUTPUT_DIR=stage2/tests.ml/ \
	  CODEGEN=PluginNoLib \
	  TAG=fstarc \
	  TOUCH=$@ \
	  $(MAKE) -f mk/tests-2.mk ocaml

$(FSTAR2_BARE_EXE): .bare2.src.touch .src.ml.touch $(MAYBEFORCE)
	$(call bold_msg, "BUILD", "STAGE 2 FSTARC-BARE")
	$(MAKE) -C stage2 fstarc-bare FSTAR_DUNE_RELEASE=1
	touch -c $@
	# ^ Note, even if we don't release fstar-bare itself,
	# it is still part of the build of the full fstar, so
	# we set the release flag to have a more incremental build.

$(TESTS2_EXE): .tests2.src.touch .src.ml.touch $(MAYBEFORCE)
	$(call bold_msg, "BUILD", "STAGE 2 TESTS")
	$(MAKE) -C stage2 tests BUILD_FSTAR_OCAML_TESTS=true
	touch -c $@

stage2-unit-tests: $(TESTS2_EXE)
	FSTAR_LIB=$(CURDIR)/ulib $(TESTS2_EXE)

.full2.src.touch: $(FSTAR2_BARE_EXE) .force
	$(call bold_msg, "EXTRACT", "STAGE 2 PLUGINS")
	env \
	  SRC=ulib/ \
	  FSTAR_EXE=$(FSTAR2_BARE_EXE) \
	  CACHE_DIR=stage2/plugins.checked/ \
	  OUTPUT_DIR=stage2/plugins.ml/ \
	  CODEGEN=PluginNoLib \
	  TAG=plugins \
	  TOUCH=$@ \
	  $(MAKE) -f mk/plugins.mk ocaml

$(FSTAR2_FULL_EXE): .bare2.src.touch .full2.src.touch .src.ml.touch $(MAYBEFORCE)
	$(call bold_msg, "BUILD", "STAGE 2 FSTARC")
	$(MAKE) -C stage2 fstarc-full FSTAR_DUNE_RELEASE=1
	touch -c $@

.alib2.src.touch: $(FSTAR2_FULL_EXE) .force
	$(call bold_msg, "EXTRACT", "STAGE 2 LIB")
	env \
	  SRC=ulib/ \
	  FSTAR_EXE=$(FSTAR2_FULL_EXE) \
	  CACHE_DIR=stage2/ulib.checked/ \
	  OUTPUT_DIR=stage2/ulib.ml/ \
	  CODEGEN=OCaml \
	  TAG=lib \
	  TOUCH=$@ \
	  $(MAKE) -f mk/lib.mk ocaml verify
	# ^ NB: also verify files we don't extract


test_ulib: $(FSTAR2_FULL_EXE) .force
	env \
	  SRC=ulib/ \
	  FSTAR_EXE=$(FSTAR2_FULL_EXE) \
	  CACHE_DIR=test_ulib/ulib.checked/ \
	  OUTPUT_DIR=test_ulib/ulib.ml/ \
	  CODEGEN=OCaml \
	  TAG=lib \
	  $(MAKE) -f mk/lib.mk ocaml verify

	# ^ NB: also verify files we don't extract
.alib2.touch: .alib2.src.touch .src.ml.touch $(MAYBEFORCE)
	$(call bold_msg, "BUILD", "STAGE 2 LIB")
	$(MAKE) -C stage2/ libapp FSTAR_DUNE_RELEASE=1
	touch $@

.plib2.src.touch: $(FSTAR2_FULL_EXE) .alib2.src.touch .force
	# NB: shares .depend and checked from .alib2.src,
	# hence the dependency, though it is not quite precise.
	$(call bold_msg, "EXTRACT", "STAGE 2 PLUGLIB")
	env \
	  SRC=ulib/ \
	  FSTAR_EXE=$(FSTAR2_FULL_EXE) \
	  CACHE_DIR=stage2/ulib.checked/ \
	  OUTPUT_DIR=stage2/ulib.pluginml/ \
	  CODEGEN=PluginNoLib \
	  TAG=pluginlib \
	  DEPFLAGS='--extract +FStar.Tactics,+FStar.Reflection,+FStar.Sealed' \
	  TOUCH=$@ \
	  $(MAKE) -f mk/lib.mk ocaml

.plib2.touch: .plib2.src.touch .src.ml.touch $(MAYBEFORCE)
	$(call bold_msg, "BUILD", "STAGE 2 PLUGLIB")
	$(MAKE) -C stage2/ libplugin FSTAR_DUNE_RELEASE=1
	touch $@

# F# library, from stage 2.
lib-fsharp.src: $(FSTAR2_FULL_EXE) .alib2.src.touch .force
	# NB: shares checked files from .alib2.src,
	# hence the dependency, though it is not quite precise.
	$(call bold_msg, "EXTRACT", "FSHARP LIB")
	# Note: FStar.Map and FStar.Set are special-cased
	env \
	  SRC=ulib/ \
	  FSTAR_EXE=$(FSTAR2_FULL_EXE) \
	  CACHE_DIR=stage2/ulib.checked/ \
	  OUTPUT_DIR=fsharp/extracted/ \
	  CODEGEN=FSharp \
	  TAG=fsharplib \
	  DEPFLAGS='--extract -FStar.Map,-FStar.Set' \
	  $(MAKE) -f mk/lib.mk all-fs

.PHONY: lib-fsharp
lib-fsharp: lib-fsharp.src
	$(MAKE) -C fsharp/VS all

# Stage 3 is different, we don't build it, we just check that the
# extracted OCaml files coincide exactly with stage2. We also do not
# extract the plugins, as is stage2/fstarc and stage3/fstarc coincide,
# then they are exactly the same compiler and will extract the plugins
# in the same way.

stage3-bare: $(FSTAR2_FULL_EXE) .force
	$(call bold_msg, "EXTRACT", "STAGE 3 FSTARC")
	# NOTE: see the explanation for FSTAR_LIB near top of file.
	env \
	  SRC=src/ \
	  FSTAR_EXE=$(FSTAR2_FULL_EXE) \
	  FSTAR_LIB=$(abspath ulib) \
	  CACHE_DIR=stage3/fstarc.checked/ \
	  OUTPUT_DIR=stage3/fstarc.ml/ \
	  CODEGEN=OCaml \
	  TAG=fstarc \
	  $(MAKE) -f mk/fstar-12.mk ocaml

stage3-diff: stage3-bare .force
	$(call bold_msg, "DIFF", "STAGE 2 vs STAGE 3")
	@# Ignore ramon files, if any
	diff -r -x '*.ramon' stage2/fstarc.ml stage3/fstarc.ml

ifeq ($(shell uname),Linux)
LINK_OK=1
else
LINK_OK=0
endif

.stage1.src.touch: .bare1.src.touch .full1.src.touch .alib1.src.touch .plib1.src.touch .src.ml.touch
	touch $@

.stage2.src.touch: .bare2.src.touch .full2.src.touch .alib2.src.touch .plib2.src.touch .src.ml.touch
	touch $@

.install-stage1.touch: export FSTAR_LINK_LIBDIRS=$(LINK_OK)
.install-stage1.touch: .stage1.src.touch $(MAYBEFORCE)
	$(call bold_msg, "INSTALL", "STAGE 1")
	$(MAKE) -C stage1 install PREFIX=$(CURDIR)/stage1/out
	@# ^ pass PREFIX to make sure we don't get it from env
	touch $@

.install-stage2.touch: export FSTAR_LINK_LIBDIRS=$(LINK_OK)
.install-stage2.touch: .stage2.src.touch $(MAYBEFORCE)
	$(call bold_msg, "INSTALL", "STAGE 2")
	$(MAKE) -C stage2 install PREFIX=$(CURDIR)/stage2/out FSTAR_DUNE_RELEASE=1
	@# ^ pass PREFIX to make sure we don't get it from env
	touch $@

setlink-%:
	if [ -e out ] && ! [ -h out ]; then echo "ERROR: out/ exists and is not a symbolic link, please remove it"; false; fi
	rm -f out && ln -sf $(CURDIR)/stage$*/out out
	# For compatibility with the previous layout
	mkdir -p bin
	ln -sf $(CURDIR)/out/bin/fstar.exe bin/fstar.exe
	ln -sf $(CURDIR)/.scripts/get_fstar_z3.sh bin/get_fstar_z3.sh

stage1: .install-stage1.touch
.PHONY: 1
1: stage1
	$(MAKE) setlink-1

stage2: .install-stage2.touch
.PHONY: 2
2: stage2
	$(MAKE) setlink-2

3: stage3-diff

install: export PREFIX?=/usr/local
install: export FSTAR_LINK_LIBDIRS=0 # default is false, but set anyway
install:
	$(call bold_msg, "INSTALL", "STAGE 2")
	$(MAKE) -C stage2 install FSTAR_DUNE_RELEASE=1

__do-install-stage1:
	$(call bold_msg, "INSTALL", "STAGE 1")
	$(MAKE) -C stage1 install
__do-install-stage2:
	$(call bold_msg, "INSTALL", "STAGE 2")
	$(MAKE) -C stage2 install FSTAR_DUNE_RELEASE=1

__do-archive: .force
	rm -rf $(PKGTMP)
	# add an 'fstar' top-level directory to the archive
	$(MAKE) $(INSTALL_RULE) PREFIX="$(abspath $(PKGTMP)/fstar)"
	$(call bold_msg, "PACKAGE", $(ARCHIVE))
	.scripts/bin-install.sh "$(PKGTMP)/fstar"
	.scripts/mk-package.sh "$(PKGTMP)" "$(ARCHIVE)"
	rm -rf $(PKGTMP)

__do-src-archive: .force
	rm -rf $(PKGTMP) # change the name, this is safe (its overriden) but scary
	$(call bold_msg, "SRC PACKAGE", $(ARCHIVE))
	.scripts/src-install.sh "$(BROOT)" "$(PKGTMP)/fstar"
	.scripts/mk-package.sh "$(PKGTMP)" "$(ARCHIVE)"
	rm -rf $(PKGTMP)

# We append the version to the package names, unless
# FSTAR_TAG is set (possibly empty)
FSTAR_TAG ?= -v$(shell cat version.txt)

package-1: .stage1.src.touch .force
	env \
	  PKGTMP=_pak1 \
	  BROOT=stage1/ \
	  ARCHIVE=fstar$(FSTAR_TAG)-stage1 \
	  INSTALL_RULE=__do-install-stage1 \
	  $(MAKE) __do-archive

package-2: .stage2.src.touch .force
	env \
	  PKGTMP=_pak2 \
	  BROOT=stage2/ \
	  ARCHIVE=fstar$(FSTAR_TAG) \
	  INSTALL_RULE=__do-install-stage2 \
	  $(MAKE) __do-archive

package-src-1: .stage1.src.touch .tests1.src.touch .force
	env \
	  PKGTMP=_srcpak1 \
	  BROOT=stage1/ \
	  ARCHIVE=fstar$(FSTAR_TAG)-stage1-src \
	  $(MAKE) __do-src-archive

package-src-2: .stage2.src.touch .tests2.src.touch .force
	env \
	  PKGTMP=_srcpak2 \
	  BROOT=stage2/ \
	  ARCHIVE=fstar$(FSTAR_TAG)-src \
	  $(MAKE) __do-src-archive

package: package-2
package-src: package-src-2

test-1-bare: override FSTAR_EXE := $(abspath $(FSTAR1_BARE_EXE))
test-1-bare: override FSTAR_LIB := $(abspath ulib)
test-1-bare: $(FSTAR1_BARE_EXE)
	$(MAKE) -C bare-tests

test-2-bare: override FSTAR_EXE := $(abspath $(FSTAR2_BARE_EXE))
test-2-bare: override FSTAR_LIB := $(abspath ulib)
test-2-bare: $(FSTAR2_BARE_EXE)
	$(MAKE) -C bare-tests

test: test-2

test-1: override FSTAR_EXE := $(abspath stage1/out/bin/fstar.exe)
test-1: stage1
	$(MAKE) _test FSTAR_EXE=$(FSTAR_EXE)

_unit-tests-1: override FSTAR_EXE := $(abspath stage1/out/bin/fstar.exe)
_unit-tests-1: stage1
	$(MAKE) _unit-tests FSTAR_EXE=$(FSTAR_EXE)

test-2: override FSTAR_EXE := $(abspath stage2/out/bin/fstar.exe)
test-2: stage2
	$(MAKE) _test FSTAR_EXE=$(FSTAR_EXE)

unit-tests: override FSTAR_EXE := $(abspath stage2/out/bin/fstar.exe)
unit-tests: _unit-tests

# Use directly only at your own risk.
_test: FSTAR_EXE ?= $(abspath out/bin/fstar.exe)
_test: _unit-tests _examples _doc

need_fstar_exe:
	if [ -z "$(FSTAR_EXE)" ]; then \
		echo "This rule needs FSTAR_EXE defined."; \
		false; \
	fi

_doc: _doc_book_code _doc_old_tutorial

_doc_book_code: need_fstar_exe .force
	+$(MAKE) -C doc/book/code FSTAR_EXE=$(FSTAR_EXE)

_doc_old_tutorial: need_fstar_exe .force
	+$(MAKE) -C doc/old/tutorial regressions FSTAR_EXE=$(FSTAR_EXE)

_unit-tests: need_fstar_exe .force
	+$(MAKE) -C tests all FSTAR_EXE=$(FSTAR_EXE)

_examples: need_fstar_exe .force
	+$(MAKE) -C examples all FSTAR_EXE=$(FSTAR_EXE)

ci: .force
	+$(MAKE) 2
	+$(MAKE) test lib-fsharp stage3-diff test-2-bare stage2-unit-tests

save: stage0_new

stage0_new: TO=stage0_new
stage0_new: .stage2.src.touch
	$(call bold_msg, "SNAPSHOT", "$(TO)")
	rm -rf "$(TO)"
	.scripts/src-install.sh "stage2" "$(TO)"
	# Trim it a bit...
	rm -rf "$(TO)/src"            # no need for compiler F* sources
	rm -rf "$(TO)/ulib/.hints"    # this library won't be checked
	rm -rf "$(TO)/ulib.pluginml"  # we won't build plugins against stage0
	rm -rf "$(TO)/dune/libplugin" # idem
	rm -rf "$(TO)/dune/libapp"    # we won't even build apps
	rm -rf "$(TO)/dune/tests"     # we won't build tests

bump-stage0: stage0_new
	$(call bold_msg, "BUMP!")
	# Replace stage0
	rm -rf stage0
	mv stage0_new stage0
	echo 'out' >> stage0/.gitignore
	echo '** -diff -merge linguist-generated=true' >> stage0/.gitattributes
	# Now that stage0 supports all features, we can return to a clean state
	# where the 01 makefile is equal to the 12 makefile. Same for stage1
	# support and config code, we just take it from the stage2.
	rm -f mk/generic-0.mk
	ln -sf generic-1.mk mk/generic-0.mk
	cp mk/fstar-12.mk mk/fstar-01.mk
	sed -i 's,include mk/generic-1.mk,include mk/generic-0.mk,' mk/fstar-01.mk
	rm -rf stage1
	cp -r stage2 stage1
	rm -f stage1/dune/fstar-guts/app
	ln -Trsf stage0/ulib/ml/app stage1/dune/fstar-guts/app

# This rule brings a stage0 from an OLD fstar repo. Only useful for migrating.
bring-stage0: .force
	if [ -z "$(FROM)" ]; then echo "FROM not set" >&2; false; fi
	rm -rf stage0
	mkdir stage0
	cp -r $(FROM)/ocaml -T stage0
	ln -Tsrf mk/stage0.mk stage0/Makefile
	cp -r $(FROM)/ulib -T stage0/ulib
	find stage0/ulib -name '*.checked' -delete
	find stage0/ulib -name '*.hints' -delete
	echo '/lib' >> stage0/.gitignore
	echo '** -diff -merge' >> stage0/.gitattributes
	echo '** linguist-generated=true' >> stage0/.gitattributes

watch:
	while true; do \
	  $(MAKE) ;\
	  inotifywait -qre close_write,moved_to .; \
	done


### CLEAN

clean-depend: .force
	rm -f stage1/fstarc.checked/.*depend*
	rm -f stage1/plugins.checked/.*depend*
	rm -f stage1/ulib.checked/.*depend*
	rm -f stage2/fstarc.checked/.*depend*
	rm -f stage2/plugins.checked/.*depend*
	rm -f stage2/ulib.checked/.*depend*

clean-0: .force
	$(call bold_msg, "CLEAN", "STAGE 0")
	$(MAKE) -C stage0 clean
	rm -rf stage0/ulib/.cache # created only to prevent warnings, always empty

clean-1: .force
	$(call bold_msg, "CLEAN", "STAGE 1")
	$(MAKE) -C stage1 clean
	rm -rf stage1/fstarc.checked
	rm -rf stage1/fstarc.ml
	rm -rf stage1/plugins.checked
	rm -rf stage1/plugins.ml
	rm -rf stage1/ulib.checked
	rm -rf stage1/ulib.ml
	rm -rf stage1/ulib.pluginml

clean-2: .force
	$(call bold_msg, "CLEAN", "STAGE 2")
	$(MAKE) -C stage2 clean
	rm -rf stage2/fstarc.checked
	rm -rf stage2/fstarc.ml
	rm -rf stage2/plugins.checked
	rm -rf stage2/plugins.ml
	rm -rf stage2/ulib.checked
	rm -rf stage2/ulib.ml
	rm -rf stage2/ulib.pluginml

clean-3: .force
	$(call bold_msg, "CLEAN", "STAGE 3")
	rm -rf stage3/

trim: clean-0 clean-1 clean-2 clean-3

clean: trim
	$(call bold_msg, "CLEAN", "out/")
	# ah.. this is just a symlink, recursive calls above should just trim
	rm -rf out

distclean: clean
	$(call bold_msg, "DISTCLEAN")
	rm -rf _new
	rm -rf _build
	rm -f fstar.tar.gz
	rm -f fstar-*.tar.gz

help:
	echo "Main rules:"
	echo "  build              build the compiler and libraries, and install it in out/"
	echo "  test               run internal tests and examples (implies build)"
	echo "  package            build a binary package"
	echo "  package-src        build an OCaml source package"
	echo "  clean              clean everything except built packages"
	echo "  install            install F* into your system (by default to /usr/local, set PREFIX to change this)"
	echo
	echo "Optional arguments:"
	echo "  V=1                enable verbose build"
	echo "  ADMIT=1            skip verification (pass '--admit_smt_queries true')"
	echo
	echo "Rules for F* hackers:"
	echo "  all                build everything that can be built, also extract stage 3"
	echo "  0                  build the stage0 compiler (in stage0/)"
	echo "  stage1             build a full stage 1 compiler and libraries"
	echo "  1                  stage1 + set the out/ symlink"
	echo "  stage2             build a full stage 2 compiler and libraries"
	echo "  2 (= build)        stage2 + set the out/ symlink"
	echo "  package-1          create a binary tar.gz for the stage 1 build"
	echo "  package-2          create a binary tar.gz for the stage 2 build (= package)"
	echo "  package-src-1      create an OCaml source distribution for the stage 1 build"
	echo "  package-src-2      create an OCaml source distribution for the stage 2 build (= package-src)"
	echo "  all-packages       build the four previous rules"
	echo "  clean-depend       remove all .depend files, useful when files change name"
	echo "  trim               clean some buildfiles, but retain any installed F* in out"
	echo "  distclean          remove every generated file"
	echo "  unit-tests         run the smaller unit test suite (implied by test)"
	echo "  save               copy a trimmed stage2 into stage0_new (essentially snapshotting a package-src-2)"
	echo "  bump-stage0        like save, but replace existing stage0 and reset to a default state"
	echo
	echo "You can set a different default goal by defining FSTAR_DEFAULT_GOAL in your environment."
