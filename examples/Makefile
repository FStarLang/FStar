OTHERFLAGS+=--warn_error -321-274
all: prep verify special_cases

# krml_tests only to be run conditionally, if we have a karamel install.
# These tests also require that krmllib is already checked.

# Note:
#
# * old: examples that are not maintained anymore, though may be worth recovering
#
# * hello: the main point of the hello example is to test extraction and build
#   things in OCaml and F#. So, we handle that separately.
#
# * native_tactics: called explicitly by the uexamples rule from
#	the Makefile in ../src/Makefile and need special rules to build the plugins
#   for them to run. Also, these examples are excluded since the binary package
#   can't verify them.
#
# * kv_parsing: Needs Krml to build
#
# * miniparse: Needs Krml to build


EXCLUDE_DIRS=old/ hello/ native_tactics/ kv_parsing/ miniparse/ sample_project/

# F* contrib directory needed by crypto/ . Since this Makefile
# supersedes crypto/Makefile, we need to determine the location of the
# F* contrib directory here.
ifdef FSTAR_HOME
FSTAR_UCONTRIB = $(shell if test -d $(FSTAR_HOME)/ucontrib ; then echo $(FSTAR_HOME)/ucontrib ; else echo $(FSTAR_HOME)/share/fstar/contrib ; fi)
else
   # FSTAR_HOME not defined, assume fstar.exe installed through opam
   # or binary package, and reachable from PATH
FSTAR_UCONTRIB=$(dir $(shell which fstar.exe))/../share/fstar/contrib
endif

INCLUDE_PATHS?= \
	$(filter-out $(EXCLUDE_DIRS),$(shell ls -d */)) \
	$(FSTAR_UCONTRIB)/CoreCrypto/fst \
	$(FSTAR_UCONTRIB)/Platform/fst \
	$(shell ls -d dsls/*/) \
	$(shell ls -d verifythis/*/) \
	tactics/eci19

include Makefile.common

# Remove ModifiesGen since it "leaks" into this dependency analysis.
verify: prep $(filter-out $(CACHE_DIR)/Launch.fst.checked $(CACHE_DIR)/FStar.ModifiesGen.fst.checked, $(ALL_CHECKED_FILES))

HAS_OCAML := $(shell which ocamlfind 2>/dev/null)

SPECIAL_CASES += sample_project
ifneq (,$(HAS_OCAML))
SPECIAL_CASES += hello
SPECIAL_CASES += native_tactics
endif

KRML_TESTS += demos
KRML_TESTS += kv_parsing
KRML_TESTS += miniparse

special_cases: $(addsuffix .all, $(SPECIAL_CASES))

krml_tests: $(addsuffix .all, $(KRML_TESTS))

%.all: %
	+$(MAKE) -C $^ all

prep:
	mkdir -p $(OUTPUT_DIRECTORY) $(CACHE_DIR)

FILTER_OUT = $(foreach v,$(2),$(if $(findstring $(1),$(v)),,$(v)))

wc:
	wc -l $(call FILTER_OUT,ulib, $(ALL_FST_FILES) $(ALL_FSTI_FILES))

clean: $(addsuffix .clean, $(SPECIAL_CASES))
	rm -rf $(OUTPUT_DIRECTORY) $(CACHE_DIR) .depend

%.clean: %
	+$(MAKE) -C $^ clean

.PHONY: prep clean special_cases wc

