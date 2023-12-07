OTHERFLAGS+=--warn_error -321-274
all: prep verify special_cases

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


EXCLUDE_DIRS=old/ hello/ native_tactics/ kv_parsing/ miniparse/ 

INCLUDE_PATHS?= \
	$(filter-out $(EXCLUDE_DIRS),$(shell ls -d */)) \
	../ucontrib/CoreCrypto/fst \
	../ucontrib/Platform/fst \
	$(shell ls -d dsls/*/) \
	$(shell ls -d verifythis/*/) \
	$(shell ls -d demos/*/) \
	tactics/eci19
	
include Makefile.common

verify: prep $(filter-out $(CACHE_DIR)/Launch.fst.checked, $(ALL_CHECKED_FILES))

HAS_OCAML := $(shell which ocamlfind 2>/dev/null)

ifneq (,$(HAS_OCAML))
SPECIAL_CASES += hello
endif

ifdef KRML_HOME
SPECIAL_CASES += kv_parsing
SPECIAL_CASES += miniparse
endif

special_cases: $(addsuffix .all, $(SPECIAL_CASES))

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

