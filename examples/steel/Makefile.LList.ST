.PHONY: verify clean

FSTAR_HOME ?= $(realpath $(dir $(shell which fstar.exe))/..)
KREMLIN_HOME ?= $(FSTAR_HOME)/../kremlin

# List the files that should be verified by verify-core and verify-all
# Those files are the roots from where all dependencies are computed
FSTAR_FILES = LList.ST.UInt32.fsti LList.ST.UInt32.fst

# 271: theory symbols in smt patters
WARN_ERROR=--warn_error -271
SMT_OPTIONS=--z3cliopt 'timeout=600000' --z3cliopt 'smt.arith.nl=false' \
            --smtencoding.elim_box true \
            --smtencoding.l_arith_repr native \
            --smtencoding.nl_arith_repr wrapped
OTHERFLAGS+=$(WARN_ERROR) $(SMT_OPTIONS)
ALREADY_CACHED_LIST ?= Prims,FStar,Steel
ALREADY_CACHED = --already_cached $(ALREADY_CACHED_LIST)

# A place to put all the emitted .ml files
OUTPUT_DIRECTORY ?= _output
CACHE_DIRECTORY ?= _cache

INCLUDE_PATHS+=$(OUTPUT_DIRECTORY) $(SRC_DIRS)

FSTAR_OPTIONS=--odir $(OUTPUT_DIRECTORY) \
		 $(OTHERFLAGS) \
		 --cache_dir $(CACHE_DIRECTORY) \
	         $(addprefix --include , $(INCLUDE_PATHS)) \
		 --cache_checked_modules \
		 --cmi

FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_OPTIONS) $(ALREADY_CACHED)

.depend:
	mkdir -p $(CACHE_DIRECTORY)
	$(FSTAR) $(FSTAR_DEP_OPTIONS) --dep full $(notdir $(FSTAR_FILES)) > .depend.aux
	mv .depend.aux .depend

depend: .depend

include .depend

# a.fst(i).checked is the binary, checked version of a.fst(i)
$(CACHE_DIRECTORY)/%.checked:
	$(FSTAR) $<
	touch -c $@

$(OUTPUT_DIRECTORY)/%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<)))
	touch -c $@

verify: $(ALL_CHECKED_FILES)

STEEL_KRML_FILES=

extract: $(addprefix $(OUTPUT_DIRECTORY)/,$(STEEL_KRML_FILES)) $(filter-out $(OUTPUT_DIRECTORY)/FStar_NMST% $(OUTPUT_DIRECTORY)/FStar_MST% $(OUTPUT_DIRECTORY)/Steel_%, $(ALL_KRML_FILES))

KRML_BUNDLING_OPTIONS=-bundle 'LList.ST.UInt32=LList.ST.*,Prims,FStar.*,Steel.*' -dast \
  -no-prefix LList.ST.UInt32 \

compile:
	$(KREMLIN_HOME)/krml -warn-error +9 -skip-compilation \
		$(KRML_BUNDLING_OPTIONS) \
		$(OUTPUT_DIRECTORY)/*.krml \
		-tmpdir=$(OUTPUT_DIRECTORY)
