.PHONY: verify clean

# List the files that should be verified by verify-core and verify-all
# Those files are the roots from where all dependencies are computed
FSTAR_FILES ?= $(wildcard *.fst)

# Uncomment the definition of PROFILE below, if you want some basic
# profiling of F* runs on Veritas files It will report the time spent
# on typechecking your file And the time spent in SMT, which is
# included in the total typechecking time

OTHERFLAGS+=$(PROFILE)

# 271: theory symbols in smt patters
WARN_ERROR=--warn_error -271
SMT_OPTIONS=--z3cliopt 'timeout=600000' \
	    --smtencoding.elim_box true \
	    --smtencoding.l_arith_repr native \
	    --smtencoding.nl_arith_repr wrapped
OTHERFLAGS+=$(WARN_ERROR) $(SMT_OPTIONS)
ALREADY_CACHED=--already_cached 'Prims FStar LowStar Steel'

# A place to put all the emitted .ml files
OUTPUT_DIRECTORY ?= _output
CACHE_DIRECTORY = $(OUTPUT_DIRECTORY)

INCLUDE_PATHS+=$(OUTPUT_DIRECTORY)

FSTAR_OPTIONS=--odir $(OUTPUT_DIRECTORY) \
		 $(OTHERFLAGS) \
		 --cache_dir $(CACHE_DIRECTORY) \
		 $(addprefix --include , $(INCLUDE_PATHS)) \
		 --cache_checked_modules

FSTAR=fstar.exe $(FSTAR_OPTIONS) $(ALREADY_CACHED)

verify: $(addprefix $(CACHE_DIRECTORY)/,$(addsuffix .checked, $(notdir $(FSTAR_FILES))))

.depend: $(FSTAR_FILES)
	mkdir -p $(CACHE_DIRECTORY)
	$(FSTAR) --dep full $(notdir $^) > .depend

depend: .depend

include .depend

# a.fst(i).checked is the binary, checked version of a.fst(i)
$(CACHE_DIRECTORY)/%.checked:
	$(FSTAR) $<


%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

clean:
	rm -rf $(OUTPUT_DIRECTORY) .depend
