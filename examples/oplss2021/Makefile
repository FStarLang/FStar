.PHONY: verify clean

# List the files that should be verified by verify-core and verify-all
# Those files are the roots from where all dependencies are computed
FSTAR_FILES ?= $(wildcard *.fst)

# 271: theory symbols in smt patters
WARN_ERROR=--warn_error -271
SMT_OPTIONS=--z3cliopt 'timeout=600000' \
	    --smtencoding.elim_box true \
	    --smtencoding.l_arith_repr native \
	    --smtencoding.nl_arith_repr wrapped
ALREADY_CACHED=--already_cached 'Prims FStar LowStar Steel'
OTHERFLAGS+=$(WARN_ERROR) $(SMT_OPTIONS) $(ALREADY_CACHED)

OUTPUT_DIRECTORY = _output

CACHE_DIR = $(OUTPUT_DIRECTORY)

INCLUDE_PATHS+=$(OUTPUT_DIRECTORY)

FSTAR_OPTIONS=--odir $(OUTPUT_DIRECTORY) \
		 $(OTHERFLAGS) \
		 --cache_dir $(CACHE_DIRECTORY) \
		 $(addprefix --include , $(INCLUDE_PATHS)) \

all: verify-all

include ../Makefile.common


verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

$(CACHE_DIR):
	mkdir -p $(CACHE_DIR)

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)
