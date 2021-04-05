EXCLUDED_FSTAR_FILES=ParDivWP.fst Semantics.WP.fst
OTHERFLAGS+=--already_cached 'Prims FStar LowStar Steel NMST MST NMSTTotal MSTTotal'
FSTAR_FILES = $(filter-out $(EXCLUDED_FSTAR_FILES), $(wildcard *.fst))

all: verify-all

$(CACHE_DIR):
	mkdir -p $@

include ../Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))
