OTHERFLAGS+=--already_cached 'Prims FStar LowStar Steel NMST MST NMSTTotal MSTTotal' --compat_pre_core true
FSTAR_FILES = $(wildcard *.fst) 

all: verify-all

$(CACHE_DIR):
	mkdir -p $@

include ../Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))
