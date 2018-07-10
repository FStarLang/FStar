FSTAR_HOME=../../..
KREMLIN_HOME?=$(FSTAR_HOME)/../Kremlin
INCLUDE_PATHS=$(KREMLIN_HOME)/kremlib ..
EXCLUDED_FSTAR_FILES=
FSTAR_FILES = $(filter-out $(EXCLUDED_FSTAR_FILES), $(wildcard *.fst))

all: verify-all

# Guido: this is a hack, obviously. Just having it here causes evaluation
# of the command. (yes, GNU make is super dangerous)
x: $(shell rm -f _cache/Poly?.fst.checked)

# For Poly4, load CanonCommSemiing
_cache/Poly4.fst.checked: ../CanonCommSemiring.cmxs
	$(FSTAR) --cache_checked_modules --odir _output --cache_dir _cache --include .. --use_extracted_interfaces true --use_hints --use_hint_hashes Poly4.fst --load CanonCommSemiring

../CanonCommSemiring.cmxs:
	$(MAKE) -C .. canon-native

$(CACHE_DIR):
	mkdir -p $@

include ../../Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))
