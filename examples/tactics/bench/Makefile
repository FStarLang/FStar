FSTAR_HOME=../../..
INCLUDE_PATHS=..
KREMLIN_HOME?=$(FSTAR_HOME)/../Kremlin
INCLUDE_PATHS=$(KREMLIN_HOME)/kremlib ..
EXCLUDED_FSTAR_FILES=PolyStub.fst

POLYS=$(foreach FACTOR,1 2 3,\
      $(foreach SE, 0 1,\
      $(foreach ED, 0 1,\
      $(foreach MODE, None Canon CanonNative,\
       Bench.Poly.$(MODE).Factor$(FACTOR).Seed$(SE)$(ED).fst ))))

.depend: $(POLYS)

FSTAR_FILES = $(filter-out $(EXCLUDED_FSTAR_FILES), $(POLYS) $(wildcard *.fst))

all: verify-all

# Guido: this is a hack, obviously. Just having it here causes evaluation
# of the command. (yes, GNU make is super dangerous)
x: $(shell rm -f _cache/Bench.*.fst.checked)

../CanonCommSemiring.cmxs:
	$(MAKE) -C .. canon-native

$(CACHE_DIR):
	mkdir -p $@

include ../../Makefile.common

Bench.%.fst: ./makepoly.sh PolyStub.fst
	./makepoly.sh $@

CanonCommSemiring.cmxs: ../CanonCommSemiring.cmxs
	ln -sf $< $@

_cache/Bench.%.fst.checked: Bench.%.fst CanonCommSemiring.cmxs
	$(FSTAR) --cache_off --odir _output --cache_dir _cache $< --load CanonCommSemiring --include ..

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))
