FSTAR_HOME=../../..
INCLUDE_PATHS=..
KREMLIN_HOME?=$(FSTAR_HOME)/../Kremlin
INCLUDE_PATHS=$(KREMLIN_HOME)/kremlib ..
EXCLUDED_FSTAR_FILES=MiniStub.fst

#Guido: Take SIZE > 1, or the the tactic may run out of goals
# (should be fixed, but who actually needs a 1-case enum verified parser?)
POLYS= $(foreach SIZE, 4 7 10,\
       $(foreach POLICY, Goal ,\
       Bench.MiniParse.Size$(SIZE).Factor1.Seed00.$(POLICY).fst ))

# $(foreach SIZE, 4 7 10,\
#       $(foreach FACTOR, 64 256 1024,\
#       $(foreach SE, 0,\
#       $(foreach ED, 0,\
#       $(foreach POLICY, SMT ,\
#        Bench.MiniParse.Size$(SIZE).Factor$(FACTOR).Seed$(SE)$(ED).$(POLICY).fst ))))) \
#        \

.depend: $(POLYS)

FSTAR_FILES = $(filter-out $(EXCLUDED_FSTAR_FILES), $(POLYS) $(wildcard *.fst))

all: verify-all

# Guido: this is a hack, obviously. Just having it here causes evaluation
# of the command. (yes, GNU make is super dangerous)
x: $(shell rm -f _cache/Bench.*.fst.checked)

$(CACHE_DIR):
	mkdir -p $@

include ../../Makefile.common

Bench.%.fst: ./makemini.sh MiniStub.fst
	./makemini.sh $@

_cache/Bench.%.fst.checked: Bench.%.fst
	$(FSTAR) --cache_off --odir _output --cache_dir _cache $< --include ..

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))
