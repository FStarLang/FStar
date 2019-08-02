FSTAR_HOME=../..
OTHERFLAGS+= \
--z3cliopt smt.QI.EAGER_THRESHOLD=100 \
--z3cliopt smt.CASE_SPLIT=3 \
--z3cliopt smt.arith.nl=false \
--smtencoding.elim_box true \
--smtencoding.l_arith_repr native \
--smtencoding.nl_arith_repr wrapped\
--max_fuel 1 \
--max_ifuel 1 \
--initial_ifuel 0

include ../Makefile.include

FSTS = $(wildcard *fst)
FSTIS = $(wildcard *fsti) # These are currently verified when the corresponding .fst is verified

TARGETS = $(FSTS:.fst=.uver) #$(FSTIS:.fsti=.uver)

DEST = $(FSTAR_HOME)/examples/vale/

all: $(TARGETS)

#NS: To regenerate hints, use `OTHERFLAGS=--record_hints make`
# %.hints : %.uver

#cp Makefile $(FSTS) $(FSTIS) $(DEST)
deploy: $(FSTS) $(FSTIS) Makefile $(FSTS:=.hints)
	cp -f * $(DEST)

clean: 
	rm *.hints
