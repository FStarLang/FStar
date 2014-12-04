VERFILES=counters.fst insertionsort-lemma.fst insertionsort.fst intlist-insertionsort.fst mergesort.fst
OTHERFLAGS=--z3timeout 10
include ../Makefile.include
all: .all.ver listprops
listprops: $(FSTAR_HOME)/lib/listproperties.fst
	$(FSTAR) $(STDLIB) $^
