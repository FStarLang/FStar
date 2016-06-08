VERFILES=counters.fst 
OTHERFLAGS=

FSTAR_HOME=../..
include ../Makefile.include

all: uall strat_all

strat_all:.all.ver 

uall: BinarySearch.uver IntSort.uver InsertionSort.uver MergeSort.uver QuickSort.List.uver QuickSort.Seq.uver QuickSort.Array.uver GC.uver Unification.uver #downgrade //TODO

%.uver: %.fst
	$(FSTAR) --universes --verify_module $* $^

downgrade: QuickSort.Array.fst downgrade.fst
	$(FSTAR) --universes --include $(FSTAR_HOME)/ulib/reclaimable downgrade.fst --verify_module Downgrade
