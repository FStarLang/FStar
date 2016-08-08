OTHERFLAGS=

FSTAR_HOME=../..
include ../Makefile.include

all: uall sall

uall: BinarySearch.uver IntSort.uver InsertionSort.uver MergeSort.uver QuickSort.List.uver QuickSort.Seq.uver QuickSort.Array.uver GC.uver Unification.uver #downgrade //TODO
sall: counters.sver

downgrade: QuickSort.Array.fst downgrade.fst
	$(FSTAR) --include $(FSTAR_HOME)/ulib/reclaimable downgrade.fst --verify_module Downgrade
