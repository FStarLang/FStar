FSTAR_HOME=../..
include ../Makefile.include

all:uall

uall: shallow examples

shallow: SepLogic.Heap.uver Shallow.uver SL.Heap.uver SL.Effect.uver SL.Shallow.uver

#not worrying about extracted interfaces right now
examples:
	$(FSTAR) --use_two_phase_tc false Examples.fst
	$(FSTAR) --record_hints --use_hints SL.Examples.fst
	$(FSTAR) --record_hints --use_hints SL.ExamplesAuto.fst

OTHERFLAGS+=--include ../tactics

%.fst-in:
	@echo $(OTHERFLAGS)
