FSTAR_HOME=../..
include ../Makefile.include

all:uall

uall: deep shallow

deep: FStar.SL.Monotonic.Heap.uver FStar.SL.Heap.uver Lang.uver SL.Tactics.uver Examples.uver 

shallow: SepLogic.Heap.uver Shallow.uver SL.Heap.uver SL.Effect.uver SL.Shallow.uver example

#not worrying about two phases or extracted interfaces right now
example:
	$(FSTAR) --use_two_phase_tc false --record_hints --use_hints SL.Examples.fst
