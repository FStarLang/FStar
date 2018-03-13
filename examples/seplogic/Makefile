FSTAR_HOME=../..
include ../Makefile.include

all:uall

uall: deep shallow

deep: FStar.SL.Monotonic.Heap.uver FStar.SL.Heap.uver Lang.uver SL.Tactics.uver Examples.uver 

shallow: SepLogic.Heap.uver Shallow.uver SL.Effect.uver SL.Examples.uver

SL.Effect.uver : SL.Effect.fst
	$(FSTAR) --__temp_fast_implicits $(OTHERFLAGS) $^

SL.Examples.uver : SL.Examples.fst
	$(FSTAR) --__temp_fast_implicits $(OTHERFLAGS) $^
