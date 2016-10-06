FSTAR_HOME=../..
OTHERFLAGS=
include ../Makefile.include

all: uall
uall: Effects.Def.uver FStar.DM4F.IntST.uver-explicit FStar.DM4F.Exceptions.uver-explicit FStar.DM4F.ExnSt.uver FStar.DM4F.StExn.uver-explicit FStar.DM4F.ST.uver-explicit FStar.DM4F.Heap.uver FStar.DM4F.Heap.ST.uver
sall:

old:
	$(MAKE) -C old

%.uver-explicit: %.fst
	$(FSTAR) $^ --explicit_deps

%.uver: %.fst
	$(FSTAR) $^

include $(FSTAR_HOME)/ulib/ml/Makefile.include
