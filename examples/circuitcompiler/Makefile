FSTAR_HOME=../..
include ../Makefile.include

all:
	$(FSTAR) cktast.fst
	$(FSTAR) ast.fst
	$(FSTAR) --explicit_deps   FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.IO.fsti FStar.List.fst mylist.fst
	$(FSTAR) wires.fst
