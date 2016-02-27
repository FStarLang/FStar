VERFILES=ArrayRealized.fst Vector.fst
include ../Makefile.include
all: .all.ver bst rbtree uall

uall:
	$(FSTAR) --universes --explicit_deps ArrayRealized.fst Vector.fst

bst: binary_search_tree.fulllib.ver

rbtree: rbtree.fst
	$(FSTAR) $^
