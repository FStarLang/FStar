include ../Makefile.include
all: bst rbtree uall

uall:
	$(FSTAR) --universes --explicit_deps ArrayRealized.fst Vector.fst

bst: binary_search_tree.fulllib.ver

rbtree: rbtree.fst
	$(FSTAR) $^
