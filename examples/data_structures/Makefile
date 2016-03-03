include ../Makefile.include
all: bst uall

uall:
	$(FSTAR) --universes --explicit_deps ArrayRealized.fst Vector.fst
	$(FSTAR) --universes rbtree.fst

bst: binary_search_tree.fulllib.ver
