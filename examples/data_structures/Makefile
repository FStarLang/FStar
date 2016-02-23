VERFILES=array-realized.fst vectors.fst
include ../Makefile.include
all: .all.ver bst rbtree

bst: binary_search_tree.fulllib.ver

rbtree: rbtree.fst
	$(FSTAR) $^
