FSTAR_HOME=../..
include ../Makefile.include
all: bst uall

uall: vector rbtree

bst: binary_search_tree.fulllib.ver

vector:
	$(FSTAR) --universes --explicit_deps ArrayRealized.fst Vector.fst

rbtree:
	$(FSTAR) --universes rbtree.fst
