VERFILES=array-realized.fst vectors.fst
#rbtree.fst -- currently disabled
include ../Makefile.include
all: .all.ver bst
# rbtree -- this fails often on some machines even with timeout 30

bst: binary_search_tree.fulllib.ver

rbtree: rbtree.fst
	$(FSTAR) $(STDLIB) --z3timeout 15 $^
