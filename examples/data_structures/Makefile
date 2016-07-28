FSTAR_HOME=../..
include ../Makefile.include
all: bst uall

uall: vector rbtree

bst:
	$(FSTAR) BinarySearchTree.fst
	$(FSTAR) BinarySearchTree0.fst
	$(FSTAR) BinarySearchTreeBasic.fst
	$(FSTAR) BinarySearchTreeFirst.fst

vector:
	$(FSTAR) --explicit_deps ArrayRealized.fst Vector.fst

rbtree:
	$(FSTAR) RBTree.fst
