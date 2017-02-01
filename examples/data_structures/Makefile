FSTAR_HOME=../..
include ../Makefile.include
all: uall

uall: bst RBTree.uver vector

bst: BinarySearchTree.uver BinarySearchTree0.uver BinarySearchTreeBasic.uver BinarySearchTreeFirst.uver

vector:
	$(FSTAR) --explicit_deps ArrayRealized.fst Vector.fst
