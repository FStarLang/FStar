FSTAR_HOME=../..
include ../Makefile.include
all: uall sall

uall: bst RBTree.uver vector
sall:

bst: BinarySearchTree.uver BinarySearchTree0.uver BinarySearchTreeBasic.uver BinarySearchTreeFirst.uver

vector:
	$(FSTAR) --explicit_deps ArrayRealized.fst Vector.fst
