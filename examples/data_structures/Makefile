FSTAR_HOME=../..
include ../Makefile.include

OTHERFLAGS+=--use_two_phase_tc true

all: uall

uall: BinaryTrees.uver bst RBTree.uver vector BinaryTreesEnumeration.uver MerkleTree.uver Lens.uver StatefulLens.uver

bst: BinarySearchTree.uver BinarySearchTree0.uver BinarySearchTreeBasic.uver BinarySearchTreeFirst.uver

vector:
	$(FSTAR) ArrayRealized.fst Vector.fst
