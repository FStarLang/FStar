FSTAR_HOME=../..
include ../Makefile.include

all: UserTactics.uver Syntax.uver GRewrite.uver MetaCoq.uver

all-cver: MetaCoq.ucver
.PHONY: neg

all:	Apply.uver		\
	Canon.uver		\
	Arith.uver		\
	Pruning.uver		\
	Cut.uver		\
	Clear.uver		\
	Cases.uver		\
	Tutorial.uver		\
	Syntax.uver		\
	GRewrite.uver		\
	UserTactics.uver	\
	Logic.uver		\
	Synthesis.uver		\
	Printers.uver		\
	Setopts.uver		\
	Neg.uver		\
	Caller.uver		\
	UnitTests.uver		\
	MetaCoq.uver		\
	neg

neg:
	$(MAKE) -C neg
