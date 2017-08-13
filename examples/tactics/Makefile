FSTAR_HOME=../..
include ../Makefile.include

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
	Trace.uver		\
	Synthesis.uver		\
	Printers.uver		\
	Setopts.uver		\
	Neg.uver		\
	Caller.uver		\
	UnitTests.uver		\
	MetaCoq.uver		\
	launch			\
	neg

launch: Launch.fst
	$(FSTAR) --unsafe_tactic_exec --verify_module Launch $^

neg:
	$(MAKE) -C neg
