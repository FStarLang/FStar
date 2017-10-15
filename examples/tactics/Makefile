FSTAR_HOME=../..
include ../Makefile.include

.PHONY: neg

all:	Apply.uver		\
	Canon.uver		\
	Arith.uver		\
	Pruning.uver		\
	Cut.uver		\
	Fail.uver		\
	MApply.uver		\
	Clear.uver		\
	Cases.uver		\
	Tutorial.uver		\
	Syntax.uver		\
	Normalization.uver	\
	GRewrite.uver		\
	Rename.uver		\
	UserTactics.uver	\
	Logic.uver		\
	Trace.uver		\
	Bug1299.fst		\
	Nest.uver		\
	TestBV.uver		\
	Map.uver		\
	Map.OpaqueToSMT.uver	\
	Map.OpaqueToSMT.Test.uver	\
	Synthesis.uver		\
	Printers.uver		\
	Setopts.uver		\
	Simplifier.uver		\
	Neg.uver		\
	Caller.uver		\
	Retype.uver		\
	Unify.uver		\
	UnitTests.uver		\
	MetaCoq.uver		\
	neg
	# launch			\

launch: Launch.fst
	$(FSTAR) --unsafe_tactic_exec --verify_module Launch $^

neg:
	$(MAKE) -C neg
