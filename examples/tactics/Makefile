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
	NormBinderType.uver	\
	Normalization.uver	\
	GRewrite.uver		\
	Rename.uver		\
	UserTactics.uver	\
	Logic.uver		\
	DependentSynth.uver	\
	NatPos.uver		\
	Trace.uver		\
	Bug1252.uver		\
	Bug1270.uver		\
	Bug1272.uver		\
	Bug1299.uver		\
	Admit.uver		\
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
	$(FSTAR) --unsafe_tactic_exec $^

neg:
	$(MAKE) -C neg
