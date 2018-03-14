FSTAR_HOME=../..
include ../Makefile.include

.PHONY: neg

all:	Apply.uver		\
	ApplyLemma.uver		\
	Canon.uver		\
	CanonMonoid.uver	\
	CanonCommMonoid.uver	\
	Arith.uver		\
	Pruning.uver		\
	Cut.uver		\
	Fail.uver		\
	MApply.uver		\
	Clear.uver		\
	Cases.uver		\
	VC.uver			\
	Div.uver		\
	Change.uver		\
	Tutorial.uver		\
	Splice.uver		\
	Syntax.uver		\
	NormBinderType.uver	\
	Normalization.uver	\
	GRewrite.uver		\
	VQuote.uver		\
	Rename.uver		\
	Imp.uver		\
	Inlining.uver		\
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
	Sequences.uver		\
	Caller.uver		\
	Retype.uver		\
	Pose.uver		\
	Unify.uver		\
	UnitTests.uver		\
	MetaCoq.uver		\
	Rewrite.Monoid.uver     \
	neg
	# launch			\

launch: Launch.fst
	$(FSTAR) --unsafe_tactic_exec $^

neg:
	$(MAKE) -C neg
