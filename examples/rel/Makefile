
OTHERFLAGS+=$(FLAGS) $(LIB) --include ../dm4free
FSTAR_HOME=../..
include ../Makefile.include

uall: all

.PHONY: benton2004

all:\
  benton2004\
  Bijection.uver\
  Equivalence.uver\
  IfcComposeReify.uver\
  IfcDeclassify.uver\
  IfcDelimitedRelease.uver\
  IfcDelimitedReleaseReify.uver\
  IfcExample.uver\
  IfcExampleReify0.uver\
  IfcExampleReify1.uver\
  IfcExampleReify2.uver\
  IfcExampleReify3.uver\
  IfcRecursiveReify.uver\
  IfcReificationRegressionTest.uver\
  IfcRules.uver\
  IfcRulesReify.uver\
  IfcTypechecker.uver\
  Loops.uver\
  Memo.uver\
  NetKat.uver\
  OneTimePad.uver\
  Point.uver\
  ProgramEquivalence.uver\
  ProgramOptimizations.uver\
  RandomTapes.uver\
  Recursive.uver\
  ReifyLong.uver\
  Rel.uver\
  StRel.uver\
  Swap.uver\
  UnionFind.Forest.uver\
  UnionFind.uver\
  UnionFind.Functions.uver\
  While.uver\
  WhileReify.uver \
  OTP.uver \
  ElGamal.uver
  # IfcRecursiveHeapReify.uver\ regressed; too slow (NS/07-10)

benton2004:\
  Benton2004.Aux.uver\
  Benton2004.uver\
  Benton2004.DDCC.uver\
  Benton2004.DDCC.Examples.uver\
  Benton2004.SmithVolpano.uver\
  Benton2004.RHL.uver\
  Benton2004.RHL.Examples.uver\
  Benton2004.RHL.Derived.uver\
  Benton2004.RHL.Examples2.uver\

%.fst-in:
	@echo $(OTHERFLAGS)

pack:
	cd ../..; zip -r relational.zip examples/rel examples/dm4free
