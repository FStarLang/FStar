
OTHERFLAGS+=$(FLAGS) $(LIB) --include ../dm4free
FSTAR_HOME=../..
include ../Makefile.include

uall: all

<<<<<<< HEAD
FILES =\
  Bijection.fst\
  Equivalence.fst\
  IfcComposeReify.fst\
  IfcDeclassify.fst\
  IfcDelimitedRelease.fst\
  IfcDelimitedReleaseReify.fst\
  IfcExample.fst\
  IfcExampleReify0.fst\
  IfcExampleReify1.fst\
  IfcExampleReify2.fst\
  IfcExampleReify3.fst\
  IfcRecursiveHeapReify.fst\
  IfcRecursiveReify.fst\
  IfcReificationRegressionTest.fst\
  IfcRules.fst\
  IfcRulesReify.fst\
  IfcTypechecker.fst\
  Loops.fst\
  Memo.fst\
  NetKat.fst\
  OneTimePad.fst\
  Point.fst\
  ProgramEquivalence.fst\
  ProgramOptimizations.fst\
  RandomTapes.fst\
  Recursive.fst\
  ReifyLong.fst\
  Rel.fst\
  StRel.fst\
  Swap.fst\
  UnionFind.Forest.fst\
  UnionFind.fst\
  UnionFind.Functions.fst\
  While.fst\
  WhileReify.fst \
  OTP.fst \
  ElGamal.fst

all: $(subst fst,uver,$(FILES))
=======
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
>>>>>>> ebe18753096dbe8111b6f009924051d6f533bab4

%.fst-in:
	@echo $(OTHERFLAGS)

pack:
	cd ../..; zip -r relational.zip examples/rel examples/dm4free

all-cver: $(subst fst,ucver,$(FILES))
