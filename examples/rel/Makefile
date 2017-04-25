
OTHERFLAGS+=$(FLAGS) $(LIB) --include ../dm4free
FSTAR_HOME=../..
include ../Makefile.include

uall: all

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

%.fst-in:
	@echo $(OTHERFLAGS)

pack:
	cd ../..; zip -r relational.zip examples/rel examples/dm4free

CFSTAR=$(subst CURRENT_DIR,examples/rel,$(CVERFSTAR))

all-cver: $(subst fst,ucver,$(FILES))
