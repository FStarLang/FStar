
OTHERFLAGS+=$(FLAGS) $(LIB) --include ../dm4free
FSTAR_HOME=../..
include ../Makefile.include

uall: all

.PHONY: benton2004 uall all benton2004 test pack clean

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
  IfcRecursiveHeapReify.uver\
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

test :\
  Loops.uver \
  Memo.uver\
  NetKat.uver\
  OneTimePad.uver\
  Point.uver\
  ProgramEquivalence.uver\
  ProgramOptimizations.uver\
  RandomTapes.uver


%.fst-in:
	@echo $(OTHERFLAGS)

pack:
	cd ../..; zip -r relational.zip examples/rel examples/dm4free

FIND=$(shell which gfind > /dev/null 2>&1 && echo gfind || echo find)
SED=$(shell which gsed > /dev/null 2>&1 && echo gsed || echo sed)

results_without_hints:
	+HINTS_ENABLED='' OTHERFLAGS='--record_hints' make -k all > results_without_hints || :

results_with_hints:
	+make -k all > results_with_hints || :

timings_without_hints.csv: results_without_hints
	$(SED) -n results_without_hints -e '/Verified/s/.*: \([^ ]*\) (\([0-9]*\) .*/\1,\2/p' \
		| sort -t , -k 1,1 > timings_without_hints.csv

timings_with_hints.csv: results_with_hints
	$(SED) -n results_with_hints -e '/Verified/s/.*: \([^ ]*\) (\([0-9]*\) .*/\1,\2/p' \
		| sort -t , -k 1,1 > timings_with_hints.csv

loc.csv:
	$(FIND) . -name '*fst' \
		-exec sh -c 'sed -n -e "/^\((\*.*\*)\| \|\/\/.*\)*$$/!p" {} | wc -l ' \; \
		-print | tr '\n' ' ' \
		| sed -e 's; \.\/;,;g' -e 's;\.fst ;\n;g' \
		| sort -t , -k 2,2 > loc.csv

timings0.csv: timings_without_hints.csv timings_with_hints.csv
	join -t , -1 1 -2 1 timings_without_hints.csv timings_with_hints.csv > timings0.csv

timings.csv: timings0.csv loc.csv
	echo 'filename,timings (no hints),timings (with hints),loc' > timings.csv
	join -t , -1 1 -2 2 timings0.csv loc.csv >> timings.csv
	#rm results_without_hints results_with_hints timings_without_hints.csv timings_with_hints.csv loc.csv timings0.csv


clean:
	rm -f results_without_hints results_with_hints timings_without_hints.csv timings_with_hints.csv loc.csv timings0.csv timings.csv
