
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
  IfcMonitor.uver\
  IfcMonitorTest.uver\
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
	cp README.md ..
	cd ../..; zip -r relational.zip examples/rel examples/dm4free examples/README.md examples/Makefile.include
	rm ../README.md

FIND=$(shell which gfind > /dev/null 2>&1 && echo gfind || echo find)
SED=$(shell which gsed > /dev/null 2>&1 && echo gsed || echo sed)

MODULES=$(shell $(SED) -e 's!^\([^,]*\).*$$!\1!' < sections.csv | xargs echo)

sections-sorted.csv:
	sort -t , -k 1,1 < sections.csv > sections-sorted.csv

modules-sorted.csv:
	i=0; for f in $(MODULES) ; do echo $$i,$$f ; i=$$(($$i + 1)) ; done | sort -t , -k 2,2 > modules-sorted.csv

results_without_hints:
	+HINTS_ENABLED='' OTHERFLAGS='--record_hints' make -k $(addsuffix .uver,$(MODULES)) > results_without_hints || :

results_with_hints:
	+make -k $(addsuffix .uver,$(MODULES)) > results_with_hints || :

timings_without_hints.csv: results_without_hints
	$(SED) -n results_without_hints -e '/Verified/s/.*: \([^ ]*\) (\([0-9]*\) .*/\1,\2/p' \
		| sort -t , -k 1,1 \
		 > timings_without_hints.csv

timings_with_hints.csv: results_with_hints
	$(SED) -n results_with_hints -e '/Verified/s/.*: \([^ ]*\) (\([0-9]*\) .*/\1,\2/p' \
		| sort -t , -k 1,1 \
		 > timings_with_hints.csv

loc.csv:
	for f in $(MODULES) ; do echo -n $$f, ; wc -l < $$f.fst ; done \
		| sort -t , -k 1,1 \
		 > loc.csv

timings0.csv: timings_without_hints.csv timings_with_hints.csv
	join --check-order -t , -1 1 -2 1 timings_without_hints.csv timings_with_hints.csv > timings0.csv

timings1.csv: timings0.csv loc.csv
	join --check-order -t , -1 1 -2 1 timings0.csv loc.csv > timings1.csv
	#rm results_without_hints results_with_hints timings_without_hints.csv timings_with_hints.csv loc.csv timings0.csv

timings2.csv: timings1.csv sections-sorted.csv
	join --check-order -t , -1 1 -2 1 sections-sorted.csv timings1.csv | sort -t , -k 1,1 > timings2.csv

timings.csv: timings2.csv modules-sorted.csv
	echo 'Subject,Section,1st run (ms),Proof replay (ms),Loc' > timings.csv
	join --check-order -t , -1 1 -2 2 timings2.csv modules-sorted.csv | sort -n -t , -k 6,6 | $(SED) 's!,[0-9]*$$!!' >> timings.csv

clean:
	rm -f sections-sorted.csv modules-sorted.csv results_without_hints results_with_hints timings_without_hints.csv timings_with_hints.csv loc.csv timings0.csv timings1.csv timings2.csv timings.csv

timings.tex: timings.csv
	./setup_timings.py
