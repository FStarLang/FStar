VERFILES=unit1.fst unit2.fst testset.fst 
include ../Makefile.include
NEGFILES=negative-tests.fst

all: .all.ver all-neg

all-neg: $(NEGFILES)
	-$(FSTAR) $(STDLIB) $^
	echo "EXPECT 28 FAILURES<------------------------------------"

