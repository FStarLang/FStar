include ../Makefile.include

all: all-lax all-ver all-neg

VERFILES=unit1.fst testset.fst unif.fst
LAXFILES=rec.fst pat.fst 
NEGFILES=negative-tests.fst

all-ver: $(VERFILES)
	$(FSTAR) $(STDLIB) $^

all-lax: rec.fst pat.fst 
	$(FSTAR) $(STDLIB) --lax $^

all-neg: $(NEGFILES)
	-$(FSTAR) $(STDLIB) $^
	echo "EXPECT 20 FAILURES<------------------------------------"

#DO WE REALLY NEED THESE HERE?
utils:
	$(FSTAR) --codegen OCaml --prims prims.fst utils.fst

stdlib:
	$(FSTAR) --codegen OCaml $(STDLIB)

