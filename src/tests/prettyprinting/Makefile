FSTAR_HOME = ../../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe
EXCLUDED_FILES=

BASES=$(filter-out $(EXCLUDED_FILES), $(wildcard *.base.fst))
TESTS=$(patsubst %.base.fst, %.print.fst-test, $(BASES))
TESTS_IN_PLACE=$(patsubst %.base.fst, %.print_in_place.fst-test, $(BASES))

.SECONDARY:

all: $(TESTS) $(TESTS_IN_PLACE)

%.print_in_place.fst: %.base.fst
	cp $< $@
	$(FSTAR) --print_in_place $@

%.print_in_place.fst-test: %.base.fst %.print_in_place.fst
	diff --strip-trailing-cr $^

%.print.fst: %.base.fst
	$(FSTAR) --print $< > $@

%.print.fst-test: %.base.fst %.print.fst
	diff --strip-trailing-cr $^

clean:
	rm -f *.test.fst
