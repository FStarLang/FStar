FSTAR_HOME = ../../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe
EXCLUDED_FILES=

all: $(addsuffix .test.fst, $(filter-out $(EXCLUDED_FILES), $(wildcard *.base.fst)))

%.fst.test.fst: %.fst
	$(FSTAR) --print $^ > $@
	diff --strip-trailing-cr $^ $@
	$(FSTAR) --print_in_place $@
	diff --strip-trailing-cr $@ $^

clean:
	rm -f *.test.fst
