FSTAR_HOME = ../../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe
EXCLUDED_FILES=Ex1.fst

all: $(addsuffix .test, $(filter-out $(EXCLUDED_FILES), $(wildcard *.fst)))

%.fst.test: %.fst
	$(FSTAR) --indent $^ > $@
	diff -q $^ $@

clean:
	rm -f *.test
