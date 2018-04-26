FSTAR_HOME = ../../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe
EXCLUDED_FILES=

all: $(addsuffix .test, $(filter-out $(EXCLUDED_FILES), $(wildcard *.fst)))

all_text: $(addsuffix .test_text, $(wildcard *.fst))

%.fst.test: %.fst
	$(FSTAR) --indent $^ > $@
	diff --strip-trailing-cr $^ $@

# Eliminate empty lines before diffing
%.fst.test_text: %.fst
	$(FSTAR) --indent $^ | sed '/^$$/d' > $@
	sed '/^$$/d' $^ | diff $@ -

clean:
	rm -f *.test *.test_text
