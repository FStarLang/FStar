FSTAR_HOME = ../../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

all: $(addsuffix .test, $(wildcard *.fst))

%.fst.test: %.fst
	$(FSTAR) --indent $^ > $@
	diff -q $^ $@

clean:
	rm -f *.test
