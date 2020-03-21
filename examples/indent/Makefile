.PHONY: %.run clean
.PRECIOUS: %.fst-indented

FSTAR_HOME=../..

include $(FSTAR_HOME)/examples/Makefile.include

MODULES=$(wildcard Test*.fst)

all: $(patsubst %.fst,%.run,$(MODULES))

accept: $(patsubst %.fst,%.run-accept,$(MODULES))

%.fst-indented: %.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --print $< > $@

%.run: %.fst-indented
	diff $<.expected $<

%.run-accept: %.fst-indented
	cp $< $<.expected

clean:
	rm -rf out
	rm -f *.fst-indented
