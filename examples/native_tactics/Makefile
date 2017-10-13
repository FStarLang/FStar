FSTAR_HOME=../..
CACHE = _cache

include $(FSTAR_HOME)/ulib/ml/Makefile.include

OCAML_OUTPUT=$(FSTAR_HOME)/src/ocaml-output
INCLUDES=$(addprefix -I $(OCAML_OUTPUT)/_build/, src/tactics/ml ulib/ml src/ocaml-output/ src/basic/ml)
FSTAR=$(FSTAR_HOME)/bin/fstar.exe
FSTARTACLIB=$(FSTAR_HOME)/bin/fstar-tactics-lib/fstartaclib.cmxs

# The cache is shared and the tests can interactly badly.
.NOTPARALLEL:
.PRECIOUS: _cache/%.cmxs
.PHONY: %.test fstartaclib

MODULES=Print Split Canon

all: $(patsubst %,%.test,$(MODULES))

$(FSTARTACLIB):
	$(MAKE) -C $(FSTAR_HOME)/ulib install-fstar-tactics

$(CACHE):
	mkdir $@

$(CACHE)/%.cmxs: %.Test.fst $(FSTARTACLIB) | $(CACHE)
	$(FSTAR) $(OTHERFLAGS) --gen_native_tactics $(CACHE) $<

%.test: %.Test.fst $(CACHE)/%.cmxs
	$(FSTAR) $(OTHERFLAGS) --use_native_tactics $(CACHE) $<

clean:
	rm -f $(CACHE)/*.ml $(CACHE)/*.cm* $(CACHE)/*.o
