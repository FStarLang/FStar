FSTAR_HOME=../..
CACHE = _cache

include $(FSTAR_HOME)/ulib/ml/Makefile.include

OCAML_OUTPUT=$(FSTAR_HOME)/src/ocaml-output
INCLUDES=$(addprefix -I $(OCAML_OUTPUT)/_build/, src/tactics/ml ulib/ml src/ocaml-output/ src/basic/ml)
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

.PRECIOUS: %.cmxs
.PHONY: %.test

MODULES=Print Split Canon

all: $(patsubst %,%.cmxs,$(MODULES)) $(patsubst %,%.test,$(MODULES))

.ulib: ../../bin/fstarlib/fstarlib.cmxa
	touch $@

../../bin/fstarlib/fstarlib.cmxa:
	$(MAKE) -C $(ULIB_ML)

$(CACHE):
	mkdir $@

%.cmxs: %.Test.fst .ulib $(CACHE)
	$(FSTAR) $(OTHERFLAGS) --gen_native_tactics $(CACHE) $<

%.test: %.Test.fst %.cmxs
	$(FSTAR) $(OTHERFLAGS) --use_native_tactics $(CACHE) $<

clean:
	rm -f $(CACHE)/*.ml $(CACHE)/*.cm* $(CACHE)/*.o
