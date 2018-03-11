FSTAR_HOME=../../..

include $(FSTAR_HOME)/ulib/ml/Makefile.include

OCAML_OUTPUT=$(FSTAR_HOME)/src/ocaml-output
INCLUDES=$(addprefix -I $(OCAML_OUTPUT)/_build/, src/tactics/ml ulib/ml src/ocaml-output/ src/basic/ml)
FSTAR=$(FSTAR_HOME)/bin/fstar.exe
FSTARTACLIB=$(FSTAR_HOME)/bin/fstar-tactics-lib/fstartaclib.cmxs

.PHONY: %.test fstartaclib

MODULES= Apply Arith Bane.Test CanonDeep Clear Cut DependentSynth Fail Imp Logic Nest Pruning Rename Retype Sequences Simplifier Tutorial Unify
MODULES_BROKEN=Bug1270 CanonMonoid Printers Synthesis Trace


all: $(patsubst %,%.test,$(MODULES))

$(FSTARTACLIB):
	$(MAKE) -C $(FSTAR_HOME)/ulib install-fstar-tactics

%.ml: %.fst $(FSTARTACLIB)
	$(FSTAR) $*.fst --codegen Plugin --extract $*

%.test: %.fst %.ml
	$(FSTAR) $*.fst --load $*

clean:
	rm -f *.ml *.o *.cm[ix] *.cmxs
