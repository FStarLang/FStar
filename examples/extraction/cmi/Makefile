FSTAR_HOME=../../..
include ../../Makefile.include
include .depend

%.fst.checked:
	$(FSTAR) $< --cache_checked_modules

%.fsti.checked:
	$(FSTAR) $< --cache_checked_modules

%.ml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml --extract_module $(basename $(notdir $(subst .checked,,$<))) --cmi
	egrep test_function B.ml | egrep -q -v A.id #test that A.id is inlined

.depend:
	$(FSTAR) --dep full B.fst --extract A --extract B --cmi > .depend

depend: .depend

clean:
	rm -f .depend A.ml B.ml *.checked *~
