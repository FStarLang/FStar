FSTAR_HOME=../../..
include ../../Makefile.include
FSTAR_FILES := Demo.fst
FSTAR_FLAGS +=--cache_checked_modules --use_hints --use_hint_hashes --use_extracted_interfaces true $(OTHERFLAGS)
FSTAR := $(FSTAR) $(FSTAR_FLAGS)

all: $(addsuffix .checked, $(FSTAR_FILES))

.depend:
	$(FSTAR) --dep full $(FSTAR_FILES) > .depend

depend: .depend

-include .depend

%.checked:
	$(FSTAR) $<
	touch -c $@

%.fst-in:
	@echo $(FSTAR_FLAGS) --max_fuel 0 --max_ifuel 0

wc:
	wc -l prims.fst $(ALL)


extract:
	@krml -skip-compilation Demo.fst -tmpdir out | grep "wrote out"

extract-tailcalls:
	@krml -skip-compilation -ftail-calls Demo.fst -tmpdir out | grep "wrote out"

clean:
	rm -rf *.c *.h *~ *.checked *.checked.lax *.krml .depend out
