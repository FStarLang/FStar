FSTAR=fstar
FSTAR_FILES := MemCpy.fst
FSTAR_FLAGS +=--cache_checked_modules --use_hints --use_hint_hashes $(OTHERFLAGS)
FSTAR := $(FSTAR) $(FSTAR_FLAGS)

all: $(addsuffix .checked, $(FSTAR_FILES))

.depend:
	$(FSTAR) --dep full $(FSTAR_FILES) > .depend

depend: .depend

-include .depend

%.checked:
	$(FSTAR) $<
	touch -c $@

wc:
	wc -l prims.fst $(ALL)


extract:
	krml -skip-compilation MemCpy.fst -tmpdir out

clean:
	rm -rf *.c *.h *~ *.checked *.checked.lax *.krml .depend out
