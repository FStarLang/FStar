FSTAR_HOME=../../..

all: verify-all

include .depend
include $(FSTAR_HOME)/examples/Makefile.include

verify-all: $(ALL_CHECKED_FILES)

.depend:
	@echo "[DEPEND    $(patsubst $(shell realpath $(FSTAR_HOME))/%,%/,$(shell pwd))]"
	$(Q)$(FSTAR) --dep full $(wildcard *.fst *.fsti) > .depend

%.checked:
	@echo "[CHECK     $<]"
	$(Q)$(FSTAR) $(SIL) --cache_checked_modules $<
	$(Q)touch -c $@

clean:
	rm -f .depend *.checked

depend: .depend
