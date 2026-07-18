all: test-missing.touch test-missing-nocache.touch

# So test.mk does not do anything by default
NOVERIFY=1

PULSE_ROOT ?= ../../..
include $(PULSE_ROOT)/mk/test.mk

define MUSTFAIL
	@if $1 >/dev/null 2>&1; then echo "Expected failure for '$1', but command succeeded"; false; fi
	@echo "Command '$1' failed as expected"
endef

test-missing.touch: $(CACHE_DIR)/Missing.fsti.checked
	$(call MUSTFAIL,$(FSTAR_EXE) Missing.fst)
	touch $@

test-missing-nocache.touch:
	$(call MUSTFAIL,$(FSTAR_EXE) --cache_off Missing.fst)
	touch $@
