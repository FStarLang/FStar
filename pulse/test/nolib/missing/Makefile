all: test-missing test-missing-nocache

# So test.mk does not do anything by default
NOVERIFY=1

PULSE_ROOT ?= ../../..
include $(PULSE_ROOT)/mk/test.mk

define MUSTFAIL
	@if $1 >/dev/null 2>&1; then echo "Expected failure for '$1', but command succeeded"; false; fi
	@echo "Command '$1' failed as expected"
endef

test-missing: $(CACHE_DIR)/Missing.fsti.checked
	$(call MUSTFAIL,$(FSTAR_EXE) Missing.fst)

test-missing-nocache:
	$(call MUSTFAIL,$(FSTAR_EXE) --cache_off Missing.fst)
