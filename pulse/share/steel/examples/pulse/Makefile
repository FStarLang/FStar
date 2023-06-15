all: verify verify-bug-reports verify-dice

.PHONY: verify-bug-reports
verify-bug-reports:
	$(MAKE) -C bug-reports verify

.PHONY: verify-dice
verify-dice:
	$(MAKE) -C dice verify

# assuming share/steel/examples/pulse
STEEL_HOME ?= ../../../..

FSTAR_OPTIONS = --include $(STEEL_HOME)/lib/steel/pulse

COMPAT_INDEXED_EFFECTS=

include $(STEEL_HOME)/share/steel/Makefile.include
