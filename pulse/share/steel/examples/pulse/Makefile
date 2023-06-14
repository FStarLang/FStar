all: verify
	$(MAKE) -C bug-reports
	$(MAKE) -C dice

# assuming share/steel/examples/pulse
STEEL_HOME ?= ../../../..

FSTAR_OPTIONS = --include $(STEEL_HOME)/lib/steel/pulse

COMPAT_INDEXED_EFFECTS=

include $(STEEL_HOME)/share/steel/Makefile.include
