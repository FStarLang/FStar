all: verify

# assuming share/steel/examples/pulse/dice/l0
STEEL_HOME ?= ../../../../../..

FSTAR_OPTIONS = --include $(STEEL_HOME)/lib/steel/pulse --include $(STEEL_HOME)/share/steel/examples/pulse/lib --include $(STEEL_HOME)/share/steel/examples/pulse/dice/common

COMPAT_INDEXED_EFFECTS=

include $(STEEL_HOME)/share/steel/Makefile.include
