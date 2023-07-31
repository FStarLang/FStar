all: verify

# assuming share/steel/examples/pulse/dice/l0
STEEL_HOME ?= ../../../../../..
DICE_HOME ?= ..
PULSE_HOME ?= ../..

FSTAR_OPTIONS = --include $(STEEL_HOME)/lib/steel/pulse --include $(PULSE_HOME)/lib --include $(DICE_HOME)/common

COMPAT_INDEXED_EFFECTS=

include $(STEEL_HOME)/share/steel/Makefile.include
