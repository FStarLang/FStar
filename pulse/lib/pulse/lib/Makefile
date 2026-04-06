PULSE_HOME ?= ../../..

all: verify

SRC_DIRS := . class pledge
INCLUDE_PATHS += $(PULSE_HOME)/lib/pulse $(PULSE_HOME)/lib/pulse/core
FSTAR_OPTIONS += --already_cached '*,-Pulse.Lib,-Pulse.Class,-PulseTest'

include $(PULSE_HOME)/share/pulse/Makefile.include-base
