# common.mk must be included before this file.

FSTAR_EXE ?= fstar.exe
$(call need_exe, FSTAR_EXE)

ifeq ($(KRML_EXE),)
ifneq ($(KRML_HOME),)
KRML_EXE := $(KRML_HOME)/krml
else
KRML_EXE := krml
endif
endif

export KRML_EXE

PULSE_ROOT := $(abspath $(PULSE_ROOT))

# Define the Pulse root directory. We need to fix it to use the Windows path convention on Windows+Cygwin.
ifeq ($(OS),Windows_NT)
  PULSE_HOME := $(shell cygpath -m $(PULSE_ROOT))
else
  PULSE_HOME := $(PULSE_ROOT)
endif
export PULSE_HOME
