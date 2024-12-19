# common.mk must be included before this file.

ifeq ($(FSTAR_HOME),)
$(error Pulse needs an FSTAR_HOME)
endif

ifeq ($(FSTAR_EXE),)
ifneq ($(FSTAR_HOME),)
FSTAR_EXE := $(FSTAR_HOME)/bin/fstar.exe
endif
endif

FSTAR_EXE ?= $(shell which fstar.exe)
FSTAR_EXE := $(FSTAR_EXE)
export FSTAR_EXE

$(call need_exe, FSTAR_EXE)

export FSTAR_HOME

PULSE_ROOT := $(abspath $(PULSE_ROOT))

# Define the Pulse root directory. We need to fix it to use the Windows path convention on Windows+Cygwin.
ifeq ($(OS),Windows_NT)
  PULSE_HOME := $(shell cygpath -m $(PULSE_ROOT))
else
  PULSE_HOME := $(PULSE_ROOT)
endif
export PULSE_HOME
