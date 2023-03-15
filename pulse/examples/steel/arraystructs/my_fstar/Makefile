all:

FSTAR_HOME ?= $(realpath $(dir $(shell which fstar.exe))/..)
FSTAR_EXE = $(FSTAR_HOME)/bin/fstar.exe

include $(FSTAR_HOME)/.common.mk
include $(FSTAR_HOME)/ulib/gmake/z3.mk    # This pins $(Z3) ...
include $(FSTAR_HOME)/ulib/gmake/fstar.mk # and $(FSTAR) for all sub-make calls
include $(FSTAR_HOME)/src/Makefile.boot.common

