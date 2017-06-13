ifndef FSTAR_HOME
   $(error "Please define the `FSTAR_HOME` variable before including this makefile.")
endif

USE_Z3_NIGHTLY?=no
USE_UNTESTED_Z3_NIGHTLY?=no

ifeq ($(USE_Z3_NIGHTLY),yes)
ifndef HAVE_Z3_NIGHTLY_BIN
  ifeq ($(USE_UNTESTED_Z3_NIGHTLY),yes)
    C=get-latest
  else
    C=get-tested
  endif
  $(info Obtaining Z3 nightly binary ...)
  Q=$(shell cd $(FSTAR_HOME) && python .scripts/z3_nightly.py $(C))
  $(info $(Q))
  export Z3=$(lastword $(Q))
  export HAVE_Z3_NIGHTLY_BIN=yes
endif
endif

ifdef Z3
  $(info Using Z3 at $(Z3))
endif
