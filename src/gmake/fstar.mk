ifndef FSTAR_HOME
   $(error "Please define the `FSTAR_HOME` variable before including this makefile.")
endif

HINTS_ENABLED?=--use_hints --use_hint_hashes

ifdef Z3
OTHERFLAGS+=--smt $(Z3)
endif

FSTAR_ALWAYS=$(shell cd $(FSTAR_HOME) && pwd)/bin/fstar.exe $(OTHERFLAGS) $(HINTS_ENABLED)
FSTAR=$(FSTAR_ALWAYS)
