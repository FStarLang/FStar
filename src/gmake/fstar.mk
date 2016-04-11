ifndef FSTAR_HOME
   $(error "Please define the `FSTAR_HOME` variable before including this makefile.")
endif

FSTAR_ALWAYS=$(shell cd $(FSTAR_HOME) && pwd)/bin/fstar.exe $(OTHERFLAGS)
FSTAR=$(FSTAR_ALWAYS)
