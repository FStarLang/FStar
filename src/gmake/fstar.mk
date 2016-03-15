ifndef FSTAR_HOME
   $(error "Please define the `FSTAR_HOME` variable before including this makefile.")
endif

FSTAR=$(shell readlink -e $(FSTAR_HOME))/bin/fstar.exe $(OTHERFLAGS)

