ifndef FSTAR_HOME
   $(error "Please define the `FSTAR_HOME` variable before including this makefile.")
endif

HINTS_ENABLED?=--use_hints

ifdef Z3
OTHERFLAGS+=--smt $(Z3)
endif

FSTAR_ALWAYS=$(shell cd $(FSTAR_HOME) && pwd)/bin/fstar.exe $(OTHERFLAGS) $(HINTS_ENABLED)
FSTAR=$(FSTAR_ALWAYS)

CVEREXE_ALWAYS=$(shell cd $(FSTAR_HOME) && pwd)/bin/fabc-make.exe
CVEREXE=$(CVEREXE_ALWAYS)

DG=$(.DEFAULT_GOAL)

BATCH_TMP:=$(FSTAR_HOME)/tmp
$(BATCH_TMP):
	@mkdir -v $(BATCH_TMP)

BATCH_IDS_FILE:=$(shell mktemp -u -p $(BATCH_TMP))
$(BATCH_IDS_FILE): $(BATCH_TMP)
	$(CVEREXE) create -i $(BATCH_IDS_FILE) 

.DEFAULT_GOAL := $(DG)

CVERCONFIG=$(BATCH_IDS_FILE)
CVERDIR=$(subst $(abspath $(FSTAR_HOME))/,,$(abspath $(shell pwd)))
CVERFSTAR=$(CVEREXE) add -i $(CVERCONFIG) -d 'CURRENT_DIR' -- \$$H/bin/fstar.exe $(OTHERFLAGS) $(HINTS_ENABLED)
