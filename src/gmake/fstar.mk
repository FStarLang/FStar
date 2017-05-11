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

BATCH_TMP=$(shell cd $(FSTAR_HOME) && pwd)/tmp
$(BATCH_TMP):
	mkdir -v $(BATCH_TMP)

FABC_HINTS?="-h $(FSTAR_HOME)"

CURRENT_SUBDIR:=$(subst $(abspath $(FSTAR_HOME))/,,$(abspath $(shell pwd)))

.PHONY : CVERCONFIG
CVERCONFIG: $(BATCH_TMP)
ifndef BATCH_IDS_FILE_ABS
	$(eval export BATCH_IDS_FILE_ABS:=$(shell mktemp -p $(BATCH_TMP)))
	$(eval export BATCH_IDS_FILE:=$(shell realpath --relative-to=. $(BATCH_IDS_FILE_ABS)))
	$(CVEREXE) create $(FABC_EXTRA) -i $(BATCH_IDS_FILE)
else
$(eval export BATCH_IDS_FILE:=$(shell realpath --relative-to=. $(BATCH_IDS_FILE_ABS)))
endif

CFSTAR=$(CVEREXE) add -i $$BATCH_IDS_FILE -d '$(CURRENT_SUBDIR)' $(FABC_EXTRA) -- $(subst $(abspath $(FSTAR_HOME)),\$$H,$(FSTAR))

.DEFAULT_GOAL := $(DG)
