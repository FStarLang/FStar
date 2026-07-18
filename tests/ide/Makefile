FSTAR_ROOT ?= ../..
SUBDIRS += emacs
include $(FSTAR_ROOT)/mk/test.mk

INCR_TEST_FILES := $(wildcard $(FSTAR_ROOT)/ulib/*.fst  $(FSTAR_ROOT)/ulib/*.fsti)

.PHONY: test_incremental test_ide_without_file
test_incremental: $(patsubst $(FSTAR_ROOT)/ulib/%, %.test-incr, $(INCR_TEST_FILES))

test_ide_without_file:
	$(FSTAR_EXE) --ide TestNoFile.fst < idewithoutfile.in

%.test-incr: $(FSTAR_ROOT)/ulib/%
	$(call msg, "IDE_INCR", $<)
	python3 test-incremental.py $(FSTAR_EXE) $< $(if $(V),,>/dev/null)
	@touch $@

all: test_incremental test_ide_without_file
