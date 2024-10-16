FSTAR_ROOT ?= ../..
NODEPEND=1
include $(FSTAR_ROOT)/mk/test.mk

ALL_TEST_DIRS += lsp
ALL_TEST_DIRS += emacs

all: $(addsuffix .all, $(ALL_TEST_DIRS)) test_incremental
clean: $(addsuffix .clean, $(ALL_TEST_DIRS))

INCR_TEST_FILES := $(wildcard $(FSTAR_ROOT)/ulib/*.fst  $(FSTAR_ROOT)/ulib/*.fsti)

.PHONY: test_incremental
test_incremental: $(patsubst $(FSTAR_ROOT)/ulib/%, %.test-incr, $(INCR_TEST_FILES))

%.test-incr: $(FSTAR_ROOT)/ulib/%
	$(call msg, "IDE_INCR", $<)
	$(Q)python3 test-incremental.py $(FSTAR_EXE) $< $(if $(V),,>/dev/null)
	@touch $@

%.all: %
	+$(MAKE) -C $^ all

%.clean: %
	+$(MAKE) -C $^ clean
