FSTAR_HOME=../..
include ../../examples/Makefile.include

ALL_TEST_DIRS=\
lsp \
emacs

all: $(addsuffix .all, $(ALL_TEST_DIRS)) test_incremental

INCR_TEST_FILES := $(wildcard $(FSTAR_HOME)/ulib/*.fst  $(FSTAR_HOME)/ulib/*.fsti)

.PHONY: test_incremental
test_incremental: $(patsubst $(FSTAR_HOME)/ulib/%, %.test-incr, $(INCR_TEST_FILES))

%.test-incr: $(FSTAR_HOME)/ulib/%
	$(call msg, "IDE_INCR", $<)
	$(Q)python3 test-incremental.py $(FSTAR_HOME)/bin/fstar.exe $< $(if $(V),,>/dev/null)
	@touch $@

clean: $(addsuffix .clean, $(ALL_TEST_DIRS))

%.all: %
	+$(MAKE) -C $^ all

%.clean: %
	+$(MAKE) -C $^ clean
