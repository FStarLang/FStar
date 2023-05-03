FSTAR_HOME=../..
include ../../examples/Makefile.include

ALL_TEST_DIRS=\
lsp \
emacs

all: $(addsuffix .all, $(ALL_TEST_DIRS)) # test_incremental WIP! RESTORE!

INCR_TEST_FILES := $(wildcard $(FSTAR_HOME)/ulib/*.fst  $(FSTAR_HOME)/ulib/*.fsti)

.PHONY: test_incremental
test_incremental: $(patsubst %, %.test-incr, $(INCR_TEST_FILES))

%.test-incr: %
	$(Q)python test-incremental.py $(FSTAR_HOME)/bin/fstar.exe $<

clean: $(addsuffix .clean, $(ALL_TEST_DIRS))

%.all: %
	+$(MAKE) -C $^ all

%.clean: %
	+$(MAKE) -C $^ clean
