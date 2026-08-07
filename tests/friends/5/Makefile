# Regression test for #4399.
#
# Checking B.fst, which befriends A, used to rewrite an already valid
# B.fsti.checked with different (though equally valid) contents. That
# silently invalidated every module, such as C, that had already been
# checked against the previous B.fsti.checked.
#
# This test drives the individual files in the same order a parallel `make`
# would, so it cannot use the generic mk/test.mk rules.

FSTAR_ROOT ?= ../../..
FSTAR_EXE ?= $(FSTAR_ROOT)/out/bin/fstar.exe
FSTAR_EXE := $(abspath $(FSTAR_EXE))

CACHE_DIR := _cache

FSTAR = $(FSTAR_EXE) --cache_dir $(CACHE_DIR) --include . --include $(CACHE_DIR) \
	--already_cached Prims,FStar --cache_checked_modules --warn_error @241 \
	$(OTHERFLAGS)

all: verify

verify:
	rm -rf $(CACHE_DIR)
	mkdir -p $(CACHE_DIR)
	$(FSTAR) A.fsti
	$(FSTAR) A.fst
	$(FSTAR) B.fsti
	cp $(CACHE_DIR)/B.fsti.checked $(CACHE_DIR)/B.fsti.checked.bak
#	C is legally checked against the B.fsti.checked just produced.
	$(FSTAR) C.fst
#	Building B.fst must leave B.fsti.checked alone.
	$(FSTAR) B.fst
	cmp $(CACHE_DIR)/B.fsti.checked.bak $(CACHE_DIR)/B.fsti.checked
#	And so C.fst.checked must still be loadable.
	$(FSTAR) D.fst

accept depend:

clean:
	rm -rf $(CACHE_DIR)

.PHONY: all verify accept depend clean
