# Negative tests for compilation targets.  These drive fstar.exe file by
# file, since each one is expected to fail.

FSTAR_ROOT ?= ../../..
FSTAR_EXE ?= $(FSTAR_ROOT)/out/bin/fstar.exe
FSTAR_EXE := $(abspath $(FSTAR_EXE))

CACHE_DIR := _cache

FSTAR = $(FSTAR_EXE) --cache_dir $(CACHE_DIR) --include .. --include ../_cache \
	--already_cached Prims,FStar $(OTHERFLAGS)

all: verify

# Common code can neither befriend a module that only has target-specific
# implementations, nor see a module that only exists for some target.  A
# module cannot have both a common and a target-specific implementation.
verify:
	mkdir -p $(CACHE_DIR)
	! $(FSTAR) BadFriend.fst > $(CACHE_DIR)/BadFriend.log 2>&1
	grep -q 'Expected an implementation of module counter' $(CACHE_DIR)/BadFriend.log
	! $(FSTAR) UseTargetOnly.fst > $(CACHE_DIR)/UseTargetOnly.log 2>&1
	grep -q 'OcamlOnly' $(CACHE_DIR)/UseTargetOnly.log
	! $(FSTAR) --dep full conflict/Dup.fst conflict/Dup-ocaml.fst > $(CACHE_DIR)/Dup.log 2>&1
	grep -q 'has both a common implementation' $(CACHE_DIR)/Dup.log

accept depend:

clean:
	rm -rf $(CACHE_DIR)

.PHONY: all verify accept depend clean
