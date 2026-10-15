# Negative tests for compilation targets.  These drive fstar.exe file by
# file, since each one is expected to fail.

FSTAR_ROOT ?= ../../..
FSTAR_EXE ?= $(FSTAR_ROOT)/out/bin/fstar.exe
FSTAR_EXE := $(abspath $(FSTAR_EXE))

CACHE_DIR := _cache

FSTAR = $(FSTAR_EXE) --message_format human --cache_dir $(CACHE_DIR) --include .. --include ../_cache \
	--already_cached Prims,FStar $(OTHERFLAGS)

all: verify

# Each file is expected to fail with the given message (matched after joining
# wrapped lines).
define expect_error
	! $(FSTAR) $(1) > $(CACHE_DIR)/$(basename $(1)).log 2>&1
	tr -s ' \n' '  ' < $(CACHE_DIR)/$(basename $(1)).log | grep -q '$(2)'
endef

verify:
	mkdir -p $(CACHE_DIR)
	$(call expect_error,BadFriend.fst,BadFriend.fst (a common file) uses the implementation of module Counter. but none applies)
	$(call expect_error,UseTargetOnly.fst,OcamlOnly)
	$(call expect_error,UseUnfixed-s2.fst,Unfixed-s2.qemu.fst would apply in target s2.qemu)
	$(call expect_error,FriendUart-s2.fst,FriendUart-s2.fst (target s2) uses the implementation of module Uart from Uart-s2.fst.*Uart-s2.qemu.fst would apply in target s2.qemu)
	$(call expect_error,UseAmb-c-s2.fst,implementation of module Amb is ambiguous)
	$(call expect_error,Own-s2.fst,Own-s2.qemu.fsti would apply in target s2.qemu)

accept depend:

clean:
	rm -rf $(CACHE_DIR)

.PHONY: all verify accept depend clean
