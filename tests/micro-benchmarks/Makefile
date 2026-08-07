FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

SUBDIRS += ns_resolution

# These definitions agree with the erasability their interface declares, so
# none of them may raise 318. The cases that do are in tests/interfaces.
$(CACHE_DIR)/MustEraseForExtraction.fst.checked: FSTAR_ARGS += --warn_error @318
FSTAR_ARGS += --warn_error +240
