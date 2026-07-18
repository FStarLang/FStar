FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

SUBDIRS += ns_resolution

$(CACHE_DIR)/MustEraseForExtraction.fst.checked: FSTAR_ARGS += --warn_error @318
FSTAR_ARGS += --warn_error +240
