SUBDIRS += ns_resolution

OTHERFLAGS+=--warn_error +240

FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

$(CACHE_DIR)/MustEraseForExtraction.fst.checked: OTHERFLAGS += --warn_error @318
