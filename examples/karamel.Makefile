# Karamel tests.
SUBDIRS += demos
SUBDIRS += miniparse
SUBDIRS_ALL += kv_parsing
SUBDIRS_CLEAN += kv_parsing

FSTAR_ROOT ?= ..
include $(FSTAR_ROOT)/mk/test.mk
