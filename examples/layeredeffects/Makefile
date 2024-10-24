OTHERFLAGS+=--already_cached 'Prims FStar LowStar'

FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

all: extraction

HAS_OCAML := $(shell which ocamlfind 2>/dev/null)

ifneq (,$(HAS_OCAML))
extraction:
	$(MAKE) -C extraction
else
extraction:
endif
