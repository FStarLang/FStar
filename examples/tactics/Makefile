# Poly files are here for benchmarking, and expected to fail without tactics
EXCLUDED_FSTAR_FILES=Launch.fst Poly1.fst Poly2.fst
SUBDIRS += eci19
FSTAR_FILES = $(filter-out $(EXCLUDED_FSTAR_FILES), $(wildcard *.fst))

ifndef KRML_HOME
  EXCLUDED_FSTAR_FILES += $(wildcard StringPrinter*)
endif
ifdef KRML_HOME
OTHERFLAGS += --include $(KRML_HOME)/krmllib
endif

FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

ifdef KRML_HOME
stringprintertest: $(CACHE_DIR)
	 [ ! -f $(KRML_HOME)/krml ] || [ ! -x $(KRML_HOME)/krml ] || $(KRML_HOME)/krml -tmpdir stringprintertest -bundle 'StringPrinter.\*' -bundle StringPrinterTest.Aux -drop 'FStar.Tactics.\*' -drop 'FStar.Reflection.\*' StringPrinterTest.fst -skip-linking
else
stringprintertest:
endif
