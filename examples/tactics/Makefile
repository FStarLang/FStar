# Poly files are here for benchmarking, and expected to fail without tactics
EXCLUDED_FSTAR_FILES=Launch.fst Poly1.fst Poly2.fst
SUBDIRS += eci19
FSTAR_FILES = $(filter-out $(EXCLUDED_FSTAR_FILES), $(wildcard *.fst))

# The StringPrinter demo extracts to C and needs Karamel's krmllib to verify
# and the krml executable to extract. Only enable it when a Karamel executable
# is provided in KRML_EXE (checked before mk/test.mk sets a default value).
ifdef KRML_EXE
HAVE_KRML := 1
endif

ifndef HAVE_KRML
  EXCLUDED_FSTAR_FILES += $(wildcard StringPrinter*)
endif
ifdef HAVE_KRML
OTHERFLAGS += --include "$(shell "$(KRML_EXE)" -locate-krmllib)"
endif

FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

ifdef HAVE_KRML
stringprintertest: $(CACHE_DIR)
	 [ ! -f "$(KRML_EXE)" ] || [ ! -x "$(KRML_EXE)" ] || "$(KRML_EXE)" -tmpdir stringprintertest -bundle 'StringPrinter.\*' -bundle StringPrinterTest.Aux -drop 'FStar.Tactics.\*' -drop 'FStar.Reflection.\*' StringPrinterTest.fst -skip-linking
else
stringprintertest:
endif
