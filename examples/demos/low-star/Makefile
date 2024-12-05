FSTAR_ROOT ?= ../../..
include $(FSTAR_ROOT)/mk/test.mk

ifneq ($(KRML_HOME),)
KRML = $(KRML_HOME)/krml
else
KRML = krml
endif

extract:
	$(KRML) -skip-compilation Demo.fst -tmpdir $(OUTPUT_DIR) | grep "wrote out"

extract-tailcalls:
	$(KRML) -skip-compilation -ftail-calls Demo.fst -tmpdir $(OUTPUT_DIR) | grep "wrote out"
