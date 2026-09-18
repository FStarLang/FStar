OTHERFLAGS += --ext fstar:no_absolute_paths

PULSE_ROOT ?= ../..
include $(PULSE_ROOT)/mk/test.mk

# Both C tests here return a Prims.int, which the direct backend has no
# representation for; see ../Makefile.
CUSTARD_KRML_C += Bug166
CUSTARD_KRML_C += ExtractPulseFnIface

include $(PULSE_ROOT)/mk/custard-test.mk
