# This directory includes files that will be checked *without* a fully
# checked library. They can anyway depend on parts of it (it's hard
# to not depend on Prims) but it will be checked as needed for the
# tests here. Note the --no_prelude by default which means you must
# explicitly open everything, even Prims. Please write tests with as few
# dependencies as possible.


FSTAR_ARGS += --no_prelude
OTHERFLAGS += --already_cached '-Prims,-FStar,-LowStar'  # remove this which test.mk adds by default

FSTAR_ROOT ?= ..
FSTAR_EXE ?= $(abspath $(FSTAR_ROOT)/stage1/dune/_build/default/fstarc-bare/fstarc1_bare.exe)
export FSTAR_LIB ?= $(abspath $(FSTAR_ROOT)/ulib)
include $(FSTAR_ROOT)/mk/test.mk
