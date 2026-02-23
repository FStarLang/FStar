rel.__all: dm4free.__verify
rel.__accept: dm4free.__verify
rel.__verify: dm4free.__verify
# ^ rel uses modules from dm4free, make sure to check them in proper
# order.

SUBDIRS += algorithms
SUBDIRS += crypto
SUBDIRS += data_structures
SUBDIRS += dm4free
SUBDIRS += dsls
SUBDIRS += indexed_effects
SUBDIRS += layeredeffects
SUBDIRS += metatheory
SUBDIRS += misc
SUBDIRS += oplss2021
SUBDIRS += paradoxes
SUBDIRS += param
SUBDIRS += preorders
SUBDIRS += printf
SUBDIRS += rel
SUBDIRS += software_foundations
SUBDIRS += tactics
SUBDIRS += termination
SUBDIRS += typeclasses
SUBDIRS += verifythis

# SUBDIRS += sample_project # requires fstar.exe in the PATH!?!?

# These have custom makefiles

# hello has its F# extraction broken, and the dune/ocamlopt variants can
# be found in tests/simple_hello and tests/dune_hello, so I'm disabling
# this.
# SUBDIRS_ALL += hello
# SUBDIRS_CLEAN += hello
SUBDIRS_ALL += dependencies
SUBDIRS_CLEAN += dependencies

HAS_OCAML ?= 1
ifneq (,$(HAS_OCAML))
SUBDIRS_ALL += native_tactics
endif
SUBDIRS_CLEAN += native_tactics

FSTAR_ROOT ?= ..
include $(FSTAR_ROOT)/mk/test.mk
