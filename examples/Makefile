SUBDIRS += algorithms
SUBDIRS += data_structures
SUBDIRS += dsls
SUBDIRS += layeredeffects
SUBDIRS += metatheory
SUBDIRS += misc
SUBDIRS += oplss2021
SUBDIRS += paradoxes
SUBDIRS += param

SUBDIRS += printf
SUBDIRS += software_foundations
SUBDIRS += tactics
SUBDIRS += termination
SUBDIRS += typeclasses
SUBDIRS += verifythis

# SUBDIRS += sample_project # requires fstar.exe in the PATH!?!?

# These have custom makefiles

SUBDIRS_ALL += hello
SUBDIRS_CLEAN += hello

SUBDIRS_ALL += dependencies
SUBDIRS_CLEAN += dependencies

HAS_OCAML ?= 1
ifneq (,$(HAS_OCAML))
SUBDIRS_ALL += native_tactics
endif
SUBDIRS_CLEAN += native_tactics

FSTAR_ROOT ?= ..
include $(FSTAR_ROOT)/mk/test.mk

# F# tests live in fsharp/tests/ and are run via `make fsharp-lib`
