HINTS_ENABLED?=--use_hints
WARN_ERROR=
OTHERFLAGS+=$(WARN_ERROR)

ifdef Z3
OTHERFLAGS+=--smt $(Z3)
endif

# Set ADMIT=1 to admit queries
ADMIT ?=
MAYBE_ADMIT = $(if $(ADMIT),--admit_smt_queries true)

ifdef FSTAR_HOME
  FSTAR_HOME := $(realpath $(FSTAR_HOME))
  ifeq ($(OS),Windows_NT)
    FSTAR_HOME := $(shell cygpath -m $(FSTAR_HOME))
  endif
  FSTAR_EXE?=$(FSTAR_HOME)/out/bin/fstar.exe
else
# FSTAR_HOME not defined, assume fstar.exe reachable from PATH
FSTAR_EXE?=fstar.exe
endif

FSTAR=$(FSTAR_EXE) $(OTHERFLAGS) $(MAYBE_ADMIT) $(HINTS_ENABLED) $(WITH_CACHE_DIR)
