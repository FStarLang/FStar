HINTS_ENABLED?=--use_hints --use_hint_hashes
PROTECT_TOP_LEVEL_AXIOMS?=--protect_top_level_axioms true
WARN_ERROR=--warn_error +9 --warn_error +16 --warn_error +19
OTHERFLAGS+=$(PROTECT_TOP_LEVEL_AXIOMS) $(WARN_ERROR) --z3cliopt 'timeout=180000'

ifdef Z3
OTHERFLAGS+=--smt $(Z3)
endif

ifdef FSTAR_HOME
FSTAR_ALWAYS=$(shell cd $(FSTAR_HOME) && pwd)/bin/fstar.exe $(OTHERFLAGS) $(HINTS_ENABLED)
FSTAR=$(FSTAR_ALWAYS)
else
# FSTAR_HOME not defined, assume fstar.exe reachable from PATH
FSTAR=fstar.exe $(OTHERFLAGS) $(HINTS_ENABLED)
endif
