HINTS_ENABLED?=--use_hints --use_hint_hashes
WARN_ERROR=
OTHERFLAGS+=$(WARN_ERROR) --z3cliopt 'timeout=600000' --smtencoding.valid_intro true --smtencoding.valid_elim true

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

ORUN?=orun
