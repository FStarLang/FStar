FSTAR_HOME=../../..

FSTAR=$(FSTAR_HOME)/bin/fstar.exe

HINTS_ENABLED?=--use_hints

OPTIONS=--fstar_home $(FSTAR_HOME) --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3timeout 20  $(HINTS_ENABLED)

FSTAR_INCLUDE_PATHS=--include $(FSTAR_HOME)/ulib/hyperheap --include $(FSTAR_HOME)/ucontrib/Platform/fst

# Parameter for interactive mode
%.fst-in: 
	@echo $(OPTIONS) \
	$(FSTAR_INCLUDE_PATHS) \
	--verify_module $(basename $(notdir $@))

# Verifying one file at a time
%.fst-ver:
	$(FSTAR) $(OPTIONS) \
	$(FSTAR_INCLUDE_PATHS) \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst
