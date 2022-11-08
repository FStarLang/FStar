# This makefile is included from several other makefiles in the tree.
# Its only purpose is to enable configurably 'silent' rules, that do not
# print output unless V=1 is set. When writing a rule, you can do as
# follows (taken from src/Makefile.boot):
#
# ocaml-output/%.ml:
# 	@echo "[EXTRACT   $(notdir $@)]"
# 	$(Q)$(BENCHMARK_PRE) $(FSTAR_C) $(SIL) $(notdir $(subst .checked.lax,,$<)) \
#                   --codegen OCaml \
#                   --extract_module $(basename $(notdir $(subst .checked.lax,,$<)))
#
# This unconditionally prints a message like '[EXTRACT FStar_Syntax_Subst.ml]'
# (`notdir` is used to omit the directory of the target) and then
# proceeds to execute the F* invocation silently (since $(Q) expands to
# "@"). However, calling the same rule with `make V=1` will still print
# the message and then print the F* invocation before executing.
#
# Besides that, when not using V=1, F* receives the --silent flag to
# reduce non-critical output.
#
# It would be nice to define a function to print messages instead of
# copying the same echo invocation everywhere, but AFAIK that would mean
# we require GNU make.

Q?=@
SIL?=--silent
PREF=
ifneq ($(V),)
	Q=
	SIL=
endif

# Passing MON=1 will create .runlim files through the source tree with
# information about the time and space taken by each F* invocation.
ifneq ($(MON),)
	PREF=runlim -p -o $@.runlim
endif
