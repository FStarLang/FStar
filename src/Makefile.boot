include Makefile.config

FSTAR_HOME ?= ..

# Provides variables INCLUDE_PATHS, FSTAR_BOOT_OPTIONS,
# and CACHE_DIR, shared with interactive mode targets
include Makefile.boot.common

FSTAR_BOOT ?= $(FSTAR)

# FSTAR_C: This is the way in which we invoke F* for boostrapping
#   -- we use automatic dependence analysis based on files in ulib, src/{basic, ...} and boot
#   -- MLish and lax tune type-inference for use with unverified ML programs
FSTAR_C=$(FSTAR_BOOT) $(FSTAR_BOOT_OPTIONS) --cache_checked_modules --odir ocaml-output

# Each "project" for the compiler is in its own namespace.  We want to
# extract them all to OCaml.  Would be more convenient if all of them
# were within, say, FStar.Compiler.*
EXTRACT_NAMESPACES=FStar.Extraction FStar.Parser		\
		   FStar.Reflection FStar.SMTEncoding FStar.Syntax	\
		   FStar.Tactics FStar.Tests FStar.ToSyntax		\
		   FStar.TypeChecker FStar.Profiling

# Except some files that want to extract are not within a particularly
# specific namespace. So, we mention extracting those explicitly.
EXTRACT_MODULES=FStar.Pervasives FStar.Common FStar.Range FStar.Thunk		\
		FStar.VConfig FStar.Options FStar.Ident FStar.Errors FStar.Const	\
		FStar.Order FStar.Dependencies		\
		FStar.Interactive.CompletionTable			\
		FStar.Interactive.JsonHelper FStar.Interactive.QueryHelper \
		FStar.Interactive.PushHelper FStar.Interactive.Lsp	\
		FStar.Interactive.Ide FStar.Interactive.Legacy		\
		FStar.CheckedFiles FStar.Universal FStar.Prettyprint    \
		FStar.Main

# And there are a few specific files that should not be extracted at
# all, despite being in one of the EXTRACT_NAMESPACES
NO_EXTRACT=FStar.Tactics.Native FStar.Tactics.Load	\
	   FStar.Extraction.ML.PrintML

EXTRACT = $(addprefix --extract_module , $(EXTRACT_MODULES))		\
	  $(addprefix --extract_namespace , $(EXTRACT_NAMESPACES))	\
	  $(addprefix --no_extract , $(NO_EXTRACT))

# We first lax type-check each file, producing a .checked.lax file
# We touch the file, because if F* determined that the .checked.lax
# file was already up to date, it doesn't touch it. Touching it here
# ensures that if this rule is successful then %.checked.lax is more
# recent than its dependences.
%.checked.lax:
	@echo "[LAXCHECK  $(basename $(basename $(notdir $@)))]"
	$(Q)$(FSTAR_C) $(SIL) $< --already_cached "* -$(basename $(notdir $<))"
	$(Q)@touch -c $@

# And then, in a separate invocation, from each .checked.lax we
# extract an .ml file
ocaml-output/%.ml:
	@echo "[EXTRACT   $(notdir $@)]"
	$(Q)$(BENCHMARK_PRE) $(FSTAR_C) $(SIL) $(notdir $(subst .checked.lax,,$<)) \
                   --codegen OCaml \
                   --extract_module $(basename $(notdir $(subst .checked.lax,,$<)))

# --------------------------------------------------------------------
# Dependency analysis for bootstrapping
# --------------------------------------------------------------------

# The dependence analysis starts from the main file and the unit-tests
# file as the roots, mentioning the the modules that are to be
# extracted. This emits dependences for each of the ML files we want
# to produce.
#
# We do an indirection via ._depend so we don't write an empty file if
# the dependency analysis failed.

.depend:
	@echo "[DEPEND]"
	$(Q)$(FSTAR_C) $(SIL) --dep full	\
		fstar/FStar.Main.fs		\
		boot/FStar.Tests.Test.fst	\
		$(EXTRACT)			> ._depend
	$(Q)mv ._depend .depend
	$(Q)mkdir -p $(CACHE_DIR)

depend: .depend

include .depend

all-ml: $(ALL_ML_FILES)
