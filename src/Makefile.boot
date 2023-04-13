include Makefile.config

FSTAR_HOME ?= ..

# Provides variables INCLUDE_PATHS, FSTAR_BOOT_OPTIONS,
# and CACHE_DIR, shared with interactive mode targets
include Makefile.boot.common

# This variable can be defined to the path of a different F* binary for
# bootstrapping (and only bootstrapping: the library will be checked
# with the newly-compiled F*). This is useful when developing some
# breaking changes that may not bootstrap. It can be passed as an
# argument to make or via the environment.
FSTAR_BOOT ?= $(FSTAR)

# FSTAR_C: This is the way in which we invoke F* for boostrapping
#   -- we use automatic dependence analysis based on files in ulib, src/{basic, ...} and boot
#   -- MLish and lax tune type-inference for use with unverified ML programs
DUNE_SNAPSHOT ?= $(call maybe_cygwin_path,$(FSTAR_HOME)/ocaml)
OUTPUT_DIRECTORY = $(DUNE_SNAPSHOT)/fstar-lib/generated
FSTAR_C=$(RUNLIM) $(FSTAR_BOOT) $(SIL) $(FSTAR_BOOT_OPTIONS) --cache_checked_modules

# Tests.* goes to fstar-tests, the rest to fstar-lib
OUTPUT_DIRECTORY_FOR = $(if $(findstring FStar_Tests_,$(1)),$(DUNE_SNAPSHOT)/fstar-tests/generated,$(DUNE_SNAPSHOT)/fstar-lib/generated)
FSTAR_C=$(RUNLIM) $(FSTAR_BOOT) $(SIL) $(FSTAR_BOOT_OPTIONS) --cache_checked_modules

# Each "project" for the compiler is in its own namespace.  We want to
# extract them all to OCaml.  Would be more convenient if all of them
# were within, say, FStar.Compiler.*
EXTRACT_NAMESPACES=FStar.Extraction FStar.Parser		\
		   FStar.Reflection FStar.SMTEncoding FStar.Syntax	\
		   FStar.Tactics FStar.Tests FStar.ToSyntax		\
		   FStar.TypeChecker FStar.Profiling

# Except some files that want to extract are not within a particularly
# specific namespace. So, we mention extracting those explicitly.
EXTRACT_MODULES=FStar.Pervasives FStar.Common FStar.Compiler.Range FStar.Thunk		\
		FStar.VConfig FStar.Options FStar.Ident FStar.Errors FStar.Errors.Codes FStar.Const	\
		FStar.Order FStar.Dependencies		\
		FStar.Interactive.CompletionTable			\
		FStar.Interactive.JsonHelper FStar.Interactive.QueryHelper \
		FStar.Interactive.PushHelper FStar.Interactive.Lsp	\
		FStar.Interactive.Ide FStar.Interactive.Ide.Types       \
		FStar.Interactive.Incremental FStar.Interactive.Legacy	\
		FStar.CheckedFiles FStar.Universal FStar.Prettyprint    \
		FStar.Main FStar.Compiler.List FStar.Compiler.Option    \
		FStar.Compiler.Dyn

# And there are a few specific files that should not be extracted at
# all, despite being in one of the EXTRACT_NAMESPACES
NO_EXTRACT=FStar.Tactics.Native FStar.Tactics.Load	\
	   FStar.Extraction.ML.PrintML FStar.Compiler.List

EXTRACT = $(addprefix --extract_module , $(EXTRACT_MODULES))		\
	  $(addprefix --extract_namespace , $(EXTRACT_NAMESPACES))	\
	  $(addprefix --no_extract , $(NO_EXTRACT))

# We first lax type-check each file, producing a .checked.lax file
# We touch the file, because if F* determined that the .checked.lax
# file was already up to date, it doesn't touch it. Touching it here
# ensures that if this rule is successful then %.checked.lax is more
# recent than its dependences.
%.checked.lax:
	$(call msg, "LAXCHECK", $(basename $(basename $(notdir $@))))
	$(Q)$(FSTAR_C) $< --already_cached '*,'-$(basename $(notdir $<))
	$(Q)@touch -c $@

# And then, in a separate invocation, from each .checked.lax we
# extract an .ml file
%.ml:
	$(call msg, "EXTRACT", $(notdir $@))
	$(Q)$(BENCHMARK_PRE) $(FSTAR_C) $(notdir $(subst .checked.lax,,$<)) \
		   --odir "$(call OUTPUT_DIRECTORY_FOR,"$@")" \
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
	$(call msg, "DEPEND")
	$(Q)$(FSTAR_C) --dep full		\
		fstar/FStar.Main.fst		\
		boot/FStar.Tests.Test.fst	\
		--odir $(OUTPUT_DIRECTORY)	\
		$(EXTRACT)			> ._depend
	@# We've generated deps for everything into fstar-lib/generated.
	@# Here we fix up the .depend file to move tests out of the library.
	$(Q)$(SED) 's,fstar-lib/generated/FStar_Test,fstar-tests/generated/FStar_Test,g' <._depend >.depend
	$(Q)mkdir -p $(CACHE_DIR)

depend: .depend

include .depend

all-ml: $(ALL_ML_FILES)
