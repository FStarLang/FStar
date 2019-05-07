include Makefile.config

INCLUDE_PATHS = \
	../ulib \
	boot \
	basic \
	extraction \
	fsdoc \
	fstar \
	parser \
	prettyprint \
	reflection \
	smtencoding \
	syntax \
	tactics \
	tosyntax \
	typechecker \
	tests

CACHE_DIR?=./.cache.boot

FSTAR_BOOT ?= $(FSTAR)

# FSTAR_C: This is the way in which we invoke F* for boostrapping
#   -- we use automatic dependence analysis based on files in ulib, src/{basic, ...} and boot
#   -- MLish and lax tune type-inference for use with unverified ML programs
FSTAR_C=$(FSTAR_BOOT) $(OTHERFLAGS) --cache_checked_modules		\
	--use_extracted_interfaces false                                \
	--lax --MLish --no_location_info				\
	--odir ocaml-output $(addprefix --include , $(INCLUDE_PATHS))	\
	--warn_error -272-241-319 --cache_dir $(CACHE_DIR)

# Each "project" for the compiler is in its own namespace.  We want to
# extract them all to OCaml.  Would be more convenient if all of them
# were within, say, FStar.Compiler.*
EXTRACT_NAMESPACES=FStar.Extraction FStar.Fsdoc FStar.Parser		\
		   FStar.Reflection FStar.SMTEncoding FStar.Syntax	\
		   FStar.Tactics FStar.Tests FStar.ToSyntax		\
		   FStar.TypeChecker

# Except some files that want to extract are not within a particularly
# specific namespace. So, we mention extracting those explicitly.
EXTRACT_MODULES=FStar.Pervasives FStar.Common FStar.Range		\
		FStar.Options FStar.Ident FStar.Errors FStar.Const	\
		FStar.Order FStar.Dependencies		\
		FStar.Interactive.CompletionTable			\
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
	$(FSTAR_C) $< --already_cached "* -$(basename $(notdir $<))"
	touch $@

# And then, in a separate invocation, from each .checked.lax we
# extract an .ml file
ocaml-output/%.ml:
	$(FSTAR_C) $(notdir $(subst .checked.lax,,$<)) \
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
	$(FSTAR_C) --dep full                 \
		   fstar/FStar.Main.fs	      \
		   boot/FStar.Tests.Test.fst  \
		   $(EXTRACT)		      > ._depend
	mv ._depend .depend
	mkdir -p $(CACHE_DIR)

depend: .depend

include .depend

all-ml: $(ALL_ML_FILES)
