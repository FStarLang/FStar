include Makefile.config

# This is the way in which we invoke F* for boostrapping
#   -- we use automatic dependence analysis based on files in ulib, src/{basic, ...} and boot
#   -- eager_inference, MLish, lax: all tune type-inference for use with unverified ML programs
INCLUDE_PATHS = \
	../ulib \
	boot \
	basic \
	extraction \
	format \
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

FSTAR_C=$(FSTAR) $(OTHERFLAGS) --cache_checked_modules --eager_inference --lax --MLish --no_location_info \
		   --odir ocaml-output $(addprefix --include , $(INCLUDE_PATHS))

EXTRACT_MODULES=FStar.Pervasives FStar.Common FStar.Range		\
		FStar.Options FStar.Ident FStar.Errors FStar.Const	\
		FStar.Format FStar.Order FStar.Dependencies		\
		FStar.Interactive.CompletionTable			\
		FStar.Interactive.Ide FStar.Interactive.Legacy		\
		FStar.Universal FStar.Indent FStar.Main

EXTRACT_NAMESPACES=FStar.Extraction FStar.Fsdoc FStar.Parser		\
		   FStar.Reflection FStar.SMTEncoding FStar.Syntax	\
		   FStar.Tactics FStar.Tests FStar.ToSyntax		\
		   FStar.TypeChecker

NO_EXTRACT=FStar.Tactics.Native FStar.Tactics.Load	\
           FStar.Extraction.ML.PrintML

EXTRACT = $(addprefix --extract_module , $(EXTRACT_MODULES))		\
	  $(addprefix --extract_namespace , $(EXTRACT_NAMESPACES))	\
	  $(addprefix --no_extract , $(NO_EXTRACT))


%.checked.lax: %
	$(FSTAR_C) $*
	touch $@

ocaml-output/%.ml:
	$(FSTAR_C) $(subst .checked.lax,,$<) --codegen OCaml --extract_module $(basename $(notdir $(subst .checked.lax,,$<)))

# --------------------------------------------------------------------
# Dependency analysis for bootstrapping
# --------------------------------------------------------------------

.depend:
	$(FSTAR_C) --dep full fstar/FStar.Main.fs boot/FStar.Tests.Test.fst $(EXTRACT) --codegen OCaml > .depend

depend: .depend

include .depend

all-ml: $(ALL_ML_FILES)
