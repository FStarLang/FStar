FSTAR_ROOT ?= ../..

SUBDIRS += cmi

# Cross-backend matrix: every language feature and specially-handled
# primitive, extracted, compiled and *run* on OCaml, C and Rust. The C and
# Rust columns need krml and rustc respectively; each is skipped (with a
# message) if its toolchain is missing, so this is safe to run everywhere.
SUBDIRS += backends

# Test for --ext no_krml_private.
SUBDIRS += krml-private

RUN += Eta_expand.fst

# The Div test is based on testing a non-terminating program and
# sending it a signal to interrupt it, which is not well-supported on
# Windows.
ifneq ($(OS),Windows_NT)
RUN += Div.fst
endif

RUN += Division.fst
RUN += ExtractMe.fst
RUN += ExtractAs.fst
RUN += ParseTest.fst

# A precondition is a trailing implicit [squash] binder, and both it and its
# argument are dropped by extraction.  The binder can be hidden inside the
# *instantiated* type of the head, so extracting this at all is the test.
EXTRACT += InstantiatedSpecArgs.fst

# An implicit [squash] *field* is dropped from the extracted record, from the
# constructor's ML type and from every pattern matching on it.  All three have
# to agree, so extract, compile and run.
RUN += SpecFields.fst

# Only the binder a [requires] desugars into is dropped; a user-written
# implicit [squash] binder is an ordinary argument.  Getting that wrong erased
# effectful calls (issue #4650) or dropped an argument the callee still
# expected, so the output is checked against SpecBinderErasure.out.expected.
RUN += SpecBinderErasure.fst

include $(FSTAR_ROOT)/mk/test.mk

all: $(OUTPUT_DIR)/SpecBinderErasure.out.diff
# ...and again through the *legacy* OCaml backend.  [RUN] above goes through
# Custard (mk/test.mk's $(OUTPUT_DIR)/%.ml rule), but the spec-binder dropping
# this test is about lives in FStarC.Extraction.ML.Term, which Custard does not
# use, so the Custard leg alone would not have caught issue #4650.  Both legs
# must print the same thing, so they share the one .expected file.
all: $(OUTPUT_DIR)/SpecBinderErasure.ocaml.diff
$(OUTPUT_DIR)/SpecBinderErasure.ocaml.diff: $(OUTPUT_DIR)/SpecBinderErasure.ocaml.out \
                                            SpecBinderErasure.out.expected
	$(call msg, "DIFF", $<)
	$(Q)bash $(FSTAR_ROOT)/mk/diff.sh $^
	$(Q)touch $@

$(OUTPUT_DIR)/SpecBinderErasure.ocaml.out: $(CACHE_DIR)/SpecBinderErasure.fst.checked
	$(call msg, "EXTRACT (OCaml)", SpecBinderErasure)
	$(Q)$(FSTAR) --codegen OCaml --extract_module SpecBinderErasure $< \
	  --odir $(OUTPUT_DIR)/ocaml
	$(call msg, "OCAMLOPT", SpecBinderErasure)
	$(Q)$(FSTAR_EXE) --ocamlopt $(OUTPUT_DIR)/ocaml/SpecBinderErasure.ml \
	  -o $(OUTPUT_DIR)/SpecBinderErasure.ocaml.exe
	$(call msg, "RUN", SpecBinderErasure)
	$(Q)$(OUTPUT_DIR)/SpecBinderErasure.ocaml.exe > $@

all: $(OUTPUT_DIR)/FloatLiteralExtraction.test
all: $(OUTPUT_DIR)/FloatLiteralInjection.rejected
all: $(OUTPUT_DIR)/NoExtractNorm.test
all: $(OUTPUT_DIR)/NoExtractNormPerf.test

# These four used to drive --codegen krml directly.  Three of them asked a
# question the legacy extractor answered in its *debug output*, and Custard
# answers in the generated program instead; the fourth asked for a diagnostic
# that Custard raises as an error rather than a warning.

# A [noextract] definition must not be normalized -- the legacy pipeline
# normalized every top-level let before deciding whether to keep it, and
# NoExtractNormPerf below is what that costs.  Custard never reaches such a
# definition at all: it is not a root, so there is nothing to normalize and
# nothing to emit.  That is visible in the output, which is a stronger
# statement than the debug line the old test grepped for, so the debug channel
# is no longer involved.
#
# [dropped_to_krml] carries [@@noextract_to "krml"], which names a backend
# other than this one, so it survives here.  The other direction -- the same
# attribute dropping a definition on the C backend -- is
# tests/custard/NoExtractTo, because this module computes on [nat] and C has
# no unbounded integer to compute it with.
$(OUTPUT_DIR)/NoExtractNorm.test: $(CACHE_DIR)/NoExtractNorm.fst.checked $(FSTAR_EXE)
	@mkdir -p $(OUTPUT_DIR)
	$(Q)$(FSTAR) $< --codegen Custard --custard_entry_module NoExtractNorm \
	  -o $(OUTPUT_DIR)/NoExtractNorm.nx.ml
	@grep -q "noExtractNorm_kept" $(OUTPUT_DIR)/NoExtractNorm.nx.ml
	@grep -q "noExtractNorm_dropped_to_krml" $(OUTPUT_DIR)/NoExtractNorm.nx.ml
	@if grep -q "noExtractNorm_dropped " $(OUTPUT_DIR)/NoExtractNorm.nx.ml; then \
	  echo "ERROR: extracted a noextract definition"; false; \
	fi
	@touch $@

# Eighteen levels of [inline_for_extraction noextract], each doubling the
# one below it: unfolding them all is a quarter of a million applications of
# useless work, and the whole module is dropped afterwards.  Custard roots
# nothing here, so this finishes in a tenth of a second; the timeout is what
# makes the test a test.
$(OUTPUT_DIR)/NoExtractNormPerf.test: $(CACHE_DIR)/NoExtractNormPerf.fst.checked $(FSTAR_EXE)
	@mkdir -p $(OUTPUT_DIR)
	$(Q)timeout 60 $(FSTAR) $< --codegen Custard \
	  --custard_entry_module NoExtractNormPerf -o $(OUTPUT_DIR)/NoExtractNormPerf.ml
	@touch $@

# [of_literal] turns its argument into a constant in the generated program,
# which is exactly the shape of a code-injection bug if the argument is not
# checked.  The legacy pipeline warned and emitted the string anyway; Custard
# refuses (error 380, section 39.2), so there is no output to inspect.
$(OUTPUT_DIR)/FloatLiteralInjection.rejected: $(CACHE_DIR)/FloatLiteralInjection.fst.checked $(FSTAR_EXE)
	@mkdir -p $(OUTPUT_DIR)
	@$(FSTAR) $< --codegen Custard --custard_backend C \
	  --custard_entry_module FloatLiteralInjection \
	  -o $(OUTPUT_DIR)/FloatLiteralInjection.c \
	  >$(OUTPUT_DIR)/FloatLiteralInjection.out 2>&1 || true
	@grep -q "Error 380" $(OUTPUT_DIR)/FloatLiteralInjection.out
	@grep -q "is not a floating-point literal" $(OUTPUT_DIR)/FloatLiteralInjection.out
	@touch $@

# And the literals that are well-formed.  The C backend, because the module
# uses FStar.Float32 and OCaml has no binary32 (error 368, section 38).
$(OUTPUT_DIR)/FloatLiteralExtraction.test: $(CACHE_DIR)/FloatLiteralExtraction.fst.checked $(FSTAR_EXE)
	@mkdir -p $(OUTPUT_DIR)
	$(Q)$(FSTAR) $< --codegen Custard --custard_backend C \
	  --custard_entry_module FloatLiteralExtraction \
	  -o $(OUTPUT_DIR)/FloatLiteralExtraction.c
	@grep -q -- "-1250.0" $(OUTPUT_DIR)/FloatLiteralExtraction.c
	@grep -q -- "0.5f" $(OUTPUT_DIR)/FloatLiteralExtraction.c
	@touch $@

# Overriding the default rule for this one. We need to wrap this in a timeout.
$(OUTPUT_DIR)/Div.out: $(OUTPUT_DIR)/Div.exe
	$(call msg,TIMEOUT,$<)
	$(Q)timeout 1 $(OUTPUT_DIR)/Div.exe ; \
	  RC=$$? ;\
	  if ! [ $$RC -eq 124 ]; then echo "ERROR: Div.exe terminated!?!?!"; false; fi
	$(Q)touch $@

# all: inline_let all_cmi Eta_expand.test Div.test ExtractAs.test

# %.exe: %.fst
#         $(FSTAR) --codegen OCaml $<
#         $(OCAMLOPT) -package fstar.lib -linkpkg $(OUTPUT_DIR)/$(patsubst %.fst,%.ml,$<) -o $@

# %.test: %.exe
#         $(call msg,RUN,$<)
#         $(Q)./$<
#         $(Q)touch $@

# Div.test: Div.exe
#         $(call msg,TIMEOUT,$<)
#         $(Q)timeout 1 ./Div.exe ; \
#           RC=$$? ;\
#           if ! [ $$RC -eq 124 ]; then echo "ERROR: Div.exe terminated!?!?!"; false; fi
#         $(Q)touch $@

# inline_let: InlineLet.fst
#         $(FSTAR) --codegen OCaml InlineLet.fst
#         egrep -A 10 test $(OUTPUT_DIR)/InlineLet.ml | grep -qs "17"
#         @touch $@

# all_cmi:
#         +$(MAKE) -C cmi all

# clean:
#         rm -rf out
#         rm -f *.exe
#         rm -f *~
#         rm -f *.exe *.test
#         rm -f inline_let
