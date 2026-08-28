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

include $(FSTAR_ROOT)/mk/test.mk

all: $(OUTPUT_DIR)/FloatLiteralExtraction.krml
all: $(OUTPUT_DIR)/FloatLiteralInjection.rejected
all: $(OUTPUT_DIR)/NoExtractNorm.test
all: $(OUTPUT_DIR)/NoExtractNormPerf.test

$(OUTPUT_DIR)/NoExtractNorm.test: $(CACHE_DIR)/NoExtractNorm.fst.checked $(FSTAR_EXE)
	@mkdir -p $(OUTPUT_DIR)
	@$(FSTAR) $< --codegen krml --extract_module NoExtractNorm --debug ExtractionNorm >$(OUTPUT_DIR)/NoExtractNorm.out 2>&1
	@grep -q "Starting to normalize top-level let Inr kept" $(OUTPUT_DIR)/NoExtractNorm.out
	@if grep -q "Starting to normalize top-level let Inr dropped" $(OUTPUT_DIR)/NoExtractNorm.out; then \
	  echo "ERROR: normalized a noextract definition"; false; \
	fi
	@touch $@

$(OUTPUT_DIR)/NoExtractNormPerf.test: $(CACHE_DIR)/NoExtractNormPerf.fst.checked $(FSTAR_EXE)
	@mkdir -p $(OUTPUT_DIR)
	@$(FSTAR) $< --codegen krml --extract_module NoExtractNormPerf
	@touch $@

$(OUTPUT_DIR)/FloatLiteralInjection.rejected: $(CACHE_DIR)/FloatLiteralInjection.fst.checked $(FSTAR_EXE)
	@mkdir -p $(OUTPUT_DIR)
	@$(FSTAR) $< --codegen krml --extract_module FloatLiteralInjection >$(OUTPUT_DIR)/FloatLiteralInjection.out 2>&1 || true
	@grep -q "Warning 242" $(OUTPUT_DIR)/FloatLiteralInjection.out
	@grep -q "Refusing to extract invalid Float64.of_literal argument" $(OUTPUT_DIR)/FloatLiteralInjection.out
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
