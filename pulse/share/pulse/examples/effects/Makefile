# Build the complete effects demonstration: library, verified examples, extracted
# OCaml entry point, linked driver, and recorded execution result. Default `make`
# runs only out-of-date stages; `make run` explicitly executes the driver again.
# verify, extract, build, and clean are also available independently.
# All generated example artifacts stay here; the library owns a separate cache.
# See README.md for scenario coverage and the expected rebuild behavior.

# Locate the shared Pulse build rules from this example directory.
PULSE_ROOT ?= ../../../..
# Use absolute library paths so the recursive make and parent refer to the same
# output files, rather than unrelated relative target names.
EFFECTS_LIB := $(abspath $(PULSE_ROOT)/lib/pulse/lib/effects)
# The library build owns these checked modules; do not copy them into our cache.
EFFECTS_CACHE := $(EFFECTS_LIB)/_cache
# Prefer the development's source and checked files to installed effects copies.
OTHERFLAGS += --include $(EFFECTS_LIB) --include $(CACHE_DIR) --include $(EFFECTS_CACHE)
# Keep proof effort aligned with the library and the two editor configurations.
OTHERFLAGS += --z3rlimit 10
# Pulse.Main is an installed prerequisite, not another module to rebuild here.
OTHERFLAGS += --already_cached Pulse.Main
# Verify every authored example, including expected-failure tests not extracted.
FSTAR_FILES := $(wildcard *.fst) $(wildcard *.fsti)
# Local outputs also depend on this Makefile, since it supplies checking options.
EXAMPLE_CHECKED = $(addprefix $(CACHE_DIR)/,$(addsuffix .checked,$(FSTAR_FILES)))
# Track library implementations as well as interfaces: changing a hidden body
# must invalidate extraction even when client verification remains current.
EFFECTS_CHECKED := $(addprefix $(EFFECTS_CACHE)/,$(addsuffix .checked,$(notdir $(wildcard $(EFFECTS_LIB)/*.fst) $(wildcard $(EFFECTS_LIB)/*.fsti))))

# Reuse compiler discovery, F*-generated example dependencies, verify, and clean.
include $(PULSE_ROOT)/mk/test.mk

# Narrow test.mk's blanket .SECONDARY: missing runtime artifacts must rebuild.
.SECONDARY: $(EXAMPLE_CHECKED)

# Refresh each output's timestamp after the recursive make: an order-only
# prerequisite would let make retain timestamps from before that build.
# This phony gate runs the library make once per parent make pass; the library's
# own timestamp checks decide whether any verification is actually necessary.
.PHONY: effects-lib
effects-lib:
	$(MAKE) -C $(EFFECTS_LIB) PULSE_ROOT=$(abspath $(PULSE_ROOT)) CACHE_DIR=$(EFFECTS_CACHE) OUTPUT_DIR=$(EFFECTS_LIB)/_output verify

# Generate dependencies only after the local library is available. Also notice
# Makefile changes and changes to the set of files in this directory.
.depend: Makefile . $(EFFECTS_CHECKED) | $(CACHE_DIR) $(OUTPUT_DIR)
$(EXAMPLE_CHECKED): Makefile $(FSTAR_EXE)
# Probe each output after the submake so the parent refreshes its cached mtime.
# This recipe does not touch the file: unchanged library outputs stay unchanged.
$(EFFECTS_CHECKED): effects-lib
	test -f $@

# Create generated-file directories before dependency analysis, without making
# ordinary cache writes invalidate all downstream targets.
$(CACHE_DIR) $(OUTPUT_DIR):
	mkdir -p $@

# Extract one closed runtime entry. Runtime's checked dependency chain covers
# its example callees; explicit library outputs cover hidden implementations.
# Rejected.fst is verified separately and does not require re-extracting this code.
$(OUTPUT_DIR)/Effects_runtime.ml: $(CACHE_DIR)/Example.Effects.Runtime.fst.checked $(EFFECTS_CHECKED) Makefile
	$(FSTAR) --codegen OCaml --custard_entry Example.Effects.Runtime.test $< -o $@

# Compile/link the generated module and the external observation checker.
# Copying the driver keeps OCaml's auxiliary compilation files out of the source
# directory; editing only driver.ml need not reverify or re-extract F*.
$(OUTPUT_DIR)/effects.exe: $(OUTPUT_DIR)/Effects_runtime.ml driver.ml Makefile
	cp driver.ml $(OUTPUT_DIR)/
	cd $(OUTPUT_DIR) && $(FSTAR_EXE) --ocamlopt -I . Effects_runtime.ml driver.ml -o effects.exe

# Record a successful execution. The common .DELETE_ON_ERROR rule removes a
# partial output on failure; an unchanged executable need not run again by default.
$(OUTPUT_DIR)/effects.out: $(OUTPUT_DIR)/effects.exe
	$(call msg, "RUN", $(notdir $<))
	$< > $@
	cat $@

.PHONY: extract build run
# Stop after producing the extracted OCaml module.
extract: $(OUTPUT_DIR)/Effects_runtime.ml
# Produce the executable and ensure the extracted source is also present.
build: $(OUTPUT_DIR)/Effects_runtime.ml $(OUTPUT_DIR)/effects.exe
# Deliberately rerun even when effects.out already records a previous success.
run: build
	$(OUTPUT_DIR)/effects.exe

# The shared all target already verifies every example; add build and execution.
# clean remains local to this directory and does not remove the library's cache.
all: build $(OUTPUT_DIR)/effects.out

# Standalone C has no native exception runtime. Source and cached extraction
# must refuse rather than fall back to the old outcome/goto implementation.
.PHONY: check-native-extraction
check-native-extraction: $(CACHE_DIR)/Example.Effects.Native.fst.checked $(CACHE_DIR)/Example.Effects.NativeExtraction.fst.checked $(CACHE_DIR)/Example.Effects.NativeNoExtract.fst.checked
	set -eu; \
	for input in source checked; do \
	  for entry in Native.early_return Native.deferred_free Native.catch_then_continue Native.locally_defined Native.countdown NativeExtraction.implicit_call NativeExtraction.normal_scope NativeExtraction.handled_bool; do \
	    if [ "$$input" = source ] && [ "$$entry" != Native.early_return ] && [ "$$entry" != NativeExtraction.handled_bool ]; then continue; fi; \
	    module=$${entry%.*}; \
	    file=Example.Effects.$$module.fst; \
	    force=--force; \
	    if [ "$$input" = checked ]; then file=$(CACHE_DIR)/$$file.checked; force=; fi; \
	    output=$(OUTPUT_DIR)/native-reject-C-$$input-$$entry.c; \
	    rm -f "$$output"; \
	    if $(filter-out --cache_checked_modules,$(FSTAR)) $$force --codegen C --custard_monomorphize_types true \
	      --custard_entry Example.Effects.$$entry $$file -o "$$output" > "$$output.log" 2>&1; then \
	      echo "Unexpected C extraction success: $$input $$entry"; exit 1; \
	    fi; \
	    grep -E "Error (322|368)" "$$output.log"; \
	    grep -E "Native Pulse exceptions require|C has no exceptions" "$$output.log"; \
	    test ! -e "$$output"; \
	  done; \
	done
	$(FSTAR) --codegen C --custard_monomorphize_types true \
	  --custard_entry Example.Effects.NativeExtraction.raw_outcome \
	  $(CACHE_DIR)/Example.Effects.NativeExtraction.fst.checked \
	  -o $(OUTPUT_DIR)/Native_raw.c
	$(CC) -std=c11 -Wall -Wextra -Werror -I$(OUTPUT_DIR) \
	  -I$(shell $(FSTAR_EXE) --locate_lib)/ulib/c \
	  -c $(OUTPUT_DIR)/Native_raw.c -o $(OUTPUT_DIR)/Native_raw.o
	set -eu; \
	for input in source checked; do \
	  file=Example.Effects.NativeNoExtract.fst; flags=--force; \
	  if [ "$$input" = checked ]; then \
	    file=$(CACHE_DIR)/$$file.checked; flags=; \
	  fi; \
	  output=$(OUTPUT_DIR)/native-noextract-$$input.ml; \
	  rm -f "$$output"; \
	  if $(filter-out --cache_checked_modules,$(FSTAR)) $$flags --codegen OCaml \
	    --custard_entry Example.Effects.NativeNoExtract.blocked $$file -o "$$output" \
	    > "$$output.log" 2>&1; then \
	    echo "Unexpected extraction success with pulse.noextract: $$input"; exit 1; \
	  fi; \
	  grep -F "Native Pulse exceptions cannot" "$$output.log"; \
	  test ! -e "$$output"; \
	done

all: check-native-extraction

NATIVE_CHECKED := $(CACHE_DIR)/Example.Effects.NativeRuntime.fst.checked

$(OUTPUT_DIR)/Native_runtime.ml: $(NATIVE_CHECKED) $(EFFECTS_CHECKED) $(FSTAR_EXE) Makefile
	$(FSTAR) --codegen OCaml --custard_entry Example.Effects.NativeRuntime.test $< -o $@

$(OUTPUT_DIR)/native.exe: $(OUTPUT_DIR)/Native_runtime.ml native_driver.ml
	cp native_driver.ml $(OUTPUT_DIR)/
	cd $(OUTPUT_DIR) && $(FSTAR_EXE) --ocamlopt Native_runtime.ml native_driver.ml -o native.exe

$(OUTPUT_DIR)/Native_runtime.fs: $(NATIVE_CHECKED) $(EFFECTS_CHECKED) $(FSTAR_EXE) Makefile
	$(FSTAR) --codegen FSharp --custard_entry Example.Effects.NativeRuntime.test $< -o $@

# Cherry writes the implementation and header together. Regenerate both if
# either disappears; concurrent snapshot checks must not invoke it twice.
$(OUTPUT_DIR)/Native_runtime.c $(OUTPUT_DIR)/Native_runtime.h &: $(NATIVE_CHECKED) $(EFFECTS_CHECKED) $(FSTAR_EXE) Makefile
	$(FSTAR) --codegen Cherry --custard_monomorphize_types true \
	  --custard_entry Example.Effects.NativeRuntime.test $< -o $(OUTPUT_DIR)/Native_runtime.c

# Compare the complete emitted files, including the Cherry ABI and ownership
# helpers. Use test.mk's .diff/.accept rules; normal tests never bless drift.
NATIVE_GOLDENS := Native_runtime.ml Native_runtime.c Native_runtime.h
.PHONY: check-native-goldens accept-native-goldens
check-native-goldens: $(addprefix $(OUTPUT_DIR)/,$(addsuffix .diff,$(NATIVE_GOLDENS)))
accept-native-goldens: $(addprefix $(OUTPUT_DIR)/,$(addsuffix .accept,$(NATIVE_GOLDENS)))
all: check-native-goldens

CHERRY_INC := $(shell $(FSTAR_EXE) --locate_lib)/ulib/c
CHERRY_CC ?= $(CC)
CHERRY_CFLAGS ?= -std=c11 -g -DCHERRY_DEBUG -fsanitize=address,undefined -fno-sanitize-recover=undefined
$(OUTPUT_DIR)/native-cherry.exe: $(OUTPUT_DIR)/Native_runtime.c native_driver.c
	$(CHERRY_CC) $(CHERRY_CFLAGS) -Wall -Wextra -Werror \
	  -I$(OUTPUT_DIR) -I$(CHERRY_INC) $< native_driver.c $(CHERRY_INC)/cherry.c -o $@

.PHONY: native-ocaml native-fsharp native-cherry
native-ocaml: $(OUTPUT_DIR)/native.exe $(OUTPUT_DIR)/Native_runtime.ml.diff
	$<
native-fsharp: $(OUTPUT_DIR)/Native_runtime.fs native_driver.fsx
	cp native_driver.fsx $(OUTPUT_DIR)/
	cd $(OUTPUT_DIR) && DOTNET_CLI_TELEMETRY_OPTOUT=1 dotnet fsi --exec native_driver.fsx
native-cherry: $(OUTPUT_DIR)/native-cherry.exe $(OUTPUT_DIR)/Native_runtime.c.diff $(OUTPUT_DIR)/Native_runtime.h.diff
	ASAN_OPTIONS=detect_leaks=1 $<

all: native-ocaml
ifneq ($(NOCHERRY),1)
all: native-cherry
endif
ifneq ($(shell command -v dotnet 2>/dev/null),)
all: native-fsharp
endif
