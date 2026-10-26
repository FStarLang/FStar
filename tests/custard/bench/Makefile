# Benchmarks comparing the Cherry backend (cherry.md) with the OCaml and F#
# backends on the same F* programs.  Not part of `make test`: run
#
#   make            build every benchmark with every backend
#   make bench      build, then time them (RUNS=5 runs each; median time
#                   and peak RSS), printing a markdown table; Cherry also
#                   runs with mimalloc and jemalloc where installed
#
# BACKENDS selects a subset (cherry ocaml fsharp); F# is left out when no
# .NET 10 SDK is installed.  Each program checks its own result and exits
# non-zero on a wrong one, which the runner reports.
FSTAR_ROOT ?= ../../..

BENCHES ?= BenchRBMap BenchBinaryTrees BenchCFold BenchNQueens BenchStrings BenchClosures

DOTNET ?= dotnet
DOTNET10 := $(shell $(DOTNET) --list-sdks 2>/dev/null | grep -c "^1[0-9]\.")
ifeq ($(DOTNET10),0)
BACKENDS ?= cherry ocaml
else
BACKENDS ?= cherry ocaml fsharp
endif

# Cherry is also run with these mallocs, when they are installed, through
# LD_PRELOAD: the runtime allocates every cell with malloc, so the allocator
# is a large part of its time.
LIBDIRS = /usr/lib/x86_64-linux-gnu /usr/lib64 /usr/lib /usr/local/lib
MIMALLOC ?= $(firstword $(wildcard $(addsuffix /libmimalloc.so*,$(LIBDIRS))))
JEMALLOC ?= $(firstword $(wildcard $(addsuffix /libjemalloc.so*,$(LIBDIRS))))
PRELOADS = $(if $(MIMALLOC),mimalloc=$(MIMALLOC)) $(if $(JEMALLOC),jemalloc=$(JEMALLOC))
RUN_BACKENDS ?= $(filter cherry,$(BACKENDS)) \
  $(if $(filter cherry,$(BACKENDS)),$(foreach p,$(PRELOADS),cherry+$(firstword $(subst =, ,$(p))))) \
  $(filter-out cherry,$(BACKENDS))

RUNS ?= 5
comma := ,
space := $(subst ,, )
CC ?= gcc
CHERRY_CFLAGS ?= -O2 -DNDEBUG
OCAMLOPT_FLAGS ?= -O3

include $(FSTAR_ROOT)/mk/test.mk

CHERRY_INC = $(shell $(FSTAR_EXE) --locate_lib)/ulib/c

$(OUTPUT_DIR)/cherry/%.c: $(CACHE_DIR)/%.fst.checked $(FSTAR_EXE)
	$(call msg, "CHERRY", $*)
	@mkdir -p $(dir $@)
	$(FSTAR) --codegen Cherry \
	  --custard_monomorphize_types true --custard_main $*.main $*.fst -o $@

$(OUTPUT_DIR)/cherry/%.exe: $(OUTPUT_DIR)/cherry/%.c
	$(call msg, "CC", $*)
	$(Q)$(CHERRY_CC) -std=c11 $(CHERRY_CFLAGS) -I$(CHERRY_INC) $< $(CHERRY_INC)/cherry.c -o $@

$(OUTPUT_DIR)/ocaml/%.ml: $(CACHE_DIR)/%.fst.checked $(FSTAR_EXE)
	$(call msg, "CUSTARD", $*)
	@mkdir -p $(dir $@)
	$(FSTAR) --codegen OCaml --custard_main $*.main $*.fst -o $@

$(OUTPUT_DIR)/ocaml/%.exe: $(OUTPUT_DIR)/ocaml/%.ml
	$(call msg, "OCAMLOPT", $*)
	$(Q)$(FSTAR_EXE) --ocamlopt $(OCAMLOPT_FLAGS) $< -o $@ 2>&1 | grep -v "options -O3 .* ignored" || true
	$(Q)test -x $@

$(OUTPUT_DIR)/fs/%.built: $(CACHE_DIR)/%.fst.checked $(FSTAR_EXE)
	$(call msg, "CUSTARD-FS", $*)
	@mkdir -p $(OUTPUT_DIR)/fs/$*
	$(FSTAR) --codegen FSharp \
	  --custard_main $*.main $*.fst -o $(OUTPUT_DIR)/fs/$*/$*.fs
	$(call msg, "DOTNET", $*)
	$(Q)cd $(OUTPUT_DIR)/fs/$* && DOTNET_CLI_TELEMETRY_OPTOUT=1 DOTNET_NOLOGO=1 \
	  $(DOTNET) build -c Release -v quiet --nologo > build.log 2>&1 \
	  || { cat build.log; false; }
	$(Q)touch $@

exe_cherry = $(OUTPUT_DIR)/cherry/$(1).exe
exe_ocaml  = $(OUTPUT_DIR)/ocaml/$(1).exe
exe_fsharp = $(OUTPUT_DIR)/fs/$(1).built

EXES = $(foreach b,$(BACKENDS),$(foreach m,$(BENCHES),$(call exe_$(b),$(m))))

.PHONY: build bench
build: $(EXES)
all: build

bench: build
	$(Q)python3 bench.py --runs $(RUNS) --outdir $(OUTPUT_DIR) \
	  --backends $(subst $(space),$(comma),$(strip $(RUN_BACKENDS))) \
	  $(foreach p,$(PRELOADS),--preload $(p)) $(BENCHES)

clean:
	rm -rf $(OUTPUT_DIR) $(CACHE_DIR) .depend

.SECONDARY:
