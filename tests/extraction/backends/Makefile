FSTAR_ROOT ?= ../../..

include $(FSTAR_ROOT)/mk/test.mk

# Splitting a query to localize an error is fine here; these modules bundle
# many independent checks into one function on purpose.
FSTAR_ARGS += --warn_error -349

# Every ExtXxx.fst in this directory is a test. Each one is self-contained and
# exposes `main : unit -> FStar.Int32.t` returning 0 on success.
TESTS := $(basename $(wildcard Ext*.fst))

# --------------------------------------------------------------------------
# Backend exclusions.
#
# XFAIL_<backend> lists (test, backend) cells that are known to be *broken*:
# the cell is still built and run, but it is required to fail. If one starts
# passing, the build stops and tells you to remove the entry -- that way a bug
# fix cannot silently go unnoticed. See FINDINGS.md for the analysis of each.
#
# NO_<backend> lists cells that make no sense on that backend (rather than
# being buggy), and are simply not built.
# --------------------------------------------------------------------------

# --------------------------------------------------------------------------
# Columns.
#
# Custard (doc/ref/custard.md) is the extractor; it has four code generators,
# and so this directory has four columns:
#
#   custard-ocaml       --codegen OCaml    + ocamlfind ocamlopt
#   custard-c           --codegen C        + cc      (no karamel at all)
#   custard-krml-c      --codegen KrmlC    + krml    + cc
#   custard-krml-rust   --codegen KrmlRust + krml -backend rust + rustc
#
# Every module here has `main : unit -> Int32.t`, which is what
# --custard_main wants: Custard calls it from the generated code and makes its
# result the process exit status, so these columns need no driver of their own
# except on the karamel C path, where the name `main` belongs to the krml
# module rather than to the F* one.
# --------------------------------------------------------------------------

NO_CUSTARD_OCAML :=

# The direct C backend diagnoses what C cannot represent (error 368) instead
# of mistranslating it, which is the judgement NO_ records: an unbounded Prims.int, a closure, and an inductive that contains
# itself by value have no C representation.
NO_CUSTARD_C := ExtPrimsInt ExtPrimsIntDiv ExtPrimsIntMul ExtPrimsIntBignum \
                ExtBoolHigherOrder ExtDatatypesRec ExtDatatypesMutual \
                ExtInt128

# karamel's Rust backend refuses mathematical integers, and it cannot translate a closure.
NO_CUSTARD_KRML_RUST := ExtPrimsInt ExtPrimsIntDiv ExtPrimsIntMul \
                        ExtPrimsIntBignum ExtBoolHigherOrder

NO_CUSTARD_KRML_C := ExtBoolHigherOrder

# --- known bugs ----------------------------------------------------------

# FINDINGS.md #18: FStar.{U,}Int{8,16,32,64} are not realized modules for
# Custard the way FStar.UInt8 is, and only the operations with a primitive
# rule (arithmetic, comparison, the bitwise pair) are recognized. Everything
# else -- `ne`, `lognot`, the masks -- is compiled from its F* *model*, which
# is a fold over a bit vector of Prims.int. That does not even typecheck on
# the OCaml backend, and on the C ones it reaches Prims.int and is rejected.
#
# Section 125.1--125.4 gave `shift_arithmetic_right` and the two rotates
# primitive rules, which is why ExtIntShiftArith and ExtUIntRotate are no
# longer here on any of the four columns.
XFAIL_CUSTARD_OCAML     += ExtIntNe
#
# ExtUIntMask was XFAIL on the krml C column for the same reason, and is no
# longer: the machine-integer modules are realized in `ulib/ml/app/ints`, so
# `Builtins.realized_modules` now lists all eight of them and `eq_mask` and
# `gte_mask` reach the realization rather than the bit-vector fold. The
# diagnosis in the row above was that the bug was in Builtins and not in the
# C backend, which is where the fix went.

# FINDINGS.md #3: `FStar.UInt8` *is* a realized module for Custard, so its
# OCaml column inherits the realization's untruncated `lognot`.
XFAIL_CUSTARD_OCAML += ExtUInt8Lognot

# FINDINGS.md #5, #7: the krml C column uses krmllib's Prims.int, and so
# inherits its bugs.
XFAIL_CUSTARD_KRML_C += ExtPrimsIntDiv ExtPrimsIntBignum

# FINDINGS.md #8, #9: heap-allocated inductives, and krml not terminating on
# two recursive datatypes.
XFAIL_CUSTARD_KRML_C    += ExtDatatypesRec ExtDatatypesMutual
XFAIL_CUSTARD_KRML_RUST += ExtDatatypesRec ExtDatatypesMutual

# FINDINGS.md #14, #15: karamel has no 128-bit integers in Rust, and krmllib
# ships no FStar.Int128 for C.
XFAIL_CUSTARD_KRML_C    += ExtInt128 ExtUInt128
XFAIL_CUSTARD_KRML_RUST += ExtInt128

# FINDINGS.md #4: karamel's C backend drops a narrowing cast inside a
# comparison. Custard emits the cast, and karamel then removes it.
XFAIL_CUSTARD_KRML_C    += ExtIntCast

CUSTARD_OCAML_TESTS     := $(filter-out $(NO_CUSTARD_OCAML)     $(XFAIL_CUSTARD_OCAML),$(TESTS))
CUSTARD_C_TESTS         := $(filter-out $(NO_CUSTARD_C)         $(XFAIL_CUSTARD_C),$(TESTS))
CUSTARD_KRML_C_TESTS    := $(filter-out $(NO_CUSTARD_KRML_C)    $(XFAIL_CUSTARD_KRML_C),$(TESTS))
CUSTARD_KRML_RUST_TESTS := $(filter-out $(NO_CUSTARD_KRML_RUST) $(XFAIL_CUSTARD_KRML_RUST),$(TESTS))

# --------------------------------------------------------------------------
# Which columns can we actually run?
#
# This directory runs unconditionally as part of `make test`, so it has to
# cope with a tree where Karamel or rustc is unavailable rather than break the
# build. Each column is enabled only if its toolchain is present; a missing
# one is reported loudly and skipped. Set REQUIRE_BACKENDS=1 to turn those
# skips into hard errors (what CI should eventually do, once every runner is
# known to have the tools).
#
# mk/test.mk defaults KRML_EXE to $(FSTAR_ROOT)/out/bin/krml, which only
# exists in a dev tree. `make install` also puts krml next to fstar.exe in
# stageN/out/bin, which is what CI has, so try that too.
# --------------------------------------------------------------------------

KRML_CANDIDATES := $(KRML_EXE) $(dir $(FSTAR_EXE))krml $(FSTAR_ROOT)/karamel/out/bin/krml
KRML_FOUND      := $(firstword $(wildcard $(KRML_CANDIDATES)) $(shell command -v krml 2>/dev/null))
ifneq ($(KRML_FOUND),)
  override KRML_EXE := $(KRML_FOUND)
endif

HAVE_KRML  := $(if $(KRML_FOUND),1,)
HAVE_RUSTC := $(if $(shell command -v rustc 2>/dev/null),1,)

ifeq ($(HAVE_KRML),)
  ifeq ($(REQUIRE_BACKENDS),1)
    $(error krml not found (looked in $(KRML_CANDIDATES) and on PATH), and REQUIRE_BACKENDS=1)
  endif
  $(info NOTE: krml not found, skipping the karamel extraction tests.)
  $(info       Looked in: $(KRML_CANDIDATES) and on PATH.)
endif
ifeq ($(HAVE_RUSTC),)
  ifeq ($(REQUIRE_BACKENDS),1)
    $(error rustc not found on PATH, and REQUIRE_BACKENDS=1)
  endif
  $(info NOTE: rustc not found, skipping the Rust extraction tests.)
endif

# Karamel's C runtime support library (Prims_strcat, FStar_String_*, ...).
# Built once, out of the karamel distribution that ships with the compiler.
KRML_DIST     := $(if $(HAVE_KRML),$(shell $(KRML_EXE) -locate-krmllib)/dist/generic)
KRMLLIB_DIR   := $(OUTPUT_DIR)/krmllib
KRMLLIB       := $(KRMLLIB_DIR)/libkrmllib.a

# Warning 2 is "reference with no corresponding implementation". We downgrade
# it to a warning (`+`) on purpose: several primitives are legitimately
# realized by hand in krmllib, and we would rather let the real C compiler and
# linker (or rustc) decide whether the generated code is actually buildable.
KRML_COMMON = -silent -warn-error @4+2-15

# Two of the bugs in FINDINGS.md make krml loop forever, so every krml
# invocation is bounded. Anything slower than this is a bug in its own right.
KRML_TIMEOUT ?= 120
TIMEOUT      := timeout $(KRML_TIMEOUT)

# Karamel's C runtime realizes FStar.String.* and friends, but nothing pulls
# their headers in when we bundle a single module, so the generated code would
# call them through implicit declarations (an error under -Werror).
KRML_C_FLAGS = -ccopt -I$(abspath $(KRMLLIB_DIR)) -add-include '"FStar_String.h"'

CC ?= cc

all: custard-ocaml custard-c custard-krml-c custard-krml-rust

custard-ocaml: $(patsubst %,$(OUTPUT_DIR)/cml/%.ok,$(CUSTARD_OCAML_TESTS))
custard-ocaml: $(patsubst %,$(OUTPUT_DIR)/cml/%.xfail,$(XFAIL_CUSTARD_OCAML))
custard-c: $(patsubst %,$(OUTPUT_DIR)/cc/%.ok,$(CUSTARD_C_TESTS))
custard-c: $(patsubst %,$(OUTPUT_DIR)/cc/%.xfail,$(XFAIL_CUSTARD_C))
ifeq ($(HAVE_KRML),1)
custard-krml-c: $(patsubst %,$(OUTPUT_DIR)/ckc/%.ok,$(CUSTARD_KRML_C_TESTS))
custard-krml-c: $(patsubst %,$(OUTPUT_DIR)/ckc/%.xfail,$(XFAIL_CUSTARD_KRML_C))
ifeq ($(HAVE_RUSTC),1)
custard-krml-rust: $(patsubst %,$(OUTPUT_DIR)/ckr/%.ok,$(CUSTARD_KRML_RUST_TESTS))
custard-krml-rust: $(patsubst %,$(OUTPUT_DIR)/ckr/%.xfail,$(XFAIL_CUSTARD_KRML_RUST))
endif
endif
.PHONY: all custard-ocaml custard-c custard-krml-c custard-krml-rust

# Convenience: `make ExtFoo.custard-ocaml`, and so on.
%.custard-ocaml:     $(OUTPUT_DIR)/cml/%.ok ; @true
%.custard-c:         $(OUTPUT_DIR)/cc/%.ok  ; @true
%.custard-krml-c:    $(OUTPUT_DIR)/ckc/%.ok ; @true
%.custard-krml-rust: $(OUTPUT_DIR)/ckr/%.ok ; @true

#############
# krmllib   #
#############

$(KRMLLIB):
	$(call msg, "KRMLLIB", $(KRML_DIST))
	$(Q)mkdir -p $(KRMLLIB_DIR)
	$(Q)cp $(KRML_DIST)/* $(KRMLLIB_DIR)/
	@# Karamel's Makefile.basic relies on the builtin %.o: %.c rule, which
	@# mk/common.mk disables; clear MAKEFLAGS for the sub-make.
	$(Q)MAKEFLAGS= $(MAKE) -C $(KRMLLIB_DIR) -f Makefile.basic KRML_EXE=$(KRML_EXE) >/dev/null

###########
# Custard #
###########

# Custard is whole-program: it starts from an entry point and follows what it
# reaches, so there is no --extract_module and no per-module dependency graph
# to hand to karamel. One .fst goes in, one translation unit comes out.
#
# The .checked file is the only prerequisite named, which is coarser than it
# looks: a run reads far more than that, but everything else it reads is ulib,
# and ulib does not change while this directory is being built.
#
# --custard_main names `main` as *the* entry point, which is what makes the
# generated code call it and turn its Int32 result into the exit status.
CUSTARD = --custard_main $*.main

$(OUTPUT_DIR)/custard/%.ml: $(CACHE_DIR)/%.fst.checked
	$(call msg, "CUSTARD ml", $*)
	$(Q)mkdir -p $(dir $@)
	$(Q)$(FSTAR) $< $(CUSTARD) --codegen OCaml -o $@

# Type monomorphization (section 5.0.1) is a prerequisite for the direct C
# backend: without it the program still has type variables, which have no size.
$(OUTPUT_DIR)/custard/%.c: $(CACHE_DIR)/%.fst.checked
	$(call msg, "CUSTARD c", $*)
	$(Q)mkdir -p $(dir $@)
	$(Q)$(FSTAR) $< $(CUSTARD) --codegen C \
	    --custard_monomorphize_types true -o $@
	@# The invariant of tests/custard and pulse/test: a block with nothing in
	@# it is a branch the backend failed to notice was empty.
	$(Q)awk '/\{$$/ { open = NR; next } \
	         /^[ \t]*\}/ && open == NR - 1 { print NR; found = 1 } \
	         { open = 0 } END { exit found }' $@ \
	  || { echo "FAIL [custard-c] $*: empty block, at the lines above"; exit 1; }
	$(Q)python3 $(FSTAR_ROOT)/tests/custard/checkgroup.py $@ $(basename $@).h \
	  || { echo "FAIL [custard-c] $*: redundant parentheses"; exit 1; }

# Two rules, not one, because KrmlC and KrmlRust are two backends: karamel
# models Pulse.Lib.Slice on the Rust path only, so a .krml built for one
# target does not hold the program the other needs (section 20).
$(OUTPUT_DIR)/custard/%.krmlc.krml: $(CACHE_DIR)/%.fst.checked
	$(call msg, "CUSTARD krml-c", $*)
	$(Q)mkdir -p $(dir $@)
	$(Q)$(FSTAR) $< $(CUSTARD) --codegen KrmlC -o $@

$(OUTPUT_DIR)/custard/%.krmlrust.krml: $(CACHE_DIR)/%.fst.checked
	$(call msg, "CUSTARD krml-rust", $*)
	$(Q)mkdir -p $(dir $@)
	$(Q)$(FSTAR) $< $(CUSTARD) --codegen KrmlRust -o $@

# --- custard-ocaml --------------------------------------------------------

$(OUTPUT_DIR)/cml/%.exe: $(OUTPUT_DIR)/custard/%.ml
	$(call msg, "OCAMLOPT", $*)
	$(Q)mkdir -p $(dir $@)
	$(Q)$(FSTAR_EXE) --ocamlopt $< -o $@

$(OUTPUT_DIR)/cml/%.ok: $(OUTPUT_DIR)/cml/%.exe
	$(call msg, "RUN custard-ocaml", $*)
	$(Q)./$< || { echo "FAIL [custard-ocaml] $*: check #$$? (grep the module for that tag)"; exit 1; }
	$(Q)touch $@

# --- custard-c ------------------------------------------------------------

# A self-contained C11 translation unit over the standard headers: no krmllib,
# no include path, no karamel. -Werror is part of the test -- an unused
# variable or a missing cast is a bug in the backend, not a style question.
#
# -Wtype-limits and -Wtautological-compare are off because they fire on
# properties of the *test*: a module that pins `lognot 0uy <= 255uy` is saying
# something about F*, and that the bound holds for a uint8_t at all is exactly
# what it means to have got the width right.
CUSTARD_CFLAGS ?= -std=c11 -Wall -Wextra -Werror \
                  -Wno-type-limits -Wno-tautological-compare

$(OUTPUT_DIR)/cc/%.exe: $(OUTPUT_DIR)/custard/%.c
	$(call msg, "CC", $*)
	$(Q)mkdir -p $(dir $@)
	$(Q)$(CC) $(CUSTARD_CFLAGS) -o $@ $<

$(OUTPUT_DIR)/cc/%.ok: $(OUTPUT_DIR)/cc/%.exe
	$(call msg, "RUN custard-c", $*)
	$(Q)./$< || { echo "FAIL [custard-c] $*: check #$$? (grep the module for that tag)"; exit 1; }
	$(Q)touch $@

# --- custard-krml-c -------------------------------------------------------

# A whole-program krml file holds exactly one module, named Custard, so there
# is nothing to bundle and karamel writes Custard.c whatever the test is
# called. -no-prefix Custard drops that one prefix, which leaves the F* names:
# `main` is `ExtFoo_main`, not `main`, so unlike the column above this one
# needs a driver. krml writes the include path it wants into compile_flags.txt,
# which is the only portable way to find krmllib's headers.
$(OUTPUT_DIR)/ckc/%.exe: $(OUTPUT_DIR)/custard/%.krmlc.krml $(KRMLLIB)
	$(call msg, "KRML C", $*)
	$(Q)mkdir -p $(dir $@)
	$(Q)rm -rf $(OUTPUT_DIR)/ckc/$*
	$(Q)$(TIMEOUT) $(KRML_EXE) $(KRML_FLAGS) $(KRML_COMMON) $(KRML_C_FLAGS) \
	    -skip-linking -skip-makefiles -no-prefix Custard \
	    -tmpdir $(OUTPUT_DIR)/ckc/$* $<
	@# krml exits 0 even when an unhandled exception stops it from writing
	@# anything; do not let that look like a successful extraction.
	$(Q)ls $(OUTPUT_DIR)/ckc/$*/*.o >/dev/null 2>&1 || \
	    { echo "FAIL [custard-krml-c] $*: krml produced no object file"; exit 1; }
	$(Q){ echo '#include "Custard.h"'; \
	      echo 'int main(void) {'; \
	      grep -q krmlinit_globals $(OUTPUT_DIR)/ckc/$*/Custard.h && \
	        echo '  krmlinit_globals();' || true; \
	      echo '  return (int)$*_main();'; \
	      echo '}'; } > $(OUTPUT_DIR)/ckc/$*/driver.c
	$(call msg, "CC", $*)
	$(Q)$(CC) $$(tr '\n' ' ' < $(OUTPUT_DIR)/ckc/$*/compile_flags.txt) \
	    -o $@ $(OUTPUT_DIR)/ckc/$*/driver.c $(OUTPUT_DIR)/ckc/$*/*.o $(KRMLLIB)

$(OUTPUT_DIR)/ckc/%.ok: $(OUTPUT_DIR)/ckc/%.exe
	$(call msg, "RUN custard-krml-c", $*)
	$(Q)./$< || { echo "FAIL [custard-krml-c] $*: check #$$? (grep the module for that tag)"; exit 1; }
	$(Q)touch $@

# --- custard-krml-rust ----------------------------------------------------

# karamel's Rust backend flattens the F* prefix away, so here `main` really is
# `main`; rename it and append a real `fn main`, since Rust will not accept
# `pub fn main() -> i32` as a binary entry point.
$(OUTPUT_DIR)/ckr/%.rs: $(OUTPUT_DIR)/custard/%.krmlrust.krml
	$(call msg, "KRML RUST", $*)
	$(Q)mkdir -p $(dir $@)
	$(Q)rm -rf $(OUTPUT_DIR)/ckr/$*
	$(Q)$(TIMEOUT) $(KRML_EXE) $(KRML_FLAGS) $(KRML_COMMON) -backend rust \
	    -tmpdir $(OUTPUT_DIR)/ckr/$* $<
	$(Q)sed 's/^pub fn main()/pub fn krml_main()/' $(OUTPUT_DIR)/ckr/$*/*.rs > $@
	$(Q)grep -q '^pub fn krml_main()' $@ || \
	    { echo "FAIL [custard-krml-rust] $*: krml did not emit 'main' in the generated crate"; exit 1; }
	$(Q)echo 'fn main() { std::process::exit(krml_main()) }' >> $@

$(OUTPUT_DIR)/ckr/%.exe: $(OUTPUT_DIR)/ckr/%.rs
	$(call msg, "RUSTC", $*)
	$(Q)rustc --edition 2021 -A warnings -o $@ $<

$(OUTPUT_DIR)/ckr/%.ok: $(OUTPUT_DIR)/ckr/%.exe
	$(call msg, "RUN custard-krml-rust", $*)
	$(Q)./$< || { echo "FAIL [custard-krml-rust] $*: check #$$? (grep the module for that tag)"; exit 1; }
	$(Q)touch $@

#####################
# Expected failures #
#####################

# Build the cell in a sub-make and require it to fail. The point is to notice
# when a known bug gets fixed, so that the entry can be removed from XFAIL_*.
#
# Custard is the extractor, so a bug in it can stop the pipeline at the F*
# step; the failure may happen at any stage. It is required to be a failure of
# the pipeline, not of the harness: missing tools and make-level breakage are
# not expected failures.
#
# The prerequisite is the .checked file: a cell that cannot even be
# type-checked is broken in a way this directory does not mean to record.
define custard_xfail_rule
$$(OUTPUT_DIR)/$(1)/%.xfail: $$(CACHE_DIR)/%.fst.checked
	$$(call msg, "XFAIL $(2)", $$*)
	$$(Q)mkdir -p $$(dir $$@)
	$$(Q)if $$(MAKE) $$(OUTPUT_DIR)/$(1)/$$*.ok >$$@.log 2>&1; then \
	  echo "UNEXPECTED PASS [$(2)] $$*: this cell is listed in XFAIL_$(3) but it"; \
	  echo "  now works. Please remove it from the Makefile and FINDINGS.md."; \
	  exit 1; \
	fi
	$$(Q)if grep -qE "(command not found|No such file or directory: (krml|rustc|cc)|not found$$$$|takes an argument but has none)" $$@.log; then \
	  echo "BROKEN XFAIL [$(2)] $$*: the cell failed, but not because of the"; \
	  echo "  documented bug. See $$@.log:"; \
	  sed 's/^/    /' $$@.log | tail -n 5; \
	  exit 1; \
	fi
	$$(Q)touch $$@
endef

$(eval $(call custard_xfail_rule,cml,custard-ocaml,CUSTARD_OCAML))
$(eval $(call custard_xfail_rule,cc,custard-c,CUSTARD_C))
$(eval $(call custard_xfail_rule,ckc,custard-krml-c,CUSTARD_KRML_C))
$(eval $(call custard_xfail_rule,ckr,custard-krml-rust,CUSTARD_KRML_RUST))
