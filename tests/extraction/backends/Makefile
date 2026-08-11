FSTAR_ROOT ?= ../../..

# NOTE: deliberately *not* passing --cmi here. These tests rely on extraction
# not unfolding top-level names in order to keep their operands opaque; see
# README.md.

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

NO_OCAML :=

# Closures / partial application are outside Low*, so the C backend rejects
# them outright ("Warning 11: this expression is not Low*").
NO_C := ExtBoolHigherOrder

# The Rust backend refuses mathematical integers altogether ("Warning 15: ...
# is not Low*; it uses mathematical integers"), so there is nothing to XFAIL:
# Prims.int is simply out of scope for it.
NO_RUST := ExtPrimsInt ExtPrimsIntDiv ExtPrimsIntMul ExtPrimsIntBignum \
           ExtBoolHigherOrder

# --- machine integers -----------------------------------------------------

# `mk_op` (src/extraction/FStarC.Extraction.Krml.fst:494) maps `eq` to the
# Krml `Eq` opcode but has no case for `ne`, even though the AST already has a
# `Neq` opcode. `FStar.UInt8`'s hand-written OCaml realization is missing `ne`
# too. See FINDINGS.md #1.
XFAIL_OCAML += ExtIntNe
XFAIL_C     += ExtIntNe
XFAIL_RUST  += ExtIntNe

# `shift_arithmetic_right` is not a Krml opcode either. C gets away with it
# thanks to the hand-written definitions in karamel/include/krml/fstar_int.h
# whitelisted in karamel/lib/Helpers.ml, but Rust has no such fallback and
# dies with `unexpected: [type] no casts in Low* -> Rust`. FINDINGS.md #2.
XFAIL_RUST += ExtIntShiftArith

# The comparison peephole in `mk_arith` (karamel/lib/AstToCStar.ml) strips
# *any* cast from an atomic comparison operand, not just the UInt8/UInt16
# upcasts it inserted itself, so a narrowing FStar.Int.Cast inside `=` is
# dropped and the comparison happens at the wider type. FINDINGS.md #4 has a
# verified one-line fix; it lives in the karamel submodule, so it is not
# applied here.
XFAIL_C += ExtIntCast

# `FStar.UInt8`'s hand-written OCaml realization forgets to truncate `lognot`
# back to 8 bits, so `UInt8.lognot 0uy` evaluates to -1 instead of 255uy.
# FINDINGS.md #3.
XFAIL_OCAML += ExtUInt8Lognot

# --- Prims.int ------------------------------------------------------------

# krmllib's Prims_op_Division / Prims_op_Modulus hand the operation straight
# to C, which truncates towards zero; F* specifies Euclidean division, so
# every negative dividend is silently wrong. FINDINGS.md #5.
XFAIL_C += ExtPrimsIntDiv

# F* emits `Prims_op_Star` for `*`, but krmllib only ever defines
# `Prims_op_Multiply`. FINDINGS.md #6.
XFAIL_C += ExtPrimsIntMul

# `Prims_int` is `int32_t` in C. Operations trap via RETURN_OR, but literals
# are printed verbatim and truncated by the C compiler. FINDINGS.md #7.
XFAIL_C += ExtPrimsIntBignum

# --- datatypes ------------------------------------------------------------

# Low* has no heap-allocated inductives, and karamel does not diagnose it: it
# lays the recursive occurrence out by value and lets the C compiler complain
# about an incomplete type. FINDINGS.md #8.
XFAIL_C += ExtDatatypesRec ExtDatatypesMutual

# krml does not terminate on a module containing two recursive datatypes, in
# a phase shared by both backends (FINDINGS.md #9 has a 9-line repro), so
# ExtDatatypesRec times out for C and Rust alike. The Rust backend separately
# fails to box mutually recursive types: `recursive type 'expr' has infinite
# size`.
XFAIL_RUST += ExtDatatypesRec ExtDatatypesMutual

# The Rust backend emits `crate::lowstar::ignore::ignore(...)` for an unused
# binder but never emits the `lowstar` module, so the crate does not compile.
# FINDINGS.md #10.
XFAIL_RUST += ExtDatatypesRecord ExtDatatypesVariant

# Applying a projector directly to a constructor application crashes krml with
# an unhandled OCaml exception. The Rust backend emits
# `match shape::Circle { radius: seven } { ... }`, which rustc rejects
# ("struct literals are not allowed here") for want of parentheses.
# FINDINGS.md #11.
XFAIL_C    += ExtProjectorOfCtor
XFAIL_RUST += ExtProjectorOfCtor

OCAML_TESTS := $(filter-out $(NO_OCAML) $(XFAIL_OCAML),$(TESTS))
C_TESTS     := $(filter-out $(NO_C)     $(XFAIL_C),$(TESTS))
RUST_TESTS  := $(filter-out $(NO_RUST)  $(XFAIL_RUST),$(TESTS))

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
  $(info NOTE: krml not found, skipping the C and Rust extraction tests.)
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

# Karamel needs a .krml for every type it sees, and the F* installation does
# not ship .krml files for ulib. A test that mentions `option`, `either`, or a
# tuple therefore needs FStar.Pervasives.Native extracted alongside it, or
# krml stops with "Reference to undefined type". We build those on demand and
# pass them to every krml invocation.
ULIB_DIR       := $(shell $(FSTAR_EXE) --locate_lib)/ulib
ULIB_KRML_MODS := FStar.Pervasives.Native
ULIB_KRML      := $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(ULIB_KRML_MODS)))

CC ?= cc

all: ocaml c rust

ocaml: $(patsubst %,$(OUTPUT_DIR)/ml/%.ok,$(OCAML_TESTS))
ocaml: $(patsubst %,$(OUTPUT_DIR)/ml/%.xfail,$(XFAIL_OCAML))
ifeq ($(HAVE_KRML),1)
c:     $(patsubst %,$(OUTPUT_DIR)/c/%.ok,$(C_TESTS))
c:     $(patsubst %,$(OUTPUT_DIR)/c/%.xfail,$(XFAIL_C))
ifeq ($(HAVE_RUSTC),1)
rust:  $(patsubst %,$(OUTPUT_DIR)/rs/%.ok,$(RUST_TESTS))
rust:  $(patsubst %,$(OUTPUT_DIR)/rs/%.xfail,$(XFAIL_RUST))
endif
endif
.PHONY: all ocaml c rust

# Convenience: `make ExtFoo.ocaml`, `make ExtFoo.c`, `make ExtFoo.rust`.
%.ocaml: $(OUTPUT_DIR)/ml/%.ok ; @true
%.c:     $(OUTPUT_DIR)/c/%.ok  ; @true
%.rust:  $(OUTPUT_DIR)/rs/%.ok ; @true

###############
# OCaml       #
###############

# Append a driver to the extracted module itself: it is in scope of `main`, so
# no separate compilation unit (and no module resolution) is needed.
$(OUTPUT_DIR)/ml/%.ml: $(OUTPUT_DIR)/%.ml
	$(Q)mkdir -p $(dir $@)
	$(Q)cp $< $@
	$(Q)echo 'let _ = Stdlib.exit (Stdint.Int32.to_int (main ()))' >> $@

$(OUTPUT_DIR)/ml/%.exe: $(OUTPUT_DIR)/ml/%.ml
	$(call msg, "OCAMLOPT", $*)
	$(Q)$(FSTAR_EXE) --ocamlopt $< -o $@

$(OUTPUT_DIR)/ml/%.ok: $(OUTPUT_DIR)/ml/%.exe
	$(call msg, "RUN ocaml", $*)
	$(Q)./$< || { echo "FAIL [ocaml] $*: check #$$? (grep the module for that tag)"; exit 1; }
	$(Q)touch $@

###############
# C (Karamel) #
###############

# ulib modules have no .fst in this directory, so mk/test.mk's generic rule
# does not apply; extract them straight from the installed library.
$(OUTPUT_DIR)/FStar_%.krml:
	$(call msg, "EXTRACT ULIB", $(subst _,.,FStar_$*))
	$(Q)mkdir -p $(OUTPUT_DIR)
	$(Q)$(FSTAR) --codegen krml --extract_module $(subst _,.,FStar_$*) \
	    --cache_dir $(ULIB_DIR)/.cache $(ULIB_DIR)/$(subst _,.,FStar_$*).fst >/dev/null

$(KRMLLIB):
	$(call msg, "KRMLLIB", $(KRML_DIST))
	$(Q)mkdir -p $(KRMLLIB_DIR)
	$(Q)cp $(KRML_DIST)/* $(KRMLLIB_DIR)/
	@# Karamel's Makefile.basic relies on the builtin %.o: %.c rule, which
	@# mk/common.mk disables; clear MAKEFLAGS for the sub-make.
	$(Q)MAKEFLAGS= $(MAKE) -C $(KRMLLIB_DIR) -f Makefile.basic KRML_EXE=$(KRML_EXE) >/dev/null

# krml compiles the generated .c itself, with -Wall -Werror: that is what
# catches "extraction succeeded but the C does not compile" bugs.
$(OUTPUT_DIR)/c/%.exe: $(OUTPUT_DIR)/%.krml $(ULIB_KRML) $(KRMLLIB)
	$(call msg, "KRML C", $*)
	$(Q)rm -rf $(OUTPUT_DIR)/c/$*
	$(Q)$(TIMEOUT) $(KRML_EXE) $(KRML_FLAGS) $(KRML_COMMON) $(KRML_C_FLAGS) -skip-linking -skip-makefiles \
	    -no-prefix $* -bundle $*=\* -tmpdir $(OUTPUT_DIR)/c/$* $(ULIB_KRML) $<
	@# krml exits 0 even when an unhandled exception stops it from writing
	@# anything; do not let that look like a successful extraction.
	$(Q)ls $(OUTPUT_DIR)/c/$*/*.o >/dev/null 2>&1 || \
	    { echo "FAIL [c] $*: krml produced no object file"; exit 1; }
	$(call msg, "CC", $*)
	$(Q)$(CC) -o $@ $(OUTPUT_DIR)/c/$*/*.o $(KRMLLIB)

$(OUTPUT_DIR)/c/%.ok: $(OUTPUT_DIR)/c/%.exe
	$(call msg, "RUN c", $*)
	$(Q)./$< || { echo "FAIL [c] $*: check #$$? (grep the module for that tag)"; exit 1; }
	$(Q)touch $@

##################
# Rust (Karamel) #
##################

# Karamel emits a library crate whose entry point is `pub fn main() -> i32`,
# which Rust will not accept as a binary entry point. Rename it and append a
# real `fn main`.
$(OUTPUT_DIR)/rs/%.rs: $(OUTPUT_DIR)/%.krml $(ULIB_KRML)
	$(call msg, "KRML RUST", $*)
	$(Q)rm -rf $(OUTPUT_DIR)/rs/$*
	$(Q)$(TIMEOUT) $(KRML_EXE) $(KRML_FLAGS) $(KRML_COMMON) -backend rust \
	    -bundle $*=\* -tmpdir $(OUTPUT_DIR)/rs/$* $(ULIB_KRML) $<
	$(Q)sed 's/^pub fn main()/pub fn krml_main()/' $(OUTPUT_DIR)/rs/$*/*.rs > $@
	@# Karamel prints an error but still writes the file when it cannot
	@# translate a definition; a silently truncated crate must not pass.
	$(Q)grep -q '^pub fn krml_main()' $@ || \
	    { echo "FAIL [rust] $*: krml did not emit 'main' in the generated crate"; exit 1; }
	$(Q)echo 'fn main() { std::process::exit(krml_main()) }' >> $@

$(OUTPUT_DIR)/rs/%.exe: $(OUTPUT_DIR)/rs/%.rs
	$(call msg, "RUSTC", $*)
	$(Q)rustc --edition 2021 -A warnings -o $@ $<

$(OUTPUT_DIR)/rs/%.ok: $(OUTPUT_DIR)/rs/%.exe
	$(call msg, "RUN rust", $*)
	$(Q)./$< || { echo "FAIL [rust] $*: check #$$? (grep the module for that tag)"; exit 1; }
	$(Q)touch $@

#####################
# Expected failures #
#####################

# Build the cell in a sub-make and require it to fail. The point is to notice
# when a known bug gets fixed, so that the entry can be removed from XFAIL_*.
#
# The F* side is a *prerequisite*, not part of the sub-make: every bug we XFAIL
# is on the backend side, so extraction itself must still succeed. Without
# that, any breakage in the harness (a missing tool, a bad flag, an error in
# mk/test.mk) would look like the expected failure and the cell would "pass"
# for entirely the wrong reason.
define xfail_rule
$$(OUTPUT_DIR)/$(1)/%.xfail: $$(OUTPUT_DIR)/$(4)
	$$(call msg, "XFAIL $(2)", $$*)
	$$(Q)mkdir -p $$(dir $$@)
	$$(Q)if $$(MAKE) $$(OUTPUT_DIR)/$(1)/$$*.ok >$$@.log 2>&1; then \
	  echo "UNEXPECTED PASS [$(2)] $$*: this cell is listed in XFAIL_$(3) but it"; \
	  echo "  now works. Please remove it from the Makefile and FINDINGS.md."; \
	  exit 1; \
	fi
	@# A cell must fail because of the bug it documents, not because the
	@# harness fell over. Missing tools and make-level breakage are not
	@# expected failures.
	$$(Q)if grep -qE "(command not found|No such file or directory: (krml|rustc|cc)|not found$$$$|takes an argument but has none)" $$@.log; then \
	  echo "BROKEN XFAIL [$(2)] $$*: the cell failed, but not because of the"; \
	  echo "  documented bug. See $$@.log:"; \
	  sed 's/^/    /' $$@.log | tail -n 5; \
	  exit 1; \
	fi
	$$(Q)touch $$@
endef

$(eval $(call xfail_rule,ml,ocaml,OCAML,ml/%.ml))
$(eval $(call xfail_rule,c,c,C,%.krml))
$(eval $(call xfail_rule,rs,rust,RUST,%.krml))
