# Custard extraction of the DICE example.  Assumes everything has already
# been verified by the main Makefile: Custard reads .checked files only.
#
# Unlike c.Makefile there is no dependency graph to compute and no bundle or
# library flag to pass: Custard is whole-program, so the entry points are the
# only input, and it emits one translation unit.  Both C paths are exercised:
#
#   krml  -- Custard emits a .krml file and karamel emits the C, as the
#            existing pipeline does, but from a monomorphized program;
#   C     -- Custard emits the C itself (section 11).
#
# The two external types the program uses -- Spec.Hash.Definitions.hash_alg,
# declared by EverCrypt's headers, and FStar.Bytes.bytes, declared by
# krmllib's compat.h -- are handled by [@@custard_extern] and by Custard's
# built-in table respectively.  Nothing else about the example changes.

PULSE_ROOT ?= ../../../..
FSTAR_EXE ?= $(PULSE_ROOT)/../stage3/out/bin/fstar.exe
KRML ?= $(if $(KRML_EXE),$(KRML_EXE),krml)

PULSE_LIB := $(dir $(FSTAR_EXE))../lib/fstar/pulse
OUT := _custard

ENTRIES := open_session initialize_context derive_child close_session \
           certify_key sign

FSTAR := $(FSTAR_EXE) --ext optimize_let_vc --ext fly_deps --codegen Custard \
         $(foreach e,$(ENTRIES),--custard_entry DPE.$(e)) \
         --cache_dir _cache --include . --include $(PULSE_LIB) \
         --already_cached ',*' --warn_error -321-274-272-241-342

CFLAGS := -I external/c/hacl \
          -I $(dir $(FSTAR_EXE))../include/krml \
          -I $(dir $(FSTAR_EXE))../lib/krml/dist/minimal \
          -Wall -Wextra -Werror -std=c11 -D_BSD_SOURCE -D_DEFAULT_SOURCE -fwrapv

.PHONY: all krml direct clean
all: krml direct

# ---------------------------------------------------------------- via karamel

$(OUT)/DPE.krml: dpe/DPE.fst
	@mkdir -p $(OUT)
	$(FSTAR) --custard_backend Krml dpe/DPE.fst -o $@

krml: $(OUT)/DPE.krml
	$(KRML) -silent -skip-compilation -no-prefix Custard -warn-error -9 \
	  -add-include '"EverCrypt_Base.h"' -tmpdir $(OUT)/kout $<
	cp -p external/c/hacl/EverCrypt_Base.h $(OUT)/kout/
	+$(MAKE) -C $(OUT)/kout -f Makefile.basic Custard.o

# ------------------------------------------------------------- direct-to-C

# Type monomorphization is what makes a C struct per instantiation; without it
# the hash table over sessions would still be polymorphic, and C has no
# representation for a type variable.
$(OUT)/DPE.c: dpe/DPE.fst
	@mkdir -p $(OUT)
	$(FSTAR) --custard_backend C --custard_monomorphize_types true \
	  dpe/DPE.fst -o $@

direct: $(OUT)/DPE.c
	$(CC) $(CFLAGS) -c -o $(OUT)/DPE.o $<

clean:
	rm -rf $(OUT)
