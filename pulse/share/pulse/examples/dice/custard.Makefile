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
# Two of the types the program handles have no F* definition to compile:
# Spec.Hash.Definitions.hash_alg is EverCrypt's algorithm tag, and
# FStar.Bytes.bytes appears only as a field of L0Core's records, which this
# program passes through to the external L0 implementation and never builds
# or reads.  --custard_extern_type says so, and for the direct backend points
# at external/c/dice/dice_externs.h, which declares both.  Nothing in the
# example's F* sources changes.

PULSE_ROOT ?= ../../../..
FSTAR_EXE ?= $(PULSE_ROOT)/../stage3/out/bin/fstar.exe
KRML ?= $(if $(KRML_EXE),$(KRML_EXE),krml)

PULSE_LIB := $(dir $(FSTAR_EXE))../lib/fstar/pulse
OUT := _custard

ENTRIES := open_session initialize_context derive_child close_session \
           certify_key sign

EXTERN_TYPES := Spec.Hash.Definitions.hash_alg=Spec_Hash_Definitions_hash_alg \
                FStar.Bytes.bytes=FStar_Bytes_bytes

FSTAR := $(FSTAR_EXE) --ext optimize_let_vc --ext fly_deps --codegen Custard \
         $(foreach e,$(ENTRIES),--custard_entry DPE.$(e)) \
         --cache_dir _cache --include . --include $(PULSE_LIB) \
         --already_cached ',*' --warn_error -321-274-272-241-342

# The direct backend's output includes nothing but <stdint.h> and friends and
# this example's own header, so there is no krmllib on the include path.
CFLAGS := -I external/c/dice -Wall -Wextra -Werror -std=c11

.PHONY: all krml direct clean
all: krml direct

# ---------------------------------------------------------------- via karamel

$(OUT)/DPE.krml: dpe/DPE.fst
	@mkdir -p $(OUT)
	$(FSTAR) --custard_backend KrmlC \
	  $(foreach t,$(EXTERN_TYPES),--custard_extern_type $(t)) \
	  dpe/DPE.fst -o $@

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
	  $(foreach t,$(EXTERN_TYPES),--custard_extern_type '$(t)@dice_externs.h') \
	  dpe/DPE.fst -o $@

direct: $(OUT)/DPE.c
	$(CC) $(CFLAGS) -c -o $(OUT)/DPE.o $<

clean:
	rm -rf $(OUT)
