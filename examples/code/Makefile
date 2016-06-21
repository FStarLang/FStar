# FStar variables
FSTAR_HOME=../..
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

OPTIONS_VER=--universes
OPTIONS_OCAML=--lax --codegen OCaml --universes --no_location_info # --use_native_int

CURVE_ODIR=curve

# OCaml variables
OCAMLOPT := ocamlfind opt -package batteries,stdint,zarith -linkpkg -g -I $(ULIB_ML) \
	-I $(ULIB_ML)/hyperheap $(ULIB_ML)/fstarlib-hyperheap.cmxa
#	-I $(ULIB_ML)/native_int

REALIZED_MLI=
REALIZED=FStar_Mul FStar_HyperStack FStar_HST FStar_Buffer
REALIZED_MODULE=$(subst _,., $(REALIZED))
REALIZED_ML=$(addsuffix .mli,$(REALIZED_MLI)) $(addsuffix .ml,$(REALIZED_MLI) $(REALIZED))
NO_CODEGEN=$(addprefix --no_extract , SInt $(REALIZED_MODULE))

# CURVE_EXTRACTED=FStar_FunctionalExtensionality.ml FStar_Seq.ml FStar_Ghost.ml Axioms.ml Bignum_Parameters.ml Bignum_Bigint.ml Bignum_Fsum.ml Bignum_FsumWide.ml Bignum_Fdifference.ml Bignum_Fscalar.ml Bignum_Fproduct.ml Bignum_Modulo.ml Bignum_Core.ml Curve_Point.ml Curve_AddAndDouble.ml Curve_Ladder.ml

CURVE_EXTRACTED=FStar_FunctionalExtensionality.ml FStar_Ghost.ml Math_Axioms.ml Math_Lib.ml Math_Definitions.ml Math_Field.ml Math_Curve.ml Curve_Parameters.ml Curve_Bigint.ml Curve_Fsum.ml Curve_FsumWide.ml Curve_Fdifference.ml Curve_Fscalar.ml Curve_Fproduct.ml Curve_Modulo.ml Curve_Bignum.ml Curve_Crecip.ml Curve_Point.ml Curve_AddAndDouble.ml Curve_Ladder.ml

.PHONY: curve-ver curve-ml

# Curve25519 lax typechecking
curve-lax:
	$(FSTAR) $(OPTIONS_VER) Curve.Crecip.fst Curve.Ladder.fst --lax

# Curve25519 extraction to OCaml
curve-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml hyperheap #PRIMS_DIR=native_int
	mkdir -p $(CURVE_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) Curve.Crecip.fst Curve.Ladder.fst --odir $(CURVE_ODIR) #2> /dev/null
	@sed -i 's/(Obj.magic ((fun pp ppq p pq q n ctr b scalar/(((fun pp ppq p pq q n ctr b scalar/g' $(CURVE_ODIR)/Curve_Ladder.ml
	$(OCAMLOPT) -I ml -I $(CURVE_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(CURVE_ODIR)/,$(CURVE_EXTRACTED)) ml/test_curve.ml -o test_curve.exe
	./test_curve.exe

curve-compile:
	$(OCAMLOPT) -I ml -I $(CURVE_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(CURVE_ODIR)/,$(CURVE_EXTRACTED)) ml/test_curve.ml -o test_curve.exe
	./test_curve.exe

# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	@rm -f $(addprefix ml/, *.cmx *.o *.cmi *~)
	@rm -rf $(CURVE_ODIR) *~ *.exe
