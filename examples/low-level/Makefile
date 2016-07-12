# FStar variables
FSTAR_HOME=../..
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

OPTIONS_OCAML=--lax --codegen OCaml --no_location_info

CURVE_ODIR=curve
CHACHA_ODIR=chacha
POLY_ODIR=poly

# OCaml variables
OCAMLOPT := ocamlfind opt -package batteries,stdint,zarith -linkpkg -g -I $(ULIB_ML) \
	-I $(ULIB_ML)/hyperheap $(ULIB_ML)/fstarlib-hyperheap.cmxa -w -8-20-26

REALIZED_MLI=
REALIZED=FStar_HyperStack FStar_HST
REALIZED_MODULE=$(subst _,., $(REALIZED))
REALIZED_ML=$(addsuffix .mli,$(REALIZED_MLI)) $(addsuffix .ml,$(REALIZED_MLI) $(REALIZED))
NO_CODEGEN=$(addprefix --no_extract , SInt $(REALIZED_MODULE))

# CURVE_EXTRACTED=FStar_FunctionalExtensionality.ml FStar_Seq.ml FStar_Ghost.ml Axioms.ml Bignum_Parameters.ml Bignum_Bigint.ml Bignum_Fsum.ml Bignum_FsumWide.ml Bignum_Fdifference.ml Bignum_Fscalar.ml Bignum_Fproduct.ml Bignum_Modulo.ml Bignum_Core.ml Curve_Point.ml Curve_AddAndDouble.ml Curve_Ladder.ml

CURVE_EXTRACTED=FStar_FunctionalExtensionality.ml FStar_Ghost.ml Math_Axioms.ml Math_Lib.ml Math_Definitions.ml Math_Field.ml Math_Curve.ml Curve_Parameters.ml Curve_Bigint.ml Curve_Fsum.ml Curve_FsumWide.ml Curve_Fdifference.ml Curve_Fscalar.ml Curve_Fproduct.ml Curve_Modulo.ml Curve_Bignum.ml Curve_Crecip.ml Curve_Point.ml Curve_AddAndDouble.ml Curve_Ladder.ml
CHACHA_EXTRACTED=Chacha.ml
POLY_EXTRACTED=FStar_Ghost.ml Poly_Parameters.ml Poly_Bigint.ml Poly_Bignum.ml Poly_Poly1305.ml

.PHONY: lib-ver curve-ver curve-ml chacha-ver chacha-ml

all: curve-ml chacha-ml poly-ml

# Verification target for the low-level libraries of F* in universes
lib-ver:
	$(FSTAR) FStar.HyperStack.fst FStar.HST.fst FStar.Buffer.fst

# Curve25519 lax typechecking
curve-lax:
	$(FSTAR) Curve.Crecip.fst Curve.Ladder.fst --lax

# Curve25519 extraction to OCaml
curve-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml hyperheap
	mkdir -p $(CURVE_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) Curve.Crecip.fst Curve.Ladder.fst --odir $(CURVE_ODIR) #2> /dev/null
	@sed -i.bak 's/(Obj.magic ((fun pp ppq p pq q n ctr b scalar/(((fun pp ppq p pq q n ctr b scalar/g' $(CURVE_ODIR)/Curve_Ladder.ml
	$(OCAMLOPT) -I ml -I $(CURVE_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(CURVE_ODIR)/,$(CURVE_EXTRACTED)) ml/test_curve.ml -o test_curve.exe
	./test_curve.exe

curve-compile:
	$(OCAMLOPT) -I ml -I $(CURVE_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(CURVE_ODIR)/,$(CURVE_EXTRACTED)) ml/test_curve.ml -o test_curve.exe
	./test_curve.exe

# AES targets
chacha-ver:
	$(FSTAR) Chacha.fst 

chacha-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml hyperheap
	mkdir -p $(CHACHA_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) Chacha.fst --odir $(CHACHA_ODIR) 
	$(OCAMLOPT) -I ml -I $(CHACHA_ODIR) \
	  $(FSTAR_HOME)/ulib/ml/FStar_UInt32.ml \
	  $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(CHACHA_ODIR)/,$(CHACHA_EXTRACTED)) ml/test_chacha.ml -o test_chacha.exe
	./test_chacha.exe 

chacha-compile:
	$(OCAMLOPT) -I ml -I $(CHACHA_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(FSTAR_HOME)/ulib/ml/FStar_UInt32.ml \
	  $(addprefix $(CHACHA_ODIR)/,$(CHACHA_EXTRACTED)) ml/test_chacha.ml -o test_chacha.exe
	./test_chacha.exe

poly-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml hyperheap
	mkdir -p $(POLY_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) Poly.Poly1305.fst --odir $(POLY_ODIR) #2> /dev/null
	$(OCAMLOPT) -I ml -I $(POLY_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(POLY_ODIR)/,$(POLY_EXTRACTED)) ml/test_poly1305.ml -o test_poly.exe
	./test_poly.exe

poly-compile:
	$(OCAMLOPT) -I ml -I $(POLY_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(POLY_ODIR)/,$(POLY_EXTRACTED)) ml/test_poly1305.ml -o test_poly.exe
	./test_poly.exe

# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	@rm -f $(addprefix ml/, *.cmx *.o *.cmi *~)
	@rm -rf $(CURVE_ODIR) $(CHACHA_ODIR) $(POLY_ODIR) *~ *.exe
