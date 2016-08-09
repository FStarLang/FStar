# FStar variables
FSTAR_HOME=../..
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

OPTIONS_OCAML=--lax --codegen OCaml --no_location_info

CURVE_ODIR=curve
CHACHA_ODIR=chacha
POLY_ODIR=poly
AEAD_ODIR=aead

# OCaml variables
OCAMLOPT := ocamlfind opt -package batteries,stdint,zarith -linkpkg -g -I $(ULIB_ML) \
	-I $(ULIB_ML)/hyperheap $(ULIB_ML)/fstarlib-hyperheap.cmxa -w -8-20-26

REALIZED_MLI=
REALIZED=FStar_HyperStack FStar_HST Low_Bytes
REALIZED_MODULE=$(subst _,., $(REALIZED))
REALIZED_ML=$(addsuffix .mli,$(REALIZED_MLI)) $(addsuffix .ml,$(REALIZED_MLI) $(REALIZED))
NO_CODEGEN=$(addprefix --no_extract , FStar.Buffer SInt $(REALIZED_MODULE))

CURVE_EXTRACTED=FStar_TSet.ml FStar_FunctionalExtensionality.ml FStar_Ghost.ml Math_Axioms.ml Math_Lib.ml Math_Definitions.ml Math_Field.ml Math_Curve.ml Curve_Parameters.ml Curve_Bigint.ml Curve_Fsum.ml Curve_FsumWide.ml Curve_Fdifference.ml Curve_Fscalar.ml Curve_Fproduct.ml Curve_Modulo.ml Curve_Bignum.ml Curve_Crecip.ml Curve_Point.ml Curve_AddAndDouble.ml Curve_Ladder.ml
CHACHA_EXTRACTED=Chacha.ml
POLY_EXTRACTED=FStar_Ghost.ml Poly_Parameters.ml Poly_Bigint.ml Poly_Bignum.ml Poly_Poly1305.ml
AEAD_EXTRACTED= FStar_Seq.ml Buffer_Utils.ml Chacha_wip.ml FStar_Ghost.ml Poly_Parameters.ml Poly_Bigint.ml Poly_Bignum.ml Poly_Poly1305_wip_Lemmas.ml Poly_Poly1305_wip.ml AEAD_Chacha20_Poly1305.ml

P_EXTRACTED=FStar_Ghost.ml FStar_Seq.ml Poly1305_Parameters.ml Poly1305_Bigint.ml Poly1305_Arithmetic.ml Poly1305.ml

.PHONY: lib-ver curve-ver curve-ml chacha-ver chacha-ml ulib

all: uall sall

uall: chacha-test poly-test aead-test # curve-test

sall:

ulib: $(FSTAR_HOME)/ulib/ml/fstar-hyperlib.cmxa

$(FSTAR_HOME)/ulib/ml/fstar-hyperlib.cmxa:
	make -j 1 -C $(FSTAR_HOME)/ulib/ml clean hyperheap

# Verification target for the low-level libraries of F* in universes
lib-ver:
	$(FSTAR) FStar.HyperStack.fst FStar.HST.fst FStar.Buffer.fst

# Curve25519 lax typechecking
curve-lax:
	$(FSTAR) Curve.Crecip.fst Curve.Ladder.fst --lax

# Curve25519 extraction to OCaml
curve-extract: ulib
	mkdir -p $(CURVE_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) Curve.Crecip.fst Curve.Ladder.fst --odir $(CURVE_ODIR) #2> /dev/null
	@sed -i.bak 's/(Obj.magic ((fun pp ppq p pq q n ctr b scalar/(((fun pp ppq p pq q n ctr b scalar/g' $(CURVE_ODIR)/Curve_Ladder.ml

curve-compile: curve-extract
	$(OCAMLOPT) -I ml -I $(CURVE_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(CURVE_ODIR)/,$(CURVE_EXTRACTED)) ml/test_curve.ml -o test_curve.exe

curve-test: curve-compile
	./test_curve.exe

# AES targets
chacha-ver:
	$(FSTAR) Chacha.fst 

chacha-extract: ulib
	mkdir -p $(CHACHA_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) Chacha.fst --odir $(CHACHA_ODIR) 

chacha-compile: chacha-extract
	$(OCAMLOPT) -I ml -I $(CHACHA_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(CHACHA_ODIR)/,$(CHACHA_EXTRACTED)) ml/test_chacha.ml -o test_chacha.exe

chacha-test: chacha-compile
	./test_chacha.exe

poly-extract: ulib
	mkdir -p $(POLY_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) Poly.Poly1305.fst --odir $(POLY_ODIR) #2> /dev/null

poly-compile: poly-extract
	$(OCAMLOPT) -I ml -I $(POLY_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(POLY_ODIR)/,$(POLY_EXTRACTED)) ml/test_poly1305.ml -o test_poly.exe

poly-test: poly-compile
	./test_poly.exe

aead-extract: ulib
	mkdir -p $(AEAD_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) AEAD.Chacha20_Poly1305.fst --odir $(AEAD_ODIR) #2> /dev/null
	@sed -i.bak 's/Obj.magic ((fun log msg/ ((fun log msg/g' $(AEAD_ODIR)/Poly_Poly1305_wip.ml

aead-compile: aead-extract
	$(OCAMLOPT) -I ml -I $(AEAD_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(AEAD_ODIR)/,$(AEAD_EXTRACTED)) ml/test_aead.ml -o test_aead.exe

aead-test: aead-compile
	./test_aead.exe

test:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml hyperheap
	mkdir -p $(POLY_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) Poly1305.fst --odir $(POLY_ODIR) #2> /dev/null
	$(OCAMLOPT) -I ml -I $(POLY_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(POLY_ODIR)/,$(P_EXTRACTED)) ml/test_poly_wip.ml -o test_poly.exe
	./test_poly.exe

wip:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml hyperheap
	mkdir -p $(CHACHA_ODIR)
		$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) Chacha20.fst --odir $(CHACHA_ODIR) 
	$(OCAMLOPT) -I ml -I $(CHACHA_ODIR) \
	$(addprefix ml/,$(REALIZED_ML)) \
	$(addprefix $(CHACHA_ODIR)/,Chacha20.ml) ml/test_chacha20.ml -o test_chacha.exe
	./test_chacha.exe 

# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	@rm -f $(addprefix ml/, *.cmx *.o *.cmi *~)
	@rm -rf $(CURVE_ODIR) $(CHACHA_ODIR) $(POLY_ODIR) $(AEAD_ODIR) *~ *.exe
