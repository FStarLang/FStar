FSTAR_HOME=~/dev/FStar
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

OPTIONS_VER= 
OPTIONS_COMPILE=--lax --codegen C

CHACHA=chacha
POLY=poly
CHACHA_ODIR=chacha20
POLY_ODIR=poly1305
CHACHA_C=Chacha.c test_chacha.c
POLY_C=Parameters.c Bignum.c Poly.c test_poly.c

COMPILE=gcc -O2 fstarlib.c 

.PHONY: chacha-ver chacha-test poly-ver poly-test

all: chacha-test poly-test

chacha-ver: chacha.fst
	$(FSTAR) $(OPTIONS_VER) $^ --z3timeout 20

chacha-test: chacha.fst
	@echo ""
	@echo " Extracting CHACHA20"
	@mkdir -p $(CHACHA_ODIR)
	$(FSTAR) $(OPTIONS_COMPILE) --odir $(CHACHA_ODIR) $^
	@cp ./c/*.c ./c/*.h $(CHACHA_ODIR)
	@echo ""
	@echo " Compiling CHACHA20"
	cd $(CHACHA_ODIR) && $(COMPILE) $(CHACHA_C) -o $(CHACHA)
	./$(CHACHA_ODIR)/$(CHACHA)

poly-ver: poly.fst
	$(FSTAR) $(OPTIONS_VER) $^

poly-test: poly.fst
	@echo ""
	@echo " Extracting POLY1305"
	@mkdir -p $(POLY_ODIR)
	$(FSTAR) $(OPTIONS_COMPILE) --odir $(POLY_ODIR) $^
	@cp ./c/*.c ./c/*.h $(POLY_ODIR)
	@echo ""
	@echo " Compiling POLY1305"
	cd $(POLY_ODIR) && $(COMPILE) $(POLY_C) -o $(POLY)
	./$(POLY_ODIR)/$(POLY)

clean:
	@rm -rf $(CHACHA_ODIR) $(POLY_ODIR) *~
