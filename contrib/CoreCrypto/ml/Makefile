all: CoreCrypto.cmxa

OCAMLC = ocamlfind c
OCAMLOPT = ocamlfind opt
OCAMLMKLIB = ocamlfind mklib

PLATFORM = $(FSTAR_HOME)/contrib/Platform/ml
OPENSSL_INCLUDE = ../../../../openssl/include

ifeq ($(OS),Windows_NT)
    DLL = dll
    CC = i686-w64-mingw32-gcc
    OCAML_INCLUDE = /usr/local/lib/ocaml
    ARCH = win32
else
    DLL = so 
    UNAME_S := $(shell uname -s)
    ifeq ($(UNAME_S),Darwin)
        CC = gcc-4.9
        OCAML_INCLUDE = /usr/local/lib/ocaml
	ARCH = osx
    else
        CC = gcc
        OCAML_INCLUDE = /usr/lib/ocaml
        EXTRA_OPTS = -ccopt -fPIC
	ARCH = x86_64
    endif
endif

LIB = $(FSTAR_HOME)/3rdparty/$(ARCH)

openssl_stub.o: openssl_stub.c
	$(OCAMLOPT) -c -cc $(CC) -ccopt "-I $(OCAML_INCLUDE)" -ccopt "-I $(OPENSSL_INCLUDE)" $(EXTRA_OPTS) $<

$(LIB)/dllopenssl_wrap.${DLL}: openssl_stub.o
	$(OCAMLMKLIB) -o $(LIB)/openssl_wrap $<

CoreCrypto.cmi: CoreCrypto.mli
	$(OCAMLC) -I $(PLATFORM) -c $<

CoreCrypto.cmo: CoreCrypto.ml
	$(OCAMLC) -I $(PLATFORM) -c $<

CoreCrypto.cma: CoreCrypto.cmo $(LIB)/dllopenssl_wrap.so
	$(OCAMLC) -I $(PLATFORM) -L$(LIB) -a -o $@ $< -dllib -lopenssl_wrap

CoreCrypto.cmx: CoreCrypto.ml CoreCrypto.cmi
	$(OCAMLOPT) -I $(PLATFORM) -c $<

CoreCrypto.cmxa: CoreCrypto.cmx $(LIB)/dllopenssl_wrap.${DLL}
	$(OCAMLOPT) -I $(PLATFORM) -a -o $@ $< -cclib -lopenssl_wrap

clean:
	rm -f Tests *.[oa] *.so *.cm[ixoa] *.cmxa *.exe

Tests: CoreCrypto.cmx $(LIB)/dllopenssl_wrap.$(DLL) Tests.ml
	$(OCAMLOPT) -ccopt "-L$(LIB)" -I $(PLATFORM) -package batteries -linkpkg -o $@ \
	$(PLATFORM)/platform.cmx $< Tests.ml \
	-cclib -lopenssl_wrap -cclib $(LIB)/libcrypto.a 

.PHONY: test

test: Tests
	@./Tests
