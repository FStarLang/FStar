OCAMLC = ocamlfind c
OCAMLOPT = ocamlfind opt
OCAMLMKLIB = ocamlfind mklib
OCAMLDEP = ocamlfind dep

FSTAR_HOME = ../../..
PLATFORM = $(FSTAR_HOME)/contrib/Platform/ml

CCOPTS = # -ccopt -O0

ifeq ($(OS),Windows_NT)
    EXE = .exe
    DLL = dll
    CC =
    OCAML_INCLUDE =
    ARCH = win32
else
    EXE =
    DLL = so
    UNAME_S := $(shell uname -s)
    ifeq ($(UNAME_S),Darwin)
        CC = -cc gcc-5
	ARCH = osx
    else
        CC = -cc gcc
        EXTRA_OPTS = -ccopt -fPIC
	ARCH = x86_64
    endif
endif

.PHONY: test dep

all: CoreCrypto.cmxa

%.o: %.c
	$(OCAMLOPT) $(CC) $(CCOPTS) $(EXTRA_OPTS) -c $<

dllopenssl_stubs.$(DLL): openssl_stub.o
	$(OCAMLMKLIB) -lcrypto -lssl -o openssl_stubs $<

%.cmxa: %.cmx dllopenssl_stubs.$(DLL)
	$(OCAMLOPT) -a -o $@ $< -cclib -lopenssl_stubs

%.cmi: %.mli
	$(OCAMLC) -I $(PLATFORM) -c $<

%.cmo: %.ml
	$(OCAMLC) -I $(PLATFORM) -c $<

%.cmx: %.ml
	$(OCAMLOPT) -I $(PLATFORM) -c $<

# Note: because there is no .cmxa generated for [openssl_stubs], the final
# invocation has no way to know that we need -lcrypto and -lssl. If this changes
# in the future, the rule below can be simplified.
Tests$(EXE): $(PLATFORM)/platform.cmx CoreCrypto.cmx Tests.cmx openssl_stub.o
	$(OCAMLOPT) -I $(PLATFORM) -package batteries -linkpkg -o $@ \
	$^ libcrypto.a libssl.a libz.a libgdi32.a

test: Tests$(EXE)
	@./Tests$(EXE)

clean:
	rm -f Tests$(EXE) *.[oa] *.so *.cm[ixoa] *.cmxa *.exe

depend:
	$(OCAMLDEP) *.ml *.mli > .depend

include .depend
