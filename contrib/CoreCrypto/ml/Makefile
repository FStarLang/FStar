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

all: corecrypto.cmxa

%.o: %.c
	$(OCAMLOPT) $(CC) $(CCOPTS) $(EXTRA_OPTS) -c $<

DLL_OBJ = $(PLATFORM)/platform.cmx CoreCrypto.cmx openssl_stub.o

dllcorecrypto.$(DLL) corecrypto.cmxa: $(DLL_OBJ)
	$(OCAMLMKLIB) -lcrypto -lssl -o corecrypto $^

%.cmi: %.mli
	$(OCAMLC) -I $(PLATFORM) -c $<

%.cmo: %.ml
	$(OCAMLC) -I $(PLATFORM) -c $<

%.cmx: %.ml
	$(OCAMLOPT) -I $(PLATFORM) -c $<

TEST_CMX = Tests.cmx

# Static linking for Windows (until I figure out whether we want dynamic
# linking, and if so, how to do it).
Tests.exe: $(DLL_OBJ) $(TEST_CMX)
	$(OCAMLOPT) -I $(PLATFORM) -package batteries -linkpkg -o $@ \
	$^ libcrypto.a libssl.a libz.a libgdi32.a

# Dynamic linking for others.
Tests: $(TEST_CMX) corecrypto.cmxa dllcorecrypto.$(DLL)
	$(OCAMLOPT) -I $(PLATFORM) -package batteries -linkpkg -o $@ \
	-cclib dllcorecrypto.$(DLL) corecrypto.cmxa $(TEST_CMX)

test: Tests$(EXE)
	@LD_LIBRARY_PATH=. ./Tests$(EXE)

clean:
	rm -f Tests$(EXE) *.[oa] *.so *.cm[ixoa] *.cmxa *.exe *.dll

depend:
	$(OCAMLDEP) *.ml *.mli > .depend

include .depend
