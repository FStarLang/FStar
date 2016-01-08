OCAMLC = ocamlfind c -g -annot
OCAMLOPT = ocamlfind opt -g -annot
OCAMLMKLIB = ocamlfind mklib
OCAMLDEP = ocamlfind dep

FSTAR_HOME = ../../..
PLATFORM = $(FSTAR_HOME)/contrib/Platform/ml

CCOPTS = # -ccopt -O0

ifeq ($(OS),Windows_NT)
    # On cygwin + cygwinports, DLLs are searched in the PATH, which is not
    # altered to include by default the mingw64 native DLLs. We also need to
    # find dllcorecrypto.dll; it is in the current directory, which Windows
    # always uses to search for DLLs.
    EXTRA_PATH = PATH="/usr/x86_64-w64-mingw32/sys-root/mingw/bin/:$(PATH)"
    EXE = .exe
    CC =
    ARCH = win32
else
    # On Unix-like systems, the library search path is LD_LIBRARY_PATH, which is
    # correctly setup to find libssleay.so and the like, but never includes the
    # current directory, which is where dllcorecrypto.so is located.
    EXTRA_PATH = LD_LIBRARY_PATH=.
    EXE =
    UNAME_S := $(shell uname -s)
    ifeq ($(UNAME_S),Darwin)
        CC = -cc gcc-5
	EXTRA_OPTS = -ccopt -L.
	ARCH = osx
    else
        CC = -cc gcc
        EXTRA_OPTS = -ccopt -fPIC -ccopt -L.
	ARCH = x86_64
    endif
endif

.PHONY: test dep

all: corecrypto.cmxa

%.o: %.c
	$(OCAMLOPT) $(CC) $(CCOPTS) $(EXTRA_OPTS) -c $<

DLL_OBJ = $(PLATFORM)/platform.cmx CoreCrypto.cmx openssl_stub.o

corecrypto.cmxa: $(DLL_OBJ)
	$(OCAMLMKLIB) -lcrypto -o corecrypto $^

DLL_DEBUG = $(PLATFORM)/platform.cmo CoreCrypto.cmo openssl_stub.o
corecrypto.cma: $(DLL_DEBUG)
	$(OCAMLMKLIB) -lcrypto -o corecrypto $^

%.cmi: %.mli
	$(OCAMLC) -I $(PLATFORM) -c $<

%.cmo: %.ml
	$(OCAMLC) -I $(PLATFORM) -c $<

%.cmx: %.ml
	$(OCAMLOPT) -I $(PLATFORM) -c $<

TEST_CMX = Tests.cmx

Tests$(EXE): $(TEST_CMX) corecrypto.cmxa
	$(OCAMLOPT) $(EXTRA_OPTS) -I $(PLATFORM) -package batteries -linkpkg -o $@ \
	corecrypto.cmxa $(TEST_CMX)

test: Tests$(EXE)
	@$(EXTRA_PATH) ./Tests$(EXE)

clean:
	rm -f Tests$(EXE) *.[oa] *.so *.cm[ixoa] *.cmxa *.exe *.dll

depend:
	$(OCAMLDEP) *.ml *.mli > .depend

include .depend
