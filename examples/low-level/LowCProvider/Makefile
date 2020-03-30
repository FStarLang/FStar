FSTAR_HOME = ../../..
CONTRIB=ucontrib
PLATFORM = $(FSTAR_HOME)/$(CONTRIB)/Platform/ml
CORECRYPTO = $(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/ml
INCLUDE=-package batteries,zarith -I $(PLATFORM) -I $(CORECRYPTO)
MARCH?=x86_64

KREMLIN_HOME?=../../../../kremlin
KRML_INCLUDES=$(addprefix -I ,.. $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/test)
KRML_ARGS=-verbose -ccopt -Wno-error=pointer-sign $(KOPTS)
KRML=$(KREMLIN_HOME)/krml $(KRML_ARGS) $(KRML_INCLUDES)

OCAMLC = ocamlfind c $(INCLUDE) -g -annot
OCAMLOPT = ocamlfind opt $(INCLUDE) -g -annot
OCAMLMKLIB = ocamlfind mklib $(INCLUDE)
OCAMLDEP = ocamlfind dep

CCOPTS = $(addprefix -ccopt ,-Wall -std=c11 -D__USE_MINGW_ANSI_STDIO)
CCLIBS = $(addprefix -cclib ,-L.)

ifeq ($(OS),Windows_NT)
    # On cygwin + cygwinports, DLLs are searched in the PATH, which is not
    # altered to include by default the mingw64 native DLLs. We also need to
    # find dllcorecrypto.dll; it is in the current directory, which Windows
    # always uses to search for DLLs.
    EXTRA_PATH = PATH="/usr/$(MARCH)-w64-mingw32/sys-root/mingw/bin/:$(PATH)"
    ARCH = win32
    EXTRA_OPTS =
    EXTRA_LIBS = -L.
    AR = $(MARCH)-w64-mingw32-ar
else
    EXTRA_PATH = LD_LIBRARY_PATH=.
    UNAME_S := $(shell uname -s)
    AR = ar
    ifeq ($(UNAME_S),Darwin)
        EXTRA_OPTS =
        EXTRA_LIBS = -L.
        ARCH = osx
    else
        EXTRA_OPTS = -thread -ccopt -fPIC
        EXTRA_LIBS = -L.
        ARCH = x86_64
    endif
endif

.PHONY: test dep

all: ../krml-test.exe ../spartan_aes/aes.o LowCProvider.cmxa

../spartan_aes/aes.o:
	+$(MAKE) -C ../spartan_aes

../krml-test.exe: $(wildcard ../crypto/*.fst)
	+$(MAKE) -C .. krml-test.exe

%.cmi: %.mli
	$(OCAMLC) -c $<

%.cmo: %.ml
	$(OCAMLC) -c $<

%.cmx: %.ml
	$(OCAMLOPT) -c $<

$(CORECRYPTO)/CoreCrypto.cmx: $(CORECRYPTO)/CoreCrypto.ml
	+$(MAKE) -C $(CORECRYPTO)



libllcrypto.a: ../krml-test.exe
	$(AR) -cr libllcrypto.a ../spartan_aes/aes.o ../tmp/*.o
	$(AR) -d libllcrypto.a Crypto_KrmlTest.o

lowc_stub.o: libllcrypto.a
	$(OCAMLOPT) $(CCOPTS) $(EXTRA_OPTS) $(KRML_INCLUDES) -c lowc_stub.c

LowCProvider.cmxa: $(CORECRYPTO)/CoreCrypto.cmx libllcrypto.a lowc_stub.o LowCProvider.cmx
	$(OCAMLMKLIB) $(EXTRA_LIBS) $(CCLIBS) -o LowCProvider $^

Tests.exe: LowCProvider.cmxa Tests.cmx
	$(OCAMLOPT) $(EXTRA_OPTS) -I $(PLATFORM) -package batteries,zarith -linkpkg -o $@ libllcrypto.a lowc_stub.o CoreCrypto.cmxa LowCProvider.cmx Tests.cmx

clean:
	+$(MAKE) -C $(PLATFORM) clean
	+$(MAKE) -C $(CORECRYPTO) clean
	rm -fr tmp
	rm -f Tests.exe *.[oa] *.so *.cm[ixoa] *.cmxa *.exe *.dll *.annot *~

.depend: depend

depend:
	$(OCAMLDEP) *.ml *.mli > .depend

include .depend
