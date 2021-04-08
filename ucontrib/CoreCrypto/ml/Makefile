CONTRIB?=../..
PLATFORM = $(CONTRIB)/Platform/ml
DB=db
INCLUDE=-package batteries,zarith -I $(PLATFORM) -I $(DB)
MARCH?=x86_64

OCAMLC = ocamlfind c $(INCLUDE) -g -annot
OCAMLOPT = ocamlfind opt $(INCLUDE) -g -annot
OCAMLMKLIB = ocamlfind mklib $(INCLUDE)
OCAMLDEP = ocamlfind dep -slash

CCOPTS = $(addprefix -ccopt ,-Wall -std=c11 -D__USE_MINGW_ANSI_STDIO -Lopenssl -Iopenssl/include)
CCLIBS = $(addprefix -cclib ,-lcrypto)

ifeq ($(OS),Windows_NT)
    # On cygwin + cygwinports, DLLs are searched in the PATH, which is not
    # altered to include by default the mingw64 native DLLs. We also need to
    # find dllcorecrypto.dll; it is in the current directory, which Windows
    # always uses to search for DLLs.
    EXTRA_PATH = PATH="/usr/$(MARCH)-w64-mingw32/sys-root/mingw/bin/:$(PATH)"
    ARCH = win32
    EXTRA_OPTS =
    EXTRA_LIBS = -L.
    ifeq ($(MARCH),x86_64)
      OPENSSL_CONF = CC=x86_64-w64-mingw32-gcc ./Configure mingw64 enable-tls1_3
    else
      OPENSSL_CONF = CC=i686-w64-mingw32-gcc ./Configure mingw enable-tls1_3
    endif
else
    # On Unix-like systems, the library search path is LD_LIBRARY_PATH, which is
    # correctly setup to find libssleay.so and the like, but never includes the
    # current directory, which is where dllcorecrypto.so is located.
    EXTRA_PATH = LD_LIBRARY_PATH=.
    UNAME_S := $(shell uname -s)
    ifeq ($(UNAME_S),Darwin)
        EXTRA_OPTS =
        EXTRA_LIBS = -L.
        ARCH = osx
        OPENSSL_CONF = ./config enable-tls1_3
    else
        EXTRA_OPTS = -thread -ccopt -fPIC
        EXTRA_LIBS = -L.
        ARCH = x86_64
	# The HACL* test engine directly links with the .o files
        OPENSSL_CONF = ./config enable-tls1_3 -fPIC
    endif
endif

.PHONY: test dep

all: CoreCrypto.cmxa

openssl_stub.o: libcrypto.a openssl_stub.c
	$(OCAMLOPT) $(CCOPTS) $(EXTRA_OPTS) -c openssl_stub.c

%.cmi: %.mli
	$(OCAMLC) -c $<

%.cmo: %.ml
	$(OCAMLC) -c $<

%.cmx: %.ml
	$(OCAMLOPT) -c $<

$(PLATFORM)/platform.cmx: $(PLATFORM)/platform.ml
	$(MAKE) -C $(PLATFORM)

$(DB)/DB.cmx: $(DB)/DB.ml
	$(MAKE) -C $(DB)

openssl/Configure:
	echo "openssl folder is empty, running git submodule update... no recursion"
	git submodule update --init

openssl/libcrypto.a: openssl/Configure
	cd openssl && $(OPENSSL_CONF) && $(MAKE) build_libs

libcrypto.a: openssl/libcrypto.a
	cp openssl/libcrypto.a .

DLL_OBJ = $(PLATFORM)/platform.cmx CoreCrypto.cmx openssl_stub.o # $(DB)/DB.cmx DHDB.cmx
CoreCrypto.cmxa: $(DLL_OBJ)
	$(OCAMLMKLIB) $(EXTRA_LIBS) $(CCLIBS) -o CoreCrypto $(DLL_OBJ)

DLL_BYTE = $(PLATFORM)/platform.cmo CoreCrypto.cmo openssl_stub.o # DHDB.cmo $(DB)/DB.cmo
CoreCrypto.cma: $(DLL_BYTE)
	$(OCAMLMKLIB) $(EXTRA_LIBS) -o CoreCrypto $^

TEST_CMX = Tests.cmx
Tests.exe: CoreCrypto.cmxa $(TEST_CMX)
	$(OCAMLOPT) $(EXTRA_OPTS) -I $(PLATFORM) -package batteries,zarith -linkpkg -o $@ \
	CoreCrypto.cmxa $(TEST_CMX)

test: Tests.exe
	@$(EXTRA_PATH) ./Tests.exe

clean:
	$(MAKE) -C $(DB) clean
	$(MAKE) -C $(PLATFORM) clean
	rm -f Tests.exe *.[oa] *.so *.cm[ixoa] *.cmxa *.exe *.dll *.annot *~

depend:
	$(OCAMLDEP) -I $(PLATFORM) -I $(DB) *.ml *.mli > .depend

include .depend

valgrind: Tests$(EXE)
	valgrind --leak-check=yes --suppressions=suppressions ./Tests$(EXE)
