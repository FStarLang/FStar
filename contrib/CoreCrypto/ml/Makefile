all: CoreCrypto.cmxa

PLATFORM = ../../Platform/ml

ifeq ($(OS),Windows_NT)
    CC = i686-w64-mingw32-gcc
    OPENSSL_INCLUDE = ../../../../openssl/include
    OCAML_INCLUDE = /usr/local/lib/ocaml
    EXTRA_OPTS =
    DLL = dll #DLL file ending for windows
else
    DLL = so #DLL file ending for unix
    UNAME_S := $(shell uname -s)
    ifeq ($(UNAME_S),Darwin)
        CC = gcc-4.9 # Change if necessary
        OPENSSL_INCLUDE = ../../../../openssl/include
        OCAML_INCLUDE = /usr/local/lib/ocaml
        EXTRA_OPTS =
    else
        CC = gcc
        OPENSSL_INCLUDE = /usr/include/openssl
        OCAML_INCLUDE = /usr/lib/ocaml
        EXTRA_OPTS = -ccopt -fPIC
    endif
endif

openssl_stub.o: openssl_stub.c
	ocamlopt -c -cc $(CC) -ccopt "-I $(OCAML_INCLUDE)" -ccopt "-I $(OPENSSL_INCLUDE)" $(EXTRA_OPTS) -cclib -lopenssl -cclib -c $<
# haven't decided yet which style is better. It may interact slightly differently with flexlink.
#	ocamlopt -c -cc "$(CC) -I /usr/local/lib/ocaml -I ../../../../openssl-1.0.1p/include -lcrypto -c" $<
#	ocamlopt -c -cclib -lcrypto -cclib -lopenssl $< -ccopt -static

dllopenssl_wrap.${DLL}: openssl_stub.o
	ocamlmklib -o openssl_wrap $<

CoreCrypto.cmi: CoreCrypto.mli
	ocamlc -I $(PLATFORM) -c CoreCrypto.mli

CoreCrypto.cmo: CoreCrypto.ml openssl.cmi
	ocamlc -I $(PLATFORM) -c CoreCrypto.ml openssl.cmi

CoreCrypto.cma:  CoreCrypto.cmo dllopenssl_wrap.so
	ocamlc -I $(PLATFORM) -a -o $@ $< -dllib -lopenssl_wrap

CoreCrypto.cmx: CoreCrypto.ml CoreCrypto.cmi
	ocamlopt -I $(PLATFORM) -c $<

CoreCrypto.cmxa: CoreCrypto.cmx dllopenssl_wrap.${DLL}
	ocamlopt -I $(PLATFORM) -a -o $@ $< -cclib -lopenssl_wrap

stub: openssl_stub.o

clean:
	rm -f *.[oa] *.so *.cm[ixoa] *.cmxa

distclean: clean
	rm -f *.dll


Tests: CoreCrypto.cmx Tests.ml
	ocamlfind ocamlopt -I $(PLATFORM) -I . -package Unix -linkpkg -o $@ \
	$(PLATFORM)/platform.cmx $^ \
	-cclib -lopenssl_wrap -cclib $(OPENSSL_INCLUDE)/../libcrypto.a

.PHONY: test

test: Tests
	@./Tests
