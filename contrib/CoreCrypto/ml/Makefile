all: CoreCrypto.cmxa

ifeq ($(OS),Windows_NT)
    CC = i686-w64-mingw32-gcc
    OPENSSL_INCLUDE = ../../../../openssl/include
    OCAML_INCLUDE = /usr/local/lib/ocaml
else
    UNAME_S := $(shell uname -s)
    ifeq ($(UNAME_S),Darwin)
        CC = gcc-5
        OPENSSL_INCLUDE = /usr/include
        OCAML_INCLUDE = /usr/local/lib/ocaml
    else
        CC = gcc
        OPENSSL_INCLUDE = /usr/include/openssl
        OCAML_INCLUDE = /usr/lib/ocaml
    endif
endif

openssl_stub.o: openssl_stub.c
	ocamlopt -c -cc $(CC) -ccopt '-I $(OCAML_INCLUDE)' -ccopt "-I $(OPENSSL_INCLUDE)" -ccopt -fPIC -cclib -lcrypto -cclib -c $<
# haven't decided yet which style is better. It may interact slightly differently with flexlink.
#	ocamlopt -c -cc "$(CC) -I /usr/local/lib/ocaml -I ../../../../openssl-1.0.1p/include -lcrypto -c" $<
#	ocamlopt -c -cclib -lcrypto -cclib -lopenssl $< -ccopt -static

dllopenssl_wrap.so: openssl_stub.o
	ocamlmklib  -o  openssl_wrap  $<

CoreCrypto.cmi: CoreCrypto.mli
	ocamlc -I ../../Platform/ml -c CoreCrypto.mli

CoreCrypto.cmo: CoreCrypto.ml openssl.cmi
	ocamlc -I ../../Platform/ml -c CoreCrypto.ml openssl.cmi

CoreCrypto.cma:  CoreCrypto.cmo  dllopenssl_wrap.so
	ocamlc -I ../../Platform/ml -a  -o $@  $<  -dllib -lopenssl_wrap

CoreCrypto.cmx: CoreCrypto.ml CoreCrypto.cmi
	ocamlopt -I ../../Platform/ml -c $<

CoreCrypto.cmxa: CoreCrypto.cmx  dllopenssl_wrap.so
	ocamlopt -I ../../Platform/ml -a  -o $@  $<  -cclib -lopenssl_wrap

clean:
	rm -f *.[oa] *.so *.cm[ixoa] *.cmxa
