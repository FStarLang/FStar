.PHONY: all verify-% __force__

# To be ported maybe:
#   Bloom.*
#   Cert.Cert
#   Cert.DSA
#   Cert.Sig

VERFILES=AES.fst \
Encrypt_SymEnc.fst\
Encrypt_Sample.fst \
SHA1.fst \
MAC.fst \
Sig.fst \
Cert.ACLs.fst \
Cap.fst \
Formatting.fst \
SHA1.fst \
MAC.fst \
RPC.fst \
CntFormat.fst \
CntProtocol.fst

HH_VERFILES= \
EtM.Plain.fst \
EtM.MAC.fst \
EtM.CPA.fst \
EtM.AE.fst \
HyE.RSA.fst \
HyE.PlainPKE.fst \
HyE.Plain.fst \
HyE.AE.fst \
HyE.CCA2.fst \
HyE.HCCA2.fst

LIB = ../../ucontrib/CoreCrypto/ml

ifeq ($(OS),Windows_NT)
    EXTRA_PATH = PATH="/usr/x86_64-w64-mingw32/sys-root/mingw/bin/:$(PATH)"
else
    EXTRA_PATH = LD_LIBRARY_PATH=.:$(LIB)
    UNAME_S := $(shell uname -s)
endif

FSTAR_HOME=../..

include ../Makefile.include

OTHERFLAGS += --use_extracted_interfaces true

FSTAR_INCLUDE_PATHS=--include $(FSTAR_HOME)/ucontrib/Platform/fst --include $(FSTAR_HOME)/ucontrib/CoreCrypto/fst	      

%.fst-in: 
	@echo $(FSTAR_INCLUDE_PATHS) \
	      --z3rlimit 20 \
	      --use_hints

verify-%: __force__
	$(FSTAR) $(FSTAR_INCLUDE_PATHS) \
		 --z3rlimit 20 $*

verify_hh-%: __force__
	$(FSTAR) $(FSTAR_INCLUDE_PATHS) \
		 --z3rlimit 20 $*

all: uall

uall: $(VERFILES:%=verify-%) $(HH_VERFILES:%=verify_hh-%) RPC.ml CntProtocol.ml

RPC.ml: SHA1.fst MAC.fst Formatting.fst RPC.fst
	$(FSTAR_ALWAYS) --no_location_info --lax \
	 	$(FSTAR_INCLUDE_PATHS) \
		RPC.fst \
		--codegen-lib Platform --codegen-lib CoreCrypto --codegen-lib Seq --codegen OCaml

CntProtocol.ml: SHA1.fst MAC.fst CntFormat.fst CntProtocol.fst
	$(FSTAR_ALWAYS) --no_location_info --lax \
		$(FSTAR_INCLUDE_PATHS) \
		CntProtocol.fst \
		--codegen-lib Platform --codegen-lib CoreCrypto --codegen-lib Seq --codegen OCaml

OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_HOME)/ucontrib/Platform/ml $(FSTAR_HOME)/ucontrib/CoreCrypto/ml)

CONTRIB_LIBS=$(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.cmxa

include $(FSTAR_HOME)/ulib/ml/Makefile.include

#OCAMLC automatically contains fstarlib
SUPPORT_LIBS=$(FSTARLIB_DIR)/fstarlib.cmxa

$(CONTRIB_LIBS):
	$(MAKE) -C $(FSTAR_HOME)/ucontrib/

RPC.exe: RPC.ml $(CONTRIB_LIBS)
	$(OCAMLC) -o $@ $(OCAML_INCLUDE_PATHS) $(CONTRIB_LIBS) SHA1.ml MAC.ml Formatting.ml RPC.ml

rpc-test: RPC.exe
	$(EXTRA_PATH) ./RPC.exe

CntProtocol.exe: CntProtocol.ml $(CONTRIB_LIBS)
	$(OCAMLC) -o $@ $(OCAML_INCLUDE_PATHS) $(CONTRIB_LIBS) SHA1.ml MAC.ml CntFormat.ml CntProtocol.ml

cnt-test: CntProtocol.exe
	$(EXTRA_PATH) ./CntProtocol.exe

deploy-tutorial:
	cp EtM.AE.fst  EtM.CPA.fst  EtM.Ideal.fsti  EtM.MAC.fst  EtM.Plain.fst ../../doc/tutorial/code/solutions/
	cp EtM.AE.fst  EtM.CPA.fst  EtM.Ideal.fsti  EtM.MAC.fst  EtM.Plain.fst ../../doc/tutorial/code/exercises/

clean:
	rm -fr RPC *.ml *.cmi *.cmx *.o *.exe *~
