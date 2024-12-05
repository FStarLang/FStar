FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

OTHERFLAGS += --include $(FSTAR_ROOT)/contrib/Platform/fst
OTHERFLAGS += --include $(FSTAR_ROOT)/contrib/CoreCrypto/fst

all: # RPC.ml CntProtocol.ml

# NOTE: This makefile used to extract and test these programs at some
# point, but it has not been working (nor being run) for a while. It
# also referecenes $(FSTAR_ALWAYS) which is not defined anywhere since
# 2021. I'm retaining these old rules for reference but we are currently
# doing verification only.

# To be ported maybe:
#   Bloom.*
#   Cert.Cert
#   Cert.DSA
#   Cert.Sig

# LIB = $(FSTAR_UCONTRIB)/CoreCrypto/ml

# ifeq ($(OS),Windows_NT)
#     EXTRA_PATH = PATH="/usr/x86_64-w64-mingw32/sys-root/mingw/bin/:$(PATH)"
# else
#     EXTRA_PATH = LD_LIBRARY_PATH=.:$(LIB)
#     UNAME_S := $(shell uname -s)
# endif

# uall: $(VERFILES:%=verify-%) $(HH_VERFILES:%=verify_hh-%) RPC.ml CntProtocol.ml

# RPC.ml: SHA1.fst MAC.fst Formatting.fst RPC.fst
# 	$(FSTAR_ALWAYS) --no_location_info --lax \
# 	 	$(FSTAR_INCLUDE_PATHS) \
# 		RPC.fst \
# 		--codegen-lib Platform --codegen-lib CoreCrypto --codegen-lib Seq --codegen OCaml

# CntProtocol.ml: SHA1.fst MAC.fst CntFormat.fst CntProtocol.fst
# 	$(FSTAR_ALWAYS) --no_location_info --lax \
# 		$(FSTAR_INCLUDE_PATHS) \
# 		CntProtocol.fst \
# 		--codegen-lib Platform --codegen-lib CoreCrypto --codegen-lib Seq --codegen OCaml

# OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_UCONTRIB)/Platform/ml $(FSTAR_UCONTRIB)/CoreCrypto/ml)

# CONTRIB_LIBS=$(FSTAR_UCONTRIB)/CoreCrypto/ml/CoreCrypto.cmxa

# include $(FSTAR_ULIB)/ml/Makefile.include

# $(CONTRIB_LIBS):
# 	+$(MAKE) -C $(FSTAR_UCONTRIB)

# RPC.exe: RPC.ml $(CONTRIB_LIBS)
# 	$(OCAMLOPT) -thread -o $@ $(OCAML_INCLUDE_PATHS) $(CONTRIB_LIBS) SHA1.ml MAC.ml Formatting.ml RPC.ml

# rpc-test: RPC.exe
# 	$(EXTRA_PATH) ./RPC.exe

# CntProtocol.exe: CntProtocol.ml $(CONTRIB_LIBS)
# 	$(OCAMLOPT) -thread -o $@ $(OCAML_INCLUDE_PATHS) $(CONTRIB_LIBS) SHA1.ml MAC.ml CntFormat.ml CntProtocol.ml

# cnt-test: CntProtocol.exe
# 	$(EXTRA_PATH) ./CntProtocol.exe

# clean:
# 	rm -fr RPC *.ml *.cmi *.cmx *.o *.exe *~
