.PHONY: all verify-% __force__

BOX_VERFILES= \
Box.PlainDH.fst \
Box.PlainPKAE.fst \
Box.PlainAE.fst \
Box.AE.fst \
Box.DH.fst \
Box.PKAE.fst \
Box.Indexing.fst \
Box.Flags.fsti

LIB = ../../contrib/CoreCrypto/ml

ifeq ($(OS),Windows_NT)
  EXTRA_PATH = PATH="/usr/x86_64-w64-mingw32/sys-root/mingw/bin/:$(PATH)"
else
    EXTRA_PATH = LD_LIBRARY_PATH=.:$(LIB)
    UNAME_S := $(shell uname -s)
endif

FSTAR_HOME=../../../
include ../../Makefile.include

%.fst-in: 
	@echo --include $(FSTAR_HOME)/ulib/hyperstack \
	      --include $(FSTAR_HOME)/ucontrib/Platform/fst \
	      --include $(FSTAR_HOME)/ucontrib/CoreCrypto/fst \
	      --z3rlimit 20
	      --verify_module $(basename $(notdir $@))

verify-%: __force__
	$(FSTAR) --include $(FSTAR_HOME)/ucontrib/Platform/fst \
		 --include $(FSTAR_HOME)/ucontrib/CoreCrypto/fst \
		 --z3rlimit 20 $*

verify_hh-%: __force__
	$(FSTAR) --include $(FSTAR_HOME)/ulib/hyperstack \
		 --include $(FSTAR_HOME)/ucontrib/Platform/fst \
		 --include $(FSTAR_HOME)/ucontrib/CoreCrypto/fst \
		 --z3rlimit 20 $*

box: $(BOX_VERFILES:%=verify_hh-%)



export CONTRIB=../../contrib


.PHONY: mllibs

mllibs:
	$(MAKE) -C $(FSTAR_HOME)/contrib/Platform/ml clean all
	$(MAKE) -C $(FSTAR_HOME)/contrib/CoreCrypto/ml clean all test


OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_HOME)/contrib/Platform/ml $(FSTAR_HOME)/contrib/CoreCrypto/ml $(FSTAR_HOME)/ulib/ml/native_int $(FSTAR_HOME)/ulib/ml)
OCAMLC=ocamlfind ocamlopt -ccopt -L$(LIB) -package batteries -linkpkg -g -thread
SUPPORT_LIBS=$(addprefix $(FSTAR_HOME)/ulib/ml/, MkPrims.ml native_int/prims.ml FStar_ST.ml FStar_All.ml FStar_List.ml FStar_Char.ml FStar_String.ml FStar_IO.ml)
CONTRIB_LIBS=$(addprefix $(FSTAR_HOME)/contrib/, CoreCrypto/ml/CoreCrypto.cmxa)

$(CONTRIB_LIBS):
	$(MAKE) -C $(FSTAR_HOME)/contrib/


clean:
	rm -fr *.ml *.cmi *.cmx *.o *.exe *~
