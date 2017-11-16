.PHONY: all verify-% __force__

FSTAR_HOME=../..
include ../Makefile.include

# v_u: OAuth_User.uver

ALLFILES=AuxiliaryFunctions.fst \
Browser.StringFunctions.fst \
Web.Origin.fst \
Secret.SecString.fst \
Web.URI.fst \
Browser.AuxiliaryDatatypes.fst \
Browser.ContentSecurityPolicy.fst \
Browser.Datatypes.fst \
Browser.RequestResponseHeader.fst \
Browser.HTTPFetch.Auxiliary.fst \
Browser.HTTPFetch.fst \
Browser.Model.Interface.fst \
Example.ContentSecurityPolicy.fst \
Example.CORS.fst \

all: uall

verify-%: __force__
	$(FSTAR) --z3rlimit 100 $*

include $(FSTAR_HOME)/ulib/ml/Makefile.include

#all: uall ocaml fs clean

ulib: ../../bin/fstarlib/fstarlib.cmxa

../../bin/fstarlib/fstarlib.cmxa:
	$(MAKE) -C $(ULIB_ML)

uall: $(ALLFILES:%=verify-%)

# This target is very concise and re-uses the variables defined in
# Makefile.include. You shouldn't need to call `cp` ever.
ocaml_oauth: out OAuth.User.fst ulib
#	$(MAKE) -C $(ULIB_ML)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --z3rlimit 100 --odir out --codegen OCaml OAuth.User.fst
	$(OCAMLOPT) -I out/ ML_ExternalFunctions.ml out/FStar_List_Tot.ml out/FStar_Classical.ml out/FStar_Ref.ml out/FStar_TSet.ml out/FStar_Preorder.ml out/AuxiliaryFunctions.ml out/Web_Origin.ml out/Secret_SecString.ml out/Web_URI.ml out/Browser_AuxiliaryDatatypes.ml out/Browser_StringFunctions.ml out/Browser_Datatypes.ml out/Browser_ContentSecurityPolicy.ml out/Browser_RequestResponseHeader.ml out/Browser_HTTPFetch_Auxiliary.ml out/Browser_HTTPFetch.ml out/Browser_Model_Interface.ml out/Network_Interface.ml out/OAuth_Datatypes.ml out/OAuth_RP.ml out/OAuth_IP.ml out/OAuth_User.ml -o out/OAuth_User.exe
	./out/OAuth_User.exe

ocaml_csp: out Example.ContentSecurityPolicy.fst ulib
#	$(MAKE) -C $(ULIB_ML)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml Example.ContentSecurityPolicy.fst
	$(OCAMLOPT) -I out/ ML_ExternalFunctions.ml out/FStar_List_Tot.ml out/AuxiliaryFunctions.ml out/Web_Origin.ml out/Secret_SecString.ml out/Web_URI.ml out/Browser_AuxiliaryDatatypes.ml out/Browser_StringFunctions.ml out/Browser_Datatypes.ml out/Browser_ContentSecurityPolicy.ml out/Example_ContentSecurityPolicy.ml -o out/Example_ContentSecurityPolicy.exe
	./out/Example_ContentSecurityPolicy.exe

ocaml_cors: out Example.CORS.fst ulib
#	$(MAKE) -C $(ULIB_ML)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml Example.CORS.fst
	$(OCAMLOPT) -I out/ ML_ExternalFunctions.ml out/FStar_List_Tot.ml out/AuxiliaryFunctions.ml out/Web_Origin.ml out/Secret_SecString.ml out/Web_URI.ml out/Browser_AuxiliaryDatatypes.ml out/Browser_StringFunctions.ml out/Browser_Datatypes.ml out/Browser_ContentSecurityPolicy.ml out/Browser_RequestResponseHeader.ml out/Browser_HTTPFetch_Auxiliary.ml out/Browser_HTTPFetch.ml out/Browser_Model_Interface.ml out/Example_CORS.ml -o out/Example_CORS.exe
	./out/Example_CORS.exe

ocaml_example: out Example.Request.fst ulib
#	$(MAKE) -C $(ULIB_ML)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml Example.Request.fst
	$(OCAMLOPT) -I out/ ML_ExternalFunctions.ml out/FStar_List_Tot.ml out/AuxiliaryFunctions.ml out/Web_Origin.ml out/Secret_SecString.ml out/Web_URI.ml out/Browser_AuxiliaryDatatypes.ml out/Browser_StringFunctions.ml out/Browser_Datatypes.ml out/Browser_ContentSecurityPolicy.ml out/Browser_RequestResponseHeader.ml out/Browser_HTTPFetch_Auxiliary.ml out/Browser_HTTPFetch.ml out/Browser_Model_Interface.ml out/Network_Interface.ml out/Example_Request.ml -o out/Example_Request.exe
	./out/Example_Request.exe

LIB=../../ulib
BIN=../../bin
FSTAR=../../bin/fstar.exe
# LIB=$(FSTAR_HOME)/ulib
# BIN=$(FSTAR_HOME)/bin
# FSTAR=$(FSTAR_HOME)/bin/fstar.exe

ifeq ($(OS),Windows_NT)
FSC     = fsc --mlcompatibility $(addprefix -r , $(FS_LIBS))
else
FSC     = fsharpc --mlcompatibility $(addprefix -r , $(FS_LIBS))
endif

ifeq ($(OS),Windows_NT)
FSRUNTIME =
else
FSRUNTIME = mono
endif

FS_LIBS=$(BIN)/FSharp.PowerPack.dll

out:
	mkdir -p out

clean:
	make -C $(ULIB_ML) clean
	rm -rf out
	rm -f *~

