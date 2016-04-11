# Problems with this makefile:
# - make a.out only works after a call to "make"
# - make a.out copies files around (discouraged! buid a cmxa for the ml/
#   directory instead and a recursive call to make)
# - the Makefile does not use auto-deps and breaks all the time; switch to
#   auto-deps!
FSTAR_HOME=../..
include ../Makefile.include

all:
	make api
ifneq ($(shell $(FSTAR_HOME)/bin/fstar.exe --version | grep platform= | cut -c10-),Windows_x86)
# This runs out of memory with 32bit Windows binaries
	make theory
endif
	make traces
	make crypto
	make secserver
	make codegen SMCIF=examples/fstar_main/dealiface.fsti SMCMAIN=examples/fstar_main/dealmain.fst
# make distclean

EXAMPLES_DIR=./examples

api:
	make -C examples api FSTAR="$(FSTAR)"

theory:
	export CONTRIB=../../contrib
	$(FSTAR) --explicit_deps \
	      --z3timeout 10 --__temp_no_proj PSemantics --__temp_no_proj Metatheory \
	  FStar.FunctionalExtensionality.fst FStar.Classical.fst FStar.Ghost.fst FStar.List.Tot.fst FStar.Set.fst \
	  FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Seq.fst FStar.SeqProperties.fst FStar.OrdSet.fst FStar.OrdMap.fst \
	  FStar.Constructive.fst prins.fsti FStar.UInt8.fst FStar.Char.fsti $(CONTRIB)/Platform/fst/Platform.Bytes.fst ast.fst ffibridge.fsti sem.fst psem.fst \
	  theory.fst

traces:
	$(FSTAR) --z3timeout 10 --explicit_deps  FStar.Seq.fst FStar.Matrix2.fsti examples/fstar_main/traces.fst

crypto:
	export CONTRIB=../../contrib
	$(FSTAR) --explicit_deps \
	       --__temp_no_proj PSemantics --verify_module Crypto \
	FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Seq.fst FStar.SeqProperties.fst FStar.Ghost.fst FStar.List.Tot.fst FStar.OrdSet.fst FStar.OrdMap.fst FStar.List.fst \
	FStar.Float.fsti FStar.IO.fsti FStar.Char.fsti FStar.String.fsti prins.fst FStar.UInt8.fst $(CONTRIB)/Platform/fst/Platform.Bytes.fst ast.fst ffibridge.fsti sem.fst psem.fst runtime.fsti print.fst $(CONTRIB)/CoreCrypto/fst/CoreCrypto.fst ../crypto/sha1.fst

secserver:
	export CONTRIB=../../contrib
	$(FSTAR) --explicit_deps \
	         --__temp_no_proj  PSemantics --__temp_no_proj SecServer --verify_module SecServer \
						FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fst \
						FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Seq.fst \
						FStar.SeqProperties.fst FStar.Ghost.fst FStar.Squash.fsti FStar.List.Tot.fst \
						FStar.OrdSet.fst FStar.OrdMap.fst FStar.List.fst FStar.Float.fsti FStar.IO.fsti \
						FStar.Char.fsti FStar.String.fsti \
						prins.fst FStar.UInt8.fst $(CONTRIB)/Platform/fst/Platform.Bytes.fst ast.fst \
						ffibridge.fsti sem.fst psem.fst rtheory.fst runtime.fsti print.fst hashtable.fsti \
						ckt.fst $(CONTRIB)/CoreCrypto/fst/CoreCrypto.fst ../crypto/sha1.fst crypto.fst \
						interpreter.fst

OUTPUT_DIR=./ocaml-output

CONTRIB=$(FSTAR_HOME)/contrib

CODEGEN_FLAGS=   --no_location_info --use_native_int \
                 --codegen-lib Platform --codegen-lib CoreCrypto --codegen OCaml --odir $(OUTPUT_DIR)\
                 --__temp_no_proj PSemantics --__temp_no_proj SecServer

FSTAR_LIB_FILES=FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Seq.fst FStar.SeqProperties.fst FStar.Ghost.fst FStar.Squash.fsti\
                FStar.List.Tot.fst FStar.List.fst FStar.ListProperties.fst FStar.OrdSet.fst FStar.OrdMap.fst FStar.Float.fsti FStar.IO.fsti FStar.Char.fsti FStar.String.fsti hashtable.fsti\

# removed sha1, CoreCrypto, crypto, and sec_server
INTERPRETER_FILES=prins.fst FStar.UInt8.fst $(CONTRIB)/Platform/fst/Platform.Bytes.fst ast.fst ffibridge.fsti sem.fst psem.fst rtheory.fst \
                  runtime.fsti print.fst ckt.fst\
                  interpreter.fst examples/ffi.fst prog.fsti
# INTERPRETER_FILES=prins.fst $(CONTRIB)/Platform/fst/Platform.Bytes.fst ast.fst ffibridge.fsti sem.fst psem.fst rtheory.fst \
#                   runtime.fsti print.fst ckt.fst $(CONTRIB)/CoreCrypto/fst/CoreCrypto.fst ../crypto/sha1.fst crypto.fst\
#                   interpreter.fst sec_server.fst examples/ffi.fst prog.fsti

#SMCIF and SMCMain are set from command line invocation of make
codegen:
	cp $(SMCIF) smciface.fsti
	cp $(SMCMAIN) smc_main.fst
	$(FSTAR_ALWAYS) --explicit_deps $(CODEGEN_FLAGS) $(EXTERNAL_FLAGS) $(FSTAR_LIB_FILES) $(INTERPRETER_FILES) smciface.fsti smc_main.fst

# codegen:
# 	$(FSTAR)       \
#                  --codegen-lib Platform --codegen-lib CoreCrypto --codegen OCaml --odir $(OUTPUT_DIR) --use_native_int --__temp_no_proj PSemantics --__temp_no_proj SecServer\
#                  FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Seq.fst FStar.SeqProperties.fst FStar.Ghost.fst FStar.Squash.fsti\
#                  FStar.List.Tot.fst FStar.List.fst FStar.ListProperties.fst ordset.fsti FStar.OrdSet.fst ordmap.fsti FStar.OrdMap.fst FStar.IO.fsti string.fsti\
#                  prins.fst ast.fst ffibridge.fsti sem.fst psem.fst rtheory.fst $(CONTRIB)/Platform/fst/Platform.Bytes.fst runtime.fsti print.fst ckt.fst $(CONTRIB)/CoreCrypto/fst/CoreCrypto.fst ../crypto/sha1.fst crypto.fst interpreter.fst sec_server.fst examples/ffi.fst prog.fsti main.fst 

a.out:
	make -C $(OUTPUT_DIR) a.out

clean:
	make -C $(OUTPUT_DIR) clean

distclean:
	rm -f smciface.fsti smc_main.fst
	make -C $(OUTPUT_DIR) distclean
