include ../Makefile.include

all:
# make api
ifneq ($(shell fstar.exe --version | grep platform= | cut -c10-),Windows_x86)
# This runs out of memory with 32bit Windows binaries
	make theory
endif
	make traces
	make crypto
	make secserver
# make codegen SMCIF=examples/fstar_main/dealiface.fsi SMCMAIN=examples/fstar_main/dealmain.fst
# make distclean

EXAMPLES_DIR=./examples

api:
	make -C examples api FSTAR='../$(FSTAR)'

theory:
	export CONTRIB=../../contrib
	$(FSTAR) --explicit_deps \
	  --admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi Prins --admit_fsi Ffibridge --z3timeout 10 --__temp_no_proj PSemantics --__temp_no_proj Metatheory \
	  FStar.FunctionalExtensionality.fst FStar.Classical.fst FStar.Ghost.fst FStar.List.Tot.fst FStar.Set.fst \
	  FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Seq.fst FStar.SeqProperties.fst ordset.fsi ordmap.fsi \
	  FStar.Constructive.fst prins.fsi $(CONTRIB)/Platform/fst/Platform.Bytes.fst ast.fst ffibridge.fsi sem.fst psem.fst \
	  theory.fst

traces:
	$(FSTAR) --z3timeout 10 --explicit_deps --admit_fsi FStar.Matrix2 FStar.Seq.fst FStar.Matrix2.fsti examples/fstar_main/traces.fst

crypto:
	export CONTRIB=../../contrib
	$(FSTAR) --explicit_deps \
	--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap  --admit_fsi Ffibridge --admit_fsi Runtime --admit_fsi FStar.IO --admit_fsi FStar.String --__temp_no_proj PSemantics --verify_module Crypto \
	FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Seq.fst FStar.SeqProperties.fst FStar.Ghost.fst FStar.List.Tot.fst ordset.fsi ordmap.fsi FStar.List.fst \
	FStar.IO.fsti FStar.String.fst prins.fst $(CONTRIB)/Platform/fst/Platform.Bytes.fst ast.fst ffibridge.fsi sem.fst psem.fst runtime.fsi print.fst $(CONTRIB)/CoreCrypto/fst/CoreCrypto.fst ../crypto/sha1.fst

secserver:
	export CONTRIB=../../contrib
	$(FSTAR) --explicit_deps \
	--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap  --admit_fsi Ffibridge --admit_fsi Runtime --admit_fsi FStar.IO --admit_fsi FStar.String --admit_fsi FStar.Squash --admit_fsi Hashtable --__temp_no_proj  PSemantics --__temp_no_proj SecServer --verify_module SecServer \
	FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Seq.fst FStar.SeqProperties.fst FStar.Ghost.fst FStar.Squash.fsti FStar.List.Tot.fst ordset.fsi ordmap.fsi FStar.List.fst FStar.IO.fsti string.fsi prins.fst $(CONTRIB)/Platform/fst/Platform.Bytes.fst ast.fst ffibridge.fsi sem.fst psem.fst rtheory.fst runtime.fsi print.fst hashtable.fsi ckt.fst $(CONTRIB)/CoreCrypto/fst/CoreCrypto.fst ../crypto/sha1.fst crypto.fst interpreter.fst

OUTPUT_DIR=./ocaml-output

CONTRIB=$(FSTAR_HOME)/contrib

CODEGEN_FLAGS=--admit_fsi FStar.OrdSet  --admit_fsi FStar.String --admit_fsi Ffibridge --admit_fsi Runtime --admit_fsi Prog --admit_fsi FStar.IO\
              --admit_fsi FStar.Squash --admit_fsi Smciface --admit_fsi Hashtable --codegen-lib Platform --codegen-lib CoreCrypto --codegen OCaml --odir $(OUTPUT_DIR)\
              --use_native_int --__temp_no_proj PSemantics --__temp_no_proj SecServer

FSTAR_LIB_FILES=FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Seq.fst FStar.SeqProperties.fst FStar.Ghost.fst FStar.Squash.fsti\
                FStar.List.Tot.fst FStar.List.fst FStar.ListProperties.fst ordset.fsi  ordmap.fsi FStar.OrdMap.fst FStar.IO.fsti string.fsi hashtable.fsi\

# removed sha1, CoreCrypto, crypto, and sec_server
INTERPRETER_FILES=prins.fst $(CONTRIB)/Platform/fst/Platform.Bytes.fst ast.fst ffibridge.fsi sem.fst psem.fst rtheory.fst \
                  runtime.fsi print.fst ckt.fst\
                  interpreter.fst examples/ffi.fst prog.fsi
# INTERPRETER_FILES=prins.fst $(CONTRIB)/Platform/fst/Platform.Bytes.fst ast.fst ffibridge.fsi sem.fst psem.fst rtheory.fst \
#                   runtime.fsi print.fst ckt.fst $(CONTRIB)/CoreCrypto/fst/CoreCrypto.fst ../crypto/sha1.fst crypto.fst\
#                   interpreter.fst sec_server.fst examples/ffi.fst prog.fsi

#SMCIF and SMCMain are set from command line invocation of make
codegen:
	cp $(SMCIF) smciface.fsi
	cp $(SMCMAIN) smc_main.fst
	$(FSTAR) --explicit_deps $(CODEGEN_FLAGS) $(EXTERNAL_FLAGS) $(FSTAR_LIB_FILES) $(INTERPRETER_FILES) smciface.fsi smc_main.fst

# codegen:
# 	$(FSTAR)  --admit_fsi FStar.String --admit_fsi Ffibridge --admit_fsi Runtime --admit_fsi Prog --admit_fsi FStar.IO --admit_fsi FStar.Squash\
#                  --codegen-lib Platform --codegen-lib CoreCrypto --codegen OCaml --odir $(OUTPUT_DIR) --use_native_int --__temp_no_proj PSemantics --__temp_no_proj SecServer\
#                  FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Seq.fst FStar.SeqProperties.fst FStar.Ghost.fst FStar.Squash.fsti\
#                  FStar.List.Tot.fst FStar.List.fst FStar.ListProperties.fst ordset.fsi FStar.OrdSet.fst ordmap.fsi FStar.OrdMap.fst FStar.IO.fsti string.fsi\
#                  prins.fst ast.fst ffibridge.fsi sem.fst psem.fst rtheory.fst $(CONTRIB)/Platform/fst/Platform.Bytes.fst runtime.fsi print.fst ckt.fst $(CONTRIB)/CoreCrypto/fst/CoreCrypto.fst ../crypto/sha1.fst crypto.fst interpreter.fst sec_server.fst examples/ffi.fst prog.fsi main.fst 

a.out:
	make -C $(OUTPUT_DIR) a.out

clean:
	make -C $(OUTPUT_DIR) clean

distclean:
	rm -f smciface.fsi smc_main.fst
	make -C $(OUTPUT_DIR) distclean
