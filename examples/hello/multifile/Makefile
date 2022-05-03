.PHONY: all clean

FSTAR_HOME?=../../..
ROOTS=$(wildcard *.fst) #scan these files for dependences
OUTPUT_DIR=output
MAIN=Main.fst #this is the main entry point file of your project
EXECUTABLE=$(subst .fst,.exe, $(MAIN))
INCLUDE_PATHS=

ifeq ($(OS),Windows_NT)
  FSTAR_EXE := $(shell cygpath -m $(FSTAR_HOME)/bin/fstar.exe)
else
  FSTAR_EXE := $(FSTAR_HOME)/bin/fstar.exe
endif

#cache_dir: where to find checked files
#odir: where to put all output artifacts
#include: where to find source and checked files
#already_cached: fstarlib is already built

FSTAR=$(FSTAR_EXE) \
	--cache_dir $(OUTPUT_DIR) \
	--odir $(OUTPUT_DIR) \
	$(addprefix --include , $(INCLUDE_PATHS) $(OUTPUT_DIR)) \
	--already_cached 'Prims FStar'

all: $(EXECUTABLE)

# generate a dependency graph
.depend: $(wildcard *.fst *.fsti)
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar' > .depend

# this defines the $(ALL_ML_FILES) variable and dependences to produce them
include .depend

# call the makefile in output after extracting all ml files
$(OUTPUT_DIR)/$(EXECUTABLE): $(ALL_ML_FILES)
	$(MAKE) -C output $(EXECUTABLE)

# recipe to verify a file and produce its .checked file
$(OUTPUT_DIR)/%.checked:
	$(FSTAR) $< --cache_checked_modules

# recipe to extract a .ml from a .checked file
$(OUTPUT_DIR)/%.ml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml --extract_module $(basename $(notdir $(subst .checked,,$<)))

clean:
	rm $(OUTPUT_DIR)/*.checked $(OUTPUT_DIR)/*.ml .depend
	$(MAKE) -C $(OUTPUT_DIR) clean
