FSTAR_FILES = $(wildcard *.fst)

all: verify-all

include ../Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

EXTRACT = RBTreeIntrinsic

OCAML_DEFAULT_FLAGS += -I $(OUTPUT_DIRECTORY) -w -31

$(OUTPUT_DIRECTORY)/test.exe: $(OUTPUT_DIRECTORY)/$(EXTRACT).ml | $(OUTPUT_DIRECTORY)
	@echo 'let _ = test()' >> $^
	$(OCAMLC) -o $(OUTPUT_DIRECTORY)/test.exe $^

test: $(OUTPUT_DIRECTORY)/test.exe
	$(OUTPUT_DIRECTORY)/test.exe

clean:
	rm -rf $(OUTPUT_DIRECTORY) $(CACHE_DIR) .depend

.PHONY: depend verify-all test clean
