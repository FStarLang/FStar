FSTAR_ROOT ?= ../..
NODEPEND=1
include $(FSTAR_ROOT)/mk/test.mk

_ != mkdir -p $(OUTPUT_DIR)
# ^ Make sure the output dir exists, since we're passing NODEPEND=1
# it will not be created for us.

$(OUTPUT_DIR)/%.fst.printed: %.fst
	$(call msg, "PPRINT", $(basename $(notdir $@)))
	$(FSTAR) --print $< > $@

$(OUTPUT_DIR)/%.fst.printedinplace: %.fst
	$(call msg, "PPRINT INPLACE", $(basename $(notdir $@)))
	# A bit of shuffling since we must pass an .fst to F*.
	cp $< $(OUTPUT_DIR)/$*.fst
	$(FSTAR) --print_in_place $(OUTPUT_DIR)/$*.fst
	mv $(OUTPUT_DIR)/$*.fst $@

# GM: Do we really want to test the --print_in_place feature for every
# base file? It seems unlikely this will ever regress. But it doesn't
# take a lot of time, so no big deal.
#
# I'm retaining it with these rules... but we be OK with removing this altogether.
all: $(patsubst %.printed.expected,$(OUTPUT_DIR)/%.printedinplace.diff,$(wildcard *.printed.expected))
%.fst.printedinplace.expected: %.fst.printed.expected
	cp $< $@
