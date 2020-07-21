ALL_FSTs := $(wildcard tests/*.fst)
ALL_FSTIs := $(wildcard tests/*.fsti)
ALL_EXPECT := $(patsubst %,%.expect.md,$(ALL_FSTs) $(ALL_FSTIs))
ALL_GEN := $(patsubst %,%.gen.md,$(ALL_FSTs) $(ALL_FSTIs))
ALL_DIFF := $(patsubst %,%-diff,$(ALL_FSTs) $(ALL_FSTIs))

all: regression-tests

regression-tests: $(ALL_DIFF)

%.expect.md: %
	@touch $@

%.gen.md: % %.expect.md fstardoc.py
	@python3 fstardoc.py $< > $@

%-diff: %.expect.md %.gen.md
	@diff -u $^ && echo 'Test "$*" passed.'

update-to-latest:
	@echo "Cloning from base"
	@git clone --depth=1 https://github.com/jaybosamiya/fstardoc
	@echo "Copying over"
	@cp -r fstardoc/* .
	@echo "Cleaning up"
	@rm -rf fstardoc
	@git checkout -- README.md
	@echo "Done. Updates in this directory:"
	@git status .

.PRECIOUS: $(ALL_GEN) $(ALL_EXPECT)
