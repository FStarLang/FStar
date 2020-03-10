ALL_FSTs := $(wildcard tests/*.fst)
ALL_FSTIs := $(wildcard tests/*.fsti)
ALL_GEN := $(patsubst %.fst,%.md.gen,$(ALL_FSTs)) $(patsubst %.fsti,%.md.geni,$(ALL_FSTIs))
ALL_DIFF := $(patsubst %.fst,%-diff,$(ALL_FSTs)) $(patsubst %.fsti,%-diffi,$(ALL_FSTIs))

all: regression-tests

regression-tests: $(ALL_DIFF)

%.md.gen: %.fst %.md.expect fstardoc.py
	@python3 fstardoc.py $< > $@

%.md.geni: %.fsti %.md.expecti fstardoc.py
	@python3 fstardoc.py $< > $@

%-diff: %.md.expect %.md.gen
	@diff -u $^ && echo 'Test "$*.fst" passed.'

%-diffi: %.md.expecti %.md.geni
	@diff -u $^ && echo 'Test "$*.fsti" passed.'

.PRECIOUS: $(ALL_GEN)
