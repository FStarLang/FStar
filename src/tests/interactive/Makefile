.PHONY: all

all:
	for a in transcript-good*; do echo "Checking $$a"; cat $$a | ../../../bin/fstar-any.sh --in test.fst | tail -n 1 | grep done-ok || exit 1; done
	for a in transcript-bad*; do echo "Checking $$a"; cat $$a | ../../../bin/fstar-any.sh --in test.fst | tail -n 1 | grep done-nok || exit 1; done
