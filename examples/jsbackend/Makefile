FSLIBFILES=FStar.ST.fst FStar.String.fsti js.fst list.fsi
FSLIB=$(addprefix ../../lib/, $(FSLIBFILES))
FSTAR_HOME=../..
include ../Makefile.include

TESTS=constants.js strings.js fun.js tuples.js record.js

all: clean init $(TESTS) close

init:
	echo "<!doctype html><html><body><script src=\"lib/stdlib.js\"></script>" > tests.htm

close:
	echo "</body></html>" >> tests.htm

%.js: %.fst
	$(FSTAR) --admit_fsi List $(OTHERFLAGS) --silent --codegen JavaScript $(FSLIB) $^ > $@
	echo "<script src=\"$@\"></script>" >> tests.htm

clean:
	rm -fr tests.htm *.js *~
