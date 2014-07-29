FSLIBFILES=st.fst string.fst js.fst
FSLIB=$(addprefix ../../lib/, $(FSLIBFILES))
FSTAR=../../bin/FStar.exe --fstar_home ../../ $(OTHERFLAGS)

TESTS=constants.js fun.js record.js

all: clean init $(TESTS) close

init:
	echo "<!doctype html><html><body><script src=\"lib/stdlib.js\"></script>" > tests.htm

close:
	echo "</body></html>" >> tests.htm

%.js: %.fst
	$(FSTAR) --silent --codegen JavaScript $(FSLIB) $^ > $@
	echo "<script src=\"$@\"></script>" >> tests.htm

clean:
	rm -fr *.js *~ 
