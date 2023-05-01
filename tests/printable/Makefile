# A very simple makefile to run TestPrintable.
# It is all test by 'proof' e.g., normalization
# so all you need is an all verifications complete
# message. 

FSTAR_HOME=../..

.PHONY: clean all check

clean:
	rm -f *.output *.diff

all:  TestPrintable.output TestPrintable.diff check

TestPrintable.output: 
	$(FSTAR_HOME)/bin/fstar.exe TestPrintable.fst > TestPrintable.output

TestPrintable.diff: TestPrintable.expected TestPrintable.output
	diff TestPrintable.expected TestPrintable.output > TestPrintable.diff

TEST = 	if [ -s TestPrintable.diff ]; then echo "FAILURE for TestPrintable"; else echo "SUCCESS for TestPrintable"; fi

check:
	@$(TEST)



