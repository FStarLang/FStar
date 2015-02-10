all: 
	make -C bug-reports
	make -C data_structures
	make -C algorithms OTHERFLAGS='--z3timeout 10'
	make -C crypto
	make -C security
	make -C termination
	make -C software_foundations
	make -C metatheory OTHERFLAGS='--z3timeout 10'
	make -C ../doc/tutorial/code/solutions
	make -C unit-tests
