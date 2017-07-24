verify:
	fstar.exe --use_hints *.fst

extract-c: Serializer.fst Validator.fst ValidatedParser.fst
	krml -skip-compilation -warn-error +11 Serializer.fst Validator.fst ValidatedParser.fst
