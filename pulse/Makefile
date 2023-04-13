all:

.PHONY: extract-ocaml
extract-ocaml: extract-tactics extract-extraction

.PHONY: extract-tactics
extract-tactics:
	+$(MAKE) -C src/ocaml -f extract-tactics.Makefile

.PHONY: extract-extraction
extract-extraction:
	+$(MAKE) -C src/extraction
