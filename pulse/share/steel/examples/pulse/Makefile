STEEL_SHARE = ../../
# ^ This must point to /steel/share. But we cannot rely on going via
# the root (../../../..) since the OPAM package will detach the share
# directory from the rest of the repo.

INCLUDE_DIRS=bug-reports lib dice/common dice/dpe dice/engine dice/l0 parallel .
CACHE_DIR=.cache
SRC_DIRS=$(addprefix $(STEEL_SHARE)/examples/pulse/, $(INCLUDE_DIRS))
FSTAR_FILES=$(wildcard $(addsuffix /*.fst, $(SRC_DIRS))) $(wildcard $(addsuffix /*.fsti, $(SRC_DIRS)))

all: verify

extract:
#	$(FSTAR) --odir _output --codegen OCaml CustomSyntax.fst --extract CustomSyntax
	$(FSTAR) --odir _output --codegen OCaml ExtractionTest.fst --extract ExtractionTest
	
extract_c:
	$(FSTAR) --codegen krml Demo.MultiplyByRepeatedAddition.fst --extract '* -Pulse.Lib.Core'
	$(FSTAR_HOME)/../karamel/krml -bundle Demo.MultiplyByRepeatedAddition=* -skip-compilation _output/out.krml

include Makefile.pulse.common
