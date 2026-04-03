SRC := share/examples
TAG := examples
CACHE_DIR := share/examples/_cache
OUTPUT_DIR := build/$(TAG).ml
CODEGEN := Plugin
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
FSTAR_OPTIONS += --already_cached 'Prims,FStar,FStarC'
EXTRACT += --extract '-*,+Pulse,+PulseSyntaxExtension'

include mk/boot.mk
