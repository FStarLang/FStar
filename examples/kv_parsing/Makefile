ifndef KRML_HOME
     $(error "Please define the `KRML_HOME` variable.")
endif

OTHERFLAGS += --include $(KRML_HOME)/krmllib
OTHERFLAGS += --include $(KRML_HOME)/krmllib/obj # cache dir for krmllib
OTHERFLAGS += --include $(KRML_HOME)/krmllib/compat
OTHERFLAGS += --z3rlimit_factor 4

FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

# None of this was exercised.
#
# EXTRACT_FILES := IntegerParsing.fst \
#                  Validator.fst \
#                  ValidatedParser.fst \
#                  ValidatedAccess.fst \
#                  Serializer.fst \
#                  EnumParsing.fst \
#                  VectorParsing.fst


# # all: $(FST_FILES:.fst=.uver)

# # %.fst-in:
# #         @echo $(OTHERFLAGS)

# # extract-c: $(EXTRACT_FILES)
# #         krml -skip-compilation -warn-error +11 $(EXTRACT_FILES)

# # clean:
