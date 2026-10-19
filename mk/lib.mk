# Checking a library, make sure to not use the parent lib.
FSTAR_OPTIONS += --no_default_includes
FSTAR_OPTIONS += --include $(SRC)

# Leaving this empty, F* will scan the include path for all fst/fsti
# files. This will read fstar.include and follow it too.
# ROOTS :=
# No! If we do that, we will pick up files from the current directory
# (the root of the repo) since that is implicitly included in F*'s
# search path. So instead, be explicit about scanning over all the files
# in $(SRC) (i.e. ulib). Note that there is a still a problem if there is a
# file in the cwd named like a file in ulib/, F* may prefer the former.
#
# Update: generic.mk will now complain too.
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')

include mk/generic-1.mk
