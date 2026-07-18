#!/usr/bin/env bash

# For every path in the command line, this will remove all lines of
# shape `module Foo = ...` where Foo is not later used in the same file.
# This is done for fst/fsti and also ML files. For the fstis, we also
# try looking at the fst (which must be next to the fsti) to see if Foo
# is used there, which can be the case due to interleaving.
#
# Note, this is a fully syntactic check and does query F* to see if some
# lemmas or typeclass instances were actually used from the module. It
# also does nothing at all with simple "open"s.
#
# Please do NOT trust this script and make sure to save your state
# before running.

set -eu

D=$(dirname $0)

# With the autoremove this would be racy if run in parallel
find "$@" -type f \( -name '*.ml' -o -name '*.fst' -o -name '*.fsti' \) -exec "$D"/remove_unused_opens.sh {} \+
