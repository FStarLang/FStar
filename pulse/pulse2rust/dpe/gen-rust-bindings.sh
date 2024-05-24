#!/usr/bin/env bash

#
# Generates rust bindings for external dependencies of DPE
# It first invokes gen-external-h.sh to create .h files for
#   the dependencies
# And then uses the Rust bindgen tool to create their rust bindings
#

set -e
set -x

# chdir to the current directory
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"

if  [[ -z "$PULSE_HOME" ]] ; then
    PULSE_HOME=$(realpath $(pwd)/../../)
fi

# regenerate EverCrypt*.h and L0Core.h
./gen-external-h.sh

# generate evercrypt_gen.rs and l0core_gen.rs
DPE_OUTPUT_DIR=$PULSE_HOME/pulse2rust/dpe/src/generated
bindgen -o $DPE_OUTPUT_DIR/evercrypt_gen.rs --allowlist-file '.*EverCrypt.*' _output/bindings.h --dynamic-loading "evercrypt" --dynamic-link-require-all -- -I _output -I .
bindgen -o $DPE_OUTPUT_DIR/l0core_gen.rs --allowlist-file '.*L0Core.*' _output/bindings.h --dynamic-loading "l0" --dynamic-link-require-all -- -I _output -I .
