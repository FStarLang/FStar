#!/usr/bin/env bash
set -e
set -x

# chdir to the current directory
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"

if  [[ -z "$PULSE_HOME" ]] ; then
    # assume share/pulse/examples/dice/common/hacl-rust
    PULSE_HOME=$(realpath $(pwd)/../../)
fi

# regenerate EverCrypt*.h
./gen-evercrypt-h.sh

# generate EverCrypt*.rs and L0Core.rs
DPE_OUTPUT_DIR=$PULSE_HOME/pulse2rust/dpe/src/generated
bindgen -o $DPE_OUTPUT_DIR/evercrypt_gen.rs --allowlist-file '.*EverCrypt.*' _output/bindings.h --dynamic-loading "evercrypt" --dynamic-link-require-all -- -I _output -I .
bindgen -o $DPE_OUTPUT_DIR/l0core_gen.rs --allowlist-file '.*L0Core.*' _output/bindings.h --dynamic-loading "l0" --dynamic-link-require-all -- -I _output -I .
