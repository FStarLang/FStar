#!/usr/bin/env bash
set -e

# For CI, use keysize_small
sed -i.bak 's/let keysize = keysize_large/let keysize = keysize_small/' contrib/CoreCrypto/ml/Tests.ml
sed -i.bak 's/let dh_param_size = dh_param_size_large/let dh_param_size = dh_param_size_small/' contrib/CoreCrypto/ml/Tests.ml

# We leave contrib/CoreCrypto/ml/Tests.ml modified, unstaged.
# The CI teardown will forget this happened.
