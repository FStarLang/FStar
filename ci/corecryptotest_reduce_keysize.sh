#!/bin/bash
set -e

# For CI, use keysize_small
pushd ucontrib/CoreCrypto/ml # SI: check that we are called from repo root?
sed -i 's/let keysize = keysize_large/let keysize = keysize_small/' Tests.ml
popd

# We leave CoreCrypto/ml/Tests.ml modified, unstaged. The CI teardown will
# forget this happened.