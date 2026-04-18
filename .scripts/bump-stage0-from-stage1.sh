#!/usr/bin/env bash
set -euxo pipefail
make -j`nproc` bump-stage0-from-stage1
git add stage0 mk/generic-0.mk
git commit -m 'exec .scripts/bump-stage0-from-stage1.sh'