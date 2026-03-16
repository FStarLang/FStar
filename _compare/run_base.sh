#!/bin/bash
set -e
BASE_FSTAR=/home/nswamy/clean/FStar-base/stage2/out/bin/fstar.exe
SRC=ulib/
CACHE_DIR=_compare/base/checked/
OUTPUT_DIR=_compare/base/ml/
CODEGEN=OCaml
TAG=base

mkdir -p $CACHE_DIR $OUTPUT_DIR

env \
  SRC=$SRC \
  FSTAR_EXE=$BASE_FSTAR \
  CACHE_DIR=$CACHE_DIR \
  OUTPUT_DIR=$OUTPUT_DIR \
  CODEGEN=$CODEGEN \
  TAG=$TAG \
  FSTAR_OPTIONS="--log_queries" \
  make -skj$(nproc) -f mk/lib.mk verify 2>&1
