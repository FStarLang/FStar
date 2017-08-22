#!/usr/bin/env bash

FIND=$(shell which gfind > /dev/null 2>&1 && echo gfind || echo find)
SED=$(shell which gsed > /dev/null 2>&1 && echo gsed || echo sed)

$FIND "$@" -maxdepth 1 -name "*.ml" -printf '%f\n' \
   | $SED -e 's/\.ml//g' -e 's/\./_/g' -e 's/\<./\u&/g' \
   | sort \
   | uniq
