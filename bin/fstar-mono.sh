#!/bin/bash

BASEDIR=$(dirname $0)

mono $BASEDIR/fstar-mono.exe "$@"
