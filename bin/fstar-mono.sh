#!/bin/bash

BASEDIR=$(dirname $0)

mono $FSTAR_MONO_ARGS $BASEDIR/fstar-mono.exe "$@"
