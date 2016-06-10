#!/bin/bash

BASEDIR=$(dirname $0)

mono $BASEDIR/tests-mono.exe "$@"
