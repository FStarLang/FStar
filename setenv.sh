#!/bin/bash 

PWD=`pwd`
export FSTAR_HOME=`cygpath -d "$PWD"`
export PATH=`cygpath -d "$PWD/bin"`:$PATH
