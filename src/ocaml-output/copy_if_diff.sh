#!/bin/bash -x

if ! cmp -s $1 $2
then
    cp -f $1 $2
fi
