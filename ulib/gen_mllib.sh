#!/usr/bin/env bash

find "$@" -maxdepth 1 -name "*.ml" -print \
    | xargs -n 1 basename \
    | sed -e 's/\.ml//g' | sort | uniq
