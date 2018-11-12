#!/usr/bin/env bash

EXTENSIONS="*.fst *.fsti *.fs *.fsi"
add_copyright() {
    echo "Adding copyright to $1"
    cat copyright.txt > tmp
    cat $1 >> tmp
    mv tmp $1
}

for ext in $EXTENSIONS; do
    for file in `find .. -name "$ext" | xargs grep -L Copyright`; do
        add_copyright $file
    done
done
