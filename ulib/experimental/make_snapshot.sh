#! /bin/bash

commit=$(git log --pretty=format:'%h' -n 1)
cp -f README.md README.md.backup
sed -i "s/???/$commit/g" README.md
tar -czvf steelcore-icfp2020-supplementary-material.tar.gz *.fst *.fsti README.md
cp -f README.md.backup README.md
