#! /bin/bash

commit=$(git log --pretty=format:'%h' -n 1)
cp -f README.md README.md.backup
sed -i "s/???/$commit/g" README.md
tar -czvf steelcore-icfp2020-supplementary-material.tar.gz MST.fst NMST.fst Steel.*.fst Steel.*.fsti MParIndex.fst README.md
cp -f README.md.backup README.md
