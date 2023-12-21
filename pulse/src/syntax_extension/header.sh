#!/bin/bash

header=`cat header.txt`

for file in `find ./ -iname "*.fst"`
do
  echo "adding header to $file"
  sed -i -e "1i $header" $file
done
