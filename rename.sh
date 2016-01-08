#!/usr/bin/bash 

#a script to rename $1.fst to $2.fst globally
echo $1
echo $2
find contrib doc/tutorial/code examples lib src -type f -and -not -path '*/\.*' | grep -v "~" | xargs sed -i -b 's/\([^a-z_]\)'"$1"'\.fst/\1'"$2"'.fst/g;'
git mv lib/$1.fst lib/$2.fst



