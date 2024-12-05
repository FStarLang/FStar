#!/bin/bash

set -eu

list=false
if [ $# -gt 0 ] && [ $1 == "list" ]; then
	list=true
fi

declare -A files # Store all basenames for non-hint files in repo (value = 1, this is just a set)
declare -A hints # Store a map from hint paths into basenames (turns out basename computation was a bottleneck)

trap 'RC=$?; rm -f .filelist; exit $RC' EXIT INT

# Find all (normal) files, not descending into .git, and store in
# the array. Using a pipe here would be better, but a pipe creates a
# subshell, so changes to the variables won't have any effect in the
# parent.
find . -name '.git' -prune -false -o \( -type f -name '*.hints' \) > .filelist
while read f0; do
	f="$(basename "${f0}")"
	hints[$f0]=$f
done < .filelist

find . -name '.git' -prune -false -o \( -type f -not -name '*.hints' \) -printf '%f\n' > .filelist
while read f; do
	files[$f]=1
done < .filelist

rm -f .filelist

for h0 in "${!hints[@]}"; do
	h=${hints[$h0]}
	h="${h%.hints}"
	# Given a/b/c/Foo.Bar.fst.hints, if there is no Foo.Bar.fst
	# anywhere, then delete the hint file.
	if ! [ -v "files[$h]" ]; then
		if $list; then
			echo "$h0"
		else
			echo "DELETING HINT $h0"
			rm -f "${h0}"
		fi
	fi
done
