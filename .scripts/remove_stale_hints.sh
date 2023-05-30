#!/bin/bash

set -eu

declare -A files # Store all basenames in repo
declare -A hints # Store all paths of hints in repo

trap 'rm -f .filelist; exit 1' EXIT INT

# Find all (normal) files, not descending into .git, and store in
# the array. Using a pipe here would be better, but a pipe creates a
# subshell, so changes to the variables won't have any effect in the
# parent.
find . -name '.git' -prune -o \( -type f \) > .filelist
while read f0; do
	f="$(basename "${f0}")"
	files[$f]=1;
	if [[ "$f0" == *.hints ]]; then
		hints[$f0]=1
	fi
done < .filelist
rm -f .filelist

for h0 in "${!hints[@]}"; do
	h="$(basename "${h0}")"
	h="${h%.hints}"
	# Given a/b/c/Foo.Bar.fst.hints, if there is no Foo.Bar.fst
	# anywhere, then delete the hint file.
	if ! [ -v "files[$h]" ]; then
		echo "DELETING HINT $h0"
		rm -f "${h0}"
	fi
done
