#!/bin/bash
#
# Very basic script to collect all .runlim files and print the files
# that consumed the most memory and CPU time. You should run the
# makefile with RESOURCEMONITOR=1 to generate the .runlim files (and
# have runlim installed).

declare -A cpu
declare -A mem

printAll=false

if [ $# -gt 0 ] && ( [ $1 == "--all" ] || [ $1 == "-a" ] ); then
	printAll=true
	shift
fi

# Traverse all .runlim files and store the relevant information in the
# associative arrays above.
for f in $(find . -name '*.runlim'); do
	fp=${f/.runlim/}

	s=$(grep space: $f | grep -Eo '[0-9.]* MB')
	s=${s/ MB/}
	mem[$fp]=$s

	t=$(grep time: $f | grep -Eo '[0-9.]* seconds')
	t=${t/ seconds/}
	cpu[$fp]=$t
done

# If -a/--all was given, print a line for each file.
if $printAll; then
	echo "All space and time:"
	for fp in "${!mem[@]}"; do
		printf "RUNLIM: %-80s %12s %12s\n" "$fp" "${cpu[$fp]}s" "${mem[$fp]}MB"
	done
fi

# Print the top 20 in memory and CPU time.
echo "Top 20 memory:"
for fp in "${!mem[@]}"; do
	printf " %-80s %12s\n" "$fp" "${mem[$fp]} MB"
done | sort -k2 -n -r  | head -n 20

echo "Top 20 CPU time:"
for fp in "${!cpu[@]}"; do
	printf " %-80s %12s\n" "$fp" "${cpu[$fp]} s"
done | sort -k2 -n -r  | head -n 20
