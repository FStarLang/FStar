#!/bin/bash
#
# Very basic script to collect all .ramon files and print the files
# that consumed the most memory and CPU time. You should run the
# makefile with RESOURCEMONITOR=1 to generate the .ramon files (and
# have ramon installed).

declare -A cpu
declare -A mem

printAll=false

if [ $# -gt 0 ] && ( [ $1 == "--all" ] || [ $1 == "-a" ] ); then
	printAll=true
	shift
fi

# Traverse all .ramon files and store the relevant information in the
# associative arrays above.
for f in $(find . -name '*.ramon'); do
	fp=${f/.ramon/}

	s=$(grep group.mempeak $f | grep -Eo '[0-9.KMGiB]*$')
	mem[$fp]=$s

	t=$(grep group.total $f | grep -Eo '[0-9.]*s$')
	t=${t/ seconds/}
	cpu[$fp]=$t
done

# If -a/--all was given, print a line for each file.
if $printAll; then
	echo "All space and time:"
	for fp in "${!mem[@]}"; do
		printf "RUNLIM: %-80s %12s %12s\n" "$fp" "${cpu[$fp]}s" "${mem[$fp]}"
	done
fi

# Print the top 20 in memory and CPU time.
echo "Top 20 memory:"
for fp in "${!mem[@]}"; do
	printf " %-80s %12s\n" "$fp" "${mem[$fp]}"
done | sort -k2 -r -h | head -n 20
echo

echo "Top 20 CPU time:"
for fp in "${!cpu[@]}"; do
	printf " %-80s %12s\n" "$fp" "${cpu[$fp]}s"
done | sort -k2 -n -r | head -n 20
echo

# Adding up the humanized memories is a pain. Just use ramon to wrap the
# initial make invocation too, and that will provide clear numbers for everything,
# including CPU, memory peak, pid peak, and a measure of parallelism.

# TOTMEM=0
# TOTCPU=0
# Trying to do this in the loops above won't work as the command runs in
# a subshell, with its own set of variables. Bash is fun :^).
# for fp in "${!mem[@]}"; do
#         TOTMEM=$(($TOTMEM + ${mem[$fp]}))
#         TOTCPU=$(echo $TOTCPU + ${cpu[$fp]} | bc)
# done

# echo "Total CPU: $TOTCPU seconds"
# echo "Total memory: $TOTMEM MB"
