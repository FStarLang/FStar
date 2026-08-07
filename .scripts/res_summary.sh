#!/bin/bash
#
# Very basic script to collect all .ramon files and print the files
# that consumed the most memory and CPU time. You should run the
# makefile with RESOURCEMONITOR=1 to generate the .ramon files (and
# have ramon installed).

declare -A cpu
declare -A mem

printAll=false

memory_bytes() {
	local amount=${1%%[A-Za-z]*}
	local unit=${1#"$amount"}

	case "$unit" in
		B)   echo "$amount" ;;
		KiB) echo $((amount * 1024)) ;;
		MiB) echo $((amount * 1024 * 1024)) ;;
		GiB) echo $((amount * 1024 * 1024 * 1024)) ;;
		*)   echo 0 ;;
	esac
}

memory_mib() {
	awk -v bytes="$1" 'BEGIN { printf "%.1f", bytes / 1024 / 1024 }'
}

if [ $# -gt 0 ] && ( [ $1 == "--all" ] || [ $1 == "-a" ] ); then
	printAll=true
	shift
fi

# Traverse all .ramon files and store the relevant information in the
# associative arrays above.
while IFS= read -r -d '' f; do
	fp=${f/.ramon/}

	s=$(grep 'group.mempeak' "$f" | grep -Eo '[0-9]+(KiB|MiB|GiB|B)' | head -1)
	mem[$fp]=$(memory_bytes "$s")

	t=$(grep 'group.total' "$f" | grep -Eo '[0-9.]+s' | head -1)
	t=${t/s/}
	cpu[$fp]=$t
done < <(find . -name '*.ramon' -print0)

# If -a/--all was given, print a line for each file.
if $printAll; then
	echo "All space and time:"
	for fp in "${!mem[@]}"; do
		printf "RAMON: %-80s %12s %12s\n" "$fp" "${cpu[$fp]}s" "$(memory_mib "${mem[$fp]}")MiB"
	done
fi

echo

# Print the top 20 in memory and CPU time.
echo "Top 20 memory:"
for fp in "${!mem[@]}"; do
	printf "%s\t%s\n" "${mem[$fp]}" "$fp"
done | sort -k1 -n -r | head -n 20 |
	while IFS=$'\t' read -r bytes fp; do
		printf " %-80s %12s\n" "$fp" "$(memory_mib "$bytes") MiB"
	done
echo

echo "Top 20 CPU time:"
for fp in "${!cpu[@]}"; do
	printf " %-80s %12s\n" "$fp" "${cpu[$fp]} s"
done | sort -k2 -n -r  | head -n 20
echo

TOTMEM=0
TOTCPU=0
# Trying to do this in the loops above won't work as the command runs in
# a subshell, with its own set of variables. Bash is fun :^).
for fp in "${!mem[@]}"; do
	TOTMEM=$(($TOTMEM + ${mem[$fp]:-0}))
	TOTCPU=$(echo $TOTCPU + ${cpu[$fp]:-0} | bc)
done

echo "Total CPU: $TOTCPU seconds"
echo "Total memory: $(memory_mib "$TOTMEM") MiB"
