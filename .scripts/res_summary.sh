#₁!/bin/bash
#
# Very basic script to collect all .runlim files and print the files
# that consumed the most memory and CPU time. You should run the
# makefile with MON=1 to generate the .runlim files (and have runlim
# installed).

echo "Top 20 memory:"
for f in $(find . -name '*.runlim'); do
	s=$(grep space: $f | grep -Eo '[0-9.]* MB')
	fp=${f/.runlim/}
	printf " %-80s %12s\n" "$fp" "$s"
done | sort -k2 -n -r  | head -n 20

echo "Top 20 time:"
for f in $(find . -name '*.runlim'); do
	s=$(grep time: $f | grep -Eo '[0-9.]* seconds')
	fp=${f/.runlim/}
	sp=${s/seconds/s}
	printf " %-80s %12s\n" "$fp" "$sp"
done | sort -k2 -n -r | head -n 20
