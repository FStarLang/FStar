#!/bin/bash

lower () {
	echo $1 | tr 'A-Z' 'a-z'
}

ALL="Int8 Int16 Int32 Int64 UInt8 UInt16 UInt32 UInt64"

for i in $ALL; do
	for j in $ALL; do
		if [ "$i" = "$j" ]; then
			continue;
		fi
		li=$(lower $i)
		lj=$(lower $j)
		sli=$(echo "$i" | sed 's/UI/Ui/')
		slj=$(echo "$j" | sed 's/UI/Ui/')
		echo "let ${li}_to_${lj} x = FStar_$j.of_string (FStar_$i.to_string x)"

		# Alternative: using Stdint's conversion functions, but I get
		# an error since apparently it's not evident that Stdint.uint32
		# is equal to Stdint.Uint32.t and etc?
		# echo "let ${li}_to_${lj} = Stdint.${slj}.of_${li}"
	done
done
