ALL_FILES=prims.fs st.fs all.fs ../../basic/util.fsi ../../basic/util.fs

all: $(ALL_FILES)
	 	fsc --mlcompatibility -r ../../../bin/FSharp.PowerPack.dll  -r ../../../bin/FSharp.PowerPack.Compatibility.dll  -a $^

clean:
		rm -f *dll *exe
