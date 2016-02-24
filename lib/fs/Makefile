ALL_FILES=prims.fs st.fs all.fs io.fs

all: $(ALL_FILES)
	 	fsc --mlcompatibility -r ../../bin/FSharp.PowerPack.dll -a $^

clean:
		rm -f *dll *exe
