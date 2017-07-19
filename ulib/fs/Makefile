ALL_FILES=prims.fs st.fs all.fs io.fs

ifeq ($(OS),Windows_NT)
FSC     = fsc --mlcompatibility --nologo $(addprefix -r , $(FS_LIBS))
else
FSC     = fsharpc --mlcompatibility --nologo $(addprefix -r , $(FS_LIBS))
endif

BIN=../../bin

FS_LIBS=

all: $(ALL_FILES)
		$(FSC) --nowarn:0086 -a $^

clean:
		rm -f *dll *exe
