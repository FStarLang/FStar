MY_FSTAR_HOME=`cygpath "$(FSTAR_HOME)"`

all: bin/wrapper.exe test

bin/wrapper.exe:
	mkdir -p bin
	fstar --genIL --writePrims --odir bin --dotnet4 fseq.fst
	fsc -r bin/FSeq.dll --platform:x86 --target:library -o bin/Seq.dll seq.fs
	fsc -r bin/Seq.dll -r bin/FSeq.dll -o bin/wrapper.exe --platform:x86 wrapper.fs

test:
	cp $(MY_FSTAR_HOME)/bin/*.dll bin/
	(cd bin; ./wrapper.exe)

clean:
	rm -rf bin
