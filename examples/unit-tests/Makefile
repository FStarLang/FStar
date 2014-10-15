FSTAR_HOME=../..
FSTAR=../../bin/FStar.exe --fstar_home $(FSTAR_HOME) $(OTHERFLAGS)

%.tc: %.fst
	$(FSTAR) $^

%.ver: %.fst
	$(FSTAR) --verify $^

prims: 
	$(FSTAR)  

millionaires:
	$(FSTAR) --verify $(FSTAR_HOME)/lib/st.fst $(FSTAR_HOME)/lib/partialmap.fst millionaires.fst

utils:
	$(FSTAR)  --codegen OCaml --prims prims.fst utils.fst

stdlib:
	$(FSTAR)  --codegen OCaml $(STDLIB)

#NS: Moved the specifics from here to the mitls repo. 
#This target remains here just to not suprise anyone ... we should remove it soon.

# # Change the following line to the location of the top MITLS directory "lang-sec/msrc/cvk/samples/protocols/tls"
MITLS=../../../mitls
mitls:
	make -C $(MITLS)/ML mitls

wc-mitls:
	make -C $(MITLS)/ML wc

clean:
	rm *~ 
