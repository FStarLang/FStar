FSTAR=fstar.exe --silent

all: mk-pldi10 mk-healthweb-azure mk-higher-order mk-fx mk-prov mk-sessions mk-jsverify mk-misc mk-sep mk-ibex mk-monadic mk-rrf mk-interop mk-tstar

mk-healthweb-azure:
	(cd healthweb-azure; make healthweb_rdcil)

mk-pldi10:
	(cd pldi10-benchmarks; ./all.sh)

mk-higher-order:
	(cd higher-order; make)

mk-fx:
	(cd fx; make)

mk-prov:
	(cd prov; make)

mk-sessions:
	(cd sessions; make)

mk-misc:
	(cd misc; make)

mk-ibex:
	(cd ibex; make)

mk-interop:
	(cd interop; make)

mk-jsverify:
	(cd jsverify; make)

mk-sep:
	(cd sep; make)

mk-rrf: 
	(cd rrf; make)

mk-monadic:
	(cd monadic; make)

mk-tstar:
	(cd ts-star/fromjs; make clean; make all)

wc: 
	find . -type f -name *.* -print | grep -v ".svn" | grep -v ".sh" | xargs cat | wc -l
