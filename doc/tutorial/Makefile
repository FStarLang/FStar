
# This uses Madoko (https://madoko.codeplex.com/)

deck:
	madoko intro-tiny-fstar.mdk
	cp madoko2.css madoko.css

tutorial.html: tutorial.mdk fstar.json code/exercises/*.fst code/solutions/*.fst
	madoko -v tutorial.mdk

tutorial.pdf: tutorial.mdk fstar.json code/exercises/*.fst code/solutions/*.fst
	madoko -v --pdf tutorial.mdk

clean:
	rm -f *~ css.sty madoko.css madoko.sty *.aux *.dim *.dvi *.tex *.log *.out *.upa *.dimx *.html *.log *.pdf *.upa *.upb *.bbl *.blg
	rm -dfr math
