
# This uses Madoko (https://madoko.codeplex.com/)

tutorial.html: tutorial.mdk fstar.json code/exercises/*.fst code/solutions/*.fst
	madoko -v tutorial.mdk

# This target doesn't manage to add comments, for unknown reasons
tutorial-debug: tutorial.mdk fstar.json code/exercises/*.fst code/solutions/*.fst
	madoko -v tutorial.mdk --meta=.Comment:before="**&author;**:&nbsp;"

tutorial.pdf: tutorial.mdk fstar.json code/exercises/*.fst code/solutions/*.fst
	madoko -v --pdf tutorial.mdk

deck:
	madoko intro-tiny-fstar.mdk
	cp madoko2.css madoko.css

clean:
	rm -f *~ css.sty madoko.css madoko.sty *.aux *.dim *.dvi *.tex *.log *.out *.upa *.dimx *.html *.log *.pdf *.upa *.upb *.bbl *.blg
	rm -dfr math
