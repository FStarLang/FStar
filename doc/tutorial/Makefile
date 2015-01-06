
# This uses Madoko (https://madoko.codeplex.com/)

tutorial.html: tutorial.mdk fstar.json code/solutions/*.fst
	madoko -v tutorial.mdk

tutorial.pdf: tutorial.mdk fstar.json code/solutions/*.fst
	madoko -v --pdf tutorial.mdk

clean:
	rm -f *~ css.sty madoko.css madoko.sty tutorial-math-dvi.aux tutorial-math-dvi.dim tutorial-math-dvi.dvi tutorial-math-dvi.final.tex tutorial-math-dvi.log tutorial-math-dvi.out tutorial-math-dvi.upa tutorial-math-pdf.final.tex tutorial.dimx tutorial.html tutorial.aux tutorial.log tutorial.out tutorial.pdf tutorial.tex tutorial.upa tutorial.upb tutorial-bib.aux tutorial-bib.bbl tutorial-bib.blg
	rm -dfr math
