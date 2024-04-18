
# This uses Madoko (https://madoko.codeplex.com/)

# CH: passing --odir=. is a bit of a hack, but our links are relative,
#     so adding an extra `out` dir as done now by default breaks our links

tutorial.html: tutorial.mdk fstar.json code/exercises/*.fst code/solutions/*.fst
	madoko -v --odir=. tutorial.mdk

# This target doesn't manage to add comments, for unknown reasons
tutorial-debug: tutorial.mdk fstar.json code/exercises/*.fst code/solutions/*.fst
	madoko -v --odir=. tutorial.mdk  --meta=.Comment:before="**&author;**:&nbsp;"

tutorial.pdf: tutorial.mdk fstar.json code/exercises/*.fst code/solutions/*.fst
	-madoko -v --odir=. --pdf tutorial.mdk  # this might fail but still produces tex file
	-xelatex -interaction nonstopmode tutorial
	-xelatex -interaction nonstopmode tutorial

clean:
	rm -f *~ css.sty madoko.css madoko.sty *math-dvi.tex *math-pdf.tex *math-dvi.final.tex *math-pdf.final.tex  *.aux *.dim *.dvi *.log *.out *.upa *.dimx *.html *.log *.pdf *.upa *.upb *.bbl *.blg .*~
	rm -f ellipse.sty longbox.sty longfbox.sty madoko2.sty options.sty tutorial-math-dvi.out.ps
	rm -dfr math

regressions: code/exercises.ver code/solutions.ver

%.ver: %
	+$(MAKE) -C $^ all
