
# This uses Madoko (https://madoko.codeplex.com/)

tutorial.html: tutorial.mdk fstar.json code/exercises/*.fst code/solutions/*.fst
	madoko -v tutorial.mdk

# This target doesn't manage to add comments, for unknown reasons
tutorial-debug: tutorial.mdk fstar.json code/exercises/*.fst code/solutions/*.fst
	madoko -v tutorial.mdk --meta=.Comment:before="**&author;**:&nbsp;"

tutorial.pdf: tutorial.mdk fstar.json code/exercises/*.fst code/solutions/*.fst
	-madoko -v --pdf tutorial.mdk  # this fails but still produces tex file
	-xelatex -interaction nonstopmode tutorial
	-xelatex -interaction nonstopmode tutorial

clean:
	rm -f *~ css.sty madoko.css madoko.sty *math-dvi.tex *math-pdf.tex *math-dvi.final.tex *math-pdf.final.tex  *.aux *.dim *.dvi *.log *.out *.upa *.dimx *.html *.log *.pdf *.upa *.upb *.bbl *.blg .*~
	rm -dfr math
