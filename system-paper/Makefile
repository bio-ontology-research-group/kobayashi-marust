main.pdf: main.tex sections/*.tex generated/*.tex references.bib
	pdflatex -interaction=nonstopmode -halt-on-error main.tex && bibtex main && pdflatex -interaction=nonstopmode main.tex && pdflatex -interaction=nonstopmode main.tex
clean:
	rm -f main.aux main.bbl main.blg main.log main.out main.pdf
