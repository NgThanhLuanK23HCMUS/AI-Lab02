report:
	xelatex main.tex
	bibtex main
	xelatex main.tex
	xelatex main.tex
clean:
	rm main.pdf main.aux main. bbl, main.blg main.fls main.log main.out main.toc main.xdv 
 
