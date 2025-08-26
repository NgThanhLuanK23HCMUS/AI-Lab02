report:
	xelatex main.tex
	bibtex main
	xelatex main.tex
<<<<<<< HEAD
	xelatex main.tex
clean:
	rm main.pdf main.aux main. bbl, main.blg main.fls main.log main.out main.toc main.xdv 
=======
clean:
	rm main.pdf main.aux main.bbl main.fls main.toc main.blg main.log main.out main.xdv 
>>>>>>> 466b07c (workable)
 
