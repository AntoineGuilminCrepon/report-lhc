#!/bin/sh
xelatex -shell-escape main.tex
bibtex main.aux
xelatex -shell-escape main.tex
xelatex -shell-escape main.tex
