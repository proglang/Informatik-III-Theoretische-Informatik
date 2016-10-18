
LATEX = latexmk -pdf -latexoption='-interaction=nonstopmode'

ROOT = Info_3_Skript_WS2016-17.tex

.PHONY: all

all: 
	$(LATEX) $(ROOT)
