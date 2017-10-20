
LATEX = latexmk -pdf -latexoption='-interaction=nonstopmode' -latexoption='-file-line-error'

ROOT = Info_3_Skript_WS2017-18

.PHONY: all

all: 
	$(LATEX) $(ROOT).tex

clean:
	latexmk -C
