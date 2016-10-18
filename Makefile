
LATEX = latexmk -pdf -latexoption='-interaction=nonstopmode' -latexoption='-file-line-error'

ROOT = Info_3_Skript_WS2016-17

.PHONY: all

all: 
	$(LATEX) $(ROOT).tex

clean:
	latexmk -C
