LATEX = latexmk -pdf -latexoption='-interaction=nonstopmode' -latexoption='-file-line-error'

ROOT = Info_3_Skript_SS2026

EXTRACT = source .venv/bin/activate; python3 extract_range_by_datenote.py $(ROOT).pdf
EXPORTFILES =  2026-04-21.pdf
TARGET = $(HOME)/git/proglang.github.io/src/teaching/26ss/ti/script/

.PHONY: all

all: 
	$(LATEX) $(ROOT).tex

clean:
	latexmk -C

$(ROOT).pdf: $(ROOT).tex 1-Vorspann_Sprachen.tex 2-Regulaere_Sprachen_und_endliche_Automaten.tex

2026-04-21.pdf: $(ROOT).pdf
	$(EXTRACT) 2026-04-21.pdf --begin 21.04.26 --end 22.04.26
2026-04-22.pdf: $(ROOT).pdf
	$(EXTRACT) 2026-04-22.pdf --begin 22.04.26 --end 28.04.26

export: 2026-04-21.pdf 2026-04-22.pdf
	cp $? $(TARGET)

