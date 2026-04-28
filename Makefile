LATEX = latexmk -pdf -latexoption='-interaction=nonstopmode' -latexoption='-file-line-error'

ROOT = Info_3_Skript_SS2026

EXTRACT = source .venv/bin/activate; python3 extract_range_by_datenote.py $(ROOT).pdf
EXPORTFILES =  script.pdf
HOMEPAGE = $(HOME)/git/proglang.github.io
TARGET = $(HOMEPAGE)/src/teaching/26ss/ti/script/
DATE := $(shell date '+%Y-%m-%d-%H:%M:%S')

.PHONY: all

all: 
	$(LATEX) $(ROOT).tex

clean:
	latexmk -C

$(ROOT).pdf: $(ROOT).tex 1-Vorspann_Sprachen.tex 2-Regulaere_Sprachen_und_endliche_Automaten.tex

script.pdf: $(ROOT).pdf
	$(EXTRACT) script.pdf --begin 21.04.26 --end 29.04.26

export: script.pdf
	cp $? $(TARGET)
	cd $(HOMEPAGE); ./publish "update script $(DATE)"

