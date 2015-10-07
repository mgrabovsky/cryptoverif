default: help

help:
	@echo 'Available targets:'
	@echo '* cryptoverif (default)'
	@echo '* clean'

cryptoverif: src/*.ml
	./build

clean:
	-$(RM) cryptoverif src/*.{cmi,cmx,o} src/{,o}parser.ml{,i} src/{,o}lexer.ml
	-$(RM) tests/*

.PHONY: clean help

