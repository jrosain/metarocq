all: theory

_CoqProject: _CoqProject.in metarocq-config
	cat metarocq-config > _CoqProject
	cat _CoqProject.in >> _CoqProject

Makefile.quotation: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.quotation $(DEPS)

theory: Makefile.quotation
	$(MAKE) -f Makefile.quotation

install: theory
	$(MAKE) -f Makefile.quotation install

uninstall: Makefile.quotation
	$(MAKE) -f Makefile.quotation uninstall

clean: Makefile.quotation
	make -f Makefile.quotation clean

mrproper:
	rm -f metarocq-config
	rm -f Makefile.quotation _CoqProject

.merlin: Makefile.quotation
	make -f $< $@

vos: Makefile.quotation
	$(MAKE) -f Makefile.quotation vos

quick: Makefile.quotation
	$(MAKE) -f Makefile.quotation COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
