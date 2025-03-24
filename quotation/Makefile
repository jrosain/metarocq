all: theory

_RocqProject: _RocqProject.in metarocq-config
	cat metarocq-config > _RocqProject
	cat _RocqProject.in >> _RocqProject

Makefile.quotation: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.quotation $(DEPS)

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
	rm -f Makefile.quotation _RocqProject

.merlin: Makefile.quotation
	make -f $< $@

vos: Makefile.quotation
	$(MAKE) -f Makefile.quotation vos

quick: Makefile.quotation
	$(MAKE) -f Makefile.quotation COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
