all: theory

_RocqProject: _RocqProject.in metarocq-config
	cat metarocq-config > _RocqProject
	cat _RocqProject.in >> _RocqProject

Makefile.safechecker: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.safechecker $(DEPS)

theory: Makefile.safechecker
	$(MAKE) -f Makefile.safechecker

install: theory
	$(MAKE) -f Makefile.safechecker install

uninstall: Makefile.safechecker
	$(MAKE) -f Makefile.safechecker uninstall

clean: Makefile.safechecker
	make -f Makefile.safechecker clean

mrproper:
	rm -f metarocq-config
	rm -f Makefile.safechecker _RocqProject

.merlin: Makefile.safechecker
	make -f $< $@

vos: Makefile.safechecker
	$(MAKE) -f Makefile.safechecker vos

quick: Makefile.safechecker
	$(MAKE) -f Makefile.safechecker COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
