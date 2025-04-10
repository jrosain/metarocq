all: theory

_RocqProject: _RocqProject.in metarocq-config
	cat metarocq-config > _RocqProject
	cat _RocqProject.in >> _RocqProject

Makefile.templatepcuic: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.templatepcuic $(DEPS)

theory: Makefile.templatepcuic
	$(MAKE) -f Makefile.templatepcuic

install: theory
	$(MAKE) -f Makefile.templatepcuic install

uninstall: Makefile.templatepcuic
	$(MAKE) -f Makefile.templatepcuic uninstall

clean: Makefile.templatepcuic
	make -f Makefile.templatepcuic clean

mrproper:
	rm -f metarocq-config
	rm -f Makefile.templatepcuic _RocqProject

.merlin: Makefile.templatepcuic
	make -f $< $@

vos: Makefile.templatepcuic
	$(MAKE) -f Makefile.templatepcuic vos

quick: Makefile.templatepcuic
	$(MAKE) -f Makefile.templatepcuic COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
