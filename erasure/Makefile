all: theory

_RocqProject: _RocqProject.in metarocq-config
	cat metarocq-config > _RocqProject
	cat _RocqProject.in >> _RocqProject

Makefile.erasure: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.erasure $(DEPS)

theory: Makefile.erasure
	$(MAKE) -f Makefile.erasure

install: theory
	$(MAKE) -f Makefile.erasure install

uninstall: Makefile.erasure
	$(MAKE) -f Makefile.erasure uninstall

clean: Makefile.erasure
	make -f Makefile.erasure clean

mrproper:
	rm -f Makefile.erasure

.merlin: Makefile.erasure
	make -f $< $@

vos: Makefile.erasure
	$(MAKE) -f Makefile.erasure vos

quick: Makefile.erasure
	$(MAKE) -f Makefile.erasure COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
