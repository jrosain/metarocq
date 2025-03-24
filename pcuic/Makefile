all: coq

_RocqProject: _RocqProject.in metarocq-config
	cat metarocq-config > _RocqProject
	cat _RocqProject.in >> _RocqProject

Makefile.coq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

.PHONY: install html clean mrproper all

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

uninstall: Makefile.coq
	$(MAKE) -f Makefile.coq uninstall

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

mrproper:
	rm -f Makefile.coq

vos: Makefile.coq
	$(MAKE) -f Makefile.coq vos

.merlin: Makefile.coq
	$(MAKE) -f $< $@

quick: Makefile.coq
	$(MAKE) -f Makefile.coq COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
