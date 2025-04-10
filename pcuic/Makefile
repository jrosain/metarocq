all: coq

_RocqProject: _RocqProject.in metarocq-config
	cat metarocq-config > _RocqProject
	cat _RocqProject.in >> _RocqProject

Makefile.rocq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.rocq

coq: Makefile.rocq
	$(MAKE) -f Makefile.rocq

.PHONY: install html clean mrproper all

install: Makefile.rocq
	$(MAKE) -f Makefile.rocq install

uninstall: Makefile.rocq
	$(MAKE) -f Makefile.rocq uninstall

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq clean

mrproper:
	rm -f Makefile.rocq

vos: Makefile.rocq
	$(MAKE) -f Makefile.rocq vos

.merlin: Makefile.rocq
	$(MAKE) -f $< $@

quick: Makefile.rocq
	$(MAKE) -f Makefile.rocq COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
