all: coq

_RocqProject: _RocqProject.in metarocq-config
	cat metarocq-config > _RocqProject
	cat _RocqProject.in >> _RocqProject

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

.PHONY: install html clean mrproper all

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

uninstall: Makefile.coq
	$(MAKE) -f Makefile.coq uninstall

html: all
	$(MAKE) -f Makefile.coq html

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

mrproper:
	rm -f Makefile.coq

Makefile.coq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.coq

.merlin: Makefile.coq
	$(MAKE) -f $< $@
