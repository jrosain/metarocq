all: coq

_RocqProject: _RocqProject.in metarocq-config
	cat metarocq-config > _RocqProject
	cat _RocqProject.in >> _RocqProject

coq: Makefile.rocq
	$(MAKE) -f Makefile.rocq

.PHONY: install html clean mrproper all

install: Makefile.rocq
	$(MAKE) -f Makefile.rocq install

uninstall: Makefile.rocq
	$(MAKE) -f Makefile.rocq uninstall

html: all
	$(MAKE) -f Makefile.rocq html

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq clean

mrproper:
	rm -f Makefile.rocq

Makefile.rocq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.rocq

.merlin: Makefile.rocq
	$(MAKE) -f $< $@
