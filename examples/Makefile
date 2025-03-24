all: examples

examples: Makefile.coq
	$(MAKE) -f Makefile.coq TIMED=$(TIMED)

Makefile.coq: Makefile _RocqProject
	rocq makefile -f _RocqProject -o Makefile.coq

_RocqProject: _RocqProject.in metarocq-config
	cat metarocq-config > _RocqProject
	cat _RocqProject.in >> _RocqProject

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

mrproper:
	rm -f Makefile.coq

vos: Makefile.coq
	$(MAKE) -f Makefile.coq vos

quick: Makefile.coq
	$(MAKE) -f Makefile.coq COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
