all: examples

examples: Makefile.rocq
	$(MAKE) -f Makefile.rocq TIMED=$(TIMED)

Makefile.rocq: Makefile _RocqProject
	rocq makefile -f _RocqProject -o Makefile.rocq

_RocqProject: _RocqProject.in metarocq-config
	cat metarocq-config > _RocqProject
	cat _RocqProject.in >> _RocqProject

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq clean

mrproper:
	rm -f Makefile.rocq

vos: Makefile.rocq
	$(MAKE) -f Makefile.rocq vos

quick: Makefile.rocq
	$(MAKE) -f Makefile.rocq COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
