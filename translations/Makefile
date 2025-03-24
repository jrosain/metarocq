all: Makefile.coq
	$(MAKE) -f Makefile.coq TIMED=$(TIMED)

_RocqProject: _RocqProject.in metarocq-config
	cat metarocq-config > _RocqProject
	cat _RocqProject.in >> _RocqProject

Makefile.coq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

mrproper:
	rm -f Makefile.coq

force Makefile _RocqProject.in metarocq-config: ;

%: Makefile.coq force
	+$(MAKE) -f Makefile.coq $@

.PHONY: all clean mrproper force

vos: Makefile.coq
	$(MAKE) -f Makefile.coq vos

quick: Makefile.coq
	$(MAKE) -f Makefile.coq COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
