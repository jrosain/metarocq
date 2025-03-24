all: Makefile.coq
	$(MAKE) -f Makefile.coq TIMED=$(TIMED)

_CoqProject: _CoqProject.in metarocq-config
	cat metarocq-config > _CoqProject
	cat _CoqProject.in >> _CoqProject

Makefile.coq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

mrproper:
	rm -f Makefile.coq

force Makefile _CoqProject.in metarocq-config: ;

%: Makefile.coq force
	+$(MAKE) -f Makefile.coq $@

.PHONY: all clean mrproper force

vos: Makefile.coq
	$(MAKE) -f Makefile.coq vos

quick: Makefile.coq
	$(MAKE) -f Makefile.coq COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
