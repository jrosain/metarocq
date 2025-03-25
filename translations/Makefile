all: Makefile.rocq
	$(MAKE) -f Makefile.rocq TIMED=$(TIMED)

_RocqProject: _RocqProject.in metarocq-config
	cat metarocq-config > _RocqProject
	cat _RocqProject.in >> _RocqProject

Makefile.rocq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.rocq

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq clean

mrproper:
	rm -f Makefile.rocq

force Makefile _RocqProject.in metarocq-config: ;

%: Makefile.rocq force
	+$(MAKE) -f Makefile.rocq $@

.PHONY: all clean mrproper force

vos: Makefile.rocq
	$(MAKE) -f Makefile.rocq vos

quick: Makefile.rocq
	$(MAKE) -f Makefile.rocq COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
