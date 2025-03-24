.PHONY: all bugd clean mrproper plugin-demo

all: bugs plugin-demo

bugs: Makefile.coq
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

plugin-demo:
	$(MAKE) -C plugin-demo

vos: Makefile.coq
	$(MAKE) -f Makefile.coq vos

quick: Makefile.coq
	$(MAKE) -f Makefile.coq COQEXTRAFLAGS="-unset \"Universe Checking\"" vos

TEST_SUITE_BLACKLIST := \
	TypeAnnotationTests.v \
	CheckerTest.v \
	ErasureTests.v \
	self_erasure.v \
	primitive.v \
	plugin-demo/.*.v \
	#

space := $(subst ,, )

TEST_SUITE_BLACKLIST_SED:=\($(subst $(space),\|,$(strip $(TEST_SUITE_BLACKLIST)))\)

.PHONY: update-_RocqProject.in
update-_RocqProject.in:
	{ printf '%s\n\n%s\n\n' '-R . MetaRocq.TestSuite' '# list obtained with `git ls-files "*.v"`'; \
	  { git ls-files "*.v" || ls -1 *.v; } | env LC_COLLATE=C sort | sed 's,^$(TEST_SUITE_BLACKLIST_SED)$$,# \1,g'; \
	} > _RocqProject.in
