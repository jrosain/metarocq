all: coq plugin

coq: Makefile.coq
	$(MAKE) -f Makefile.coq
	cd gen-src && ./to-lower.sh

Makefile.coq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.coq

Makefile.plugin: _PluginProject
	rocq makefile -f _PluginProject -o Makefile.plugin

_RocqProject: _RocqProject.in metarocq-config
	cat metarocq-config > _RocqProject
	cat _RocqProject.in >> _RocqProject

_PluginProject: _PluginProject.in metarocq-config
	cat metarocq-config > _PluginProject
	cat _PluginProject.in >> _PluginProject

plugin: Makefile.plugin coq
	$(MAKE) -f Makefile.plugin

.PHONY: plugin

clean: Makefile.coq Makefile.plugin
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -f Makefile.plugin clean

.merlin:
	make -f Makefile.plugin .merlin

cleanplugin: Makefile.plugin
	make -f Makefile.plugin clean
