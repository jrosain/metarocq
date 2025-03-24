all: theory plugin

_PluginProject: _PluginProject.in metarocq-config
	cat metarocq-config > _PluginProject
	cat _PluginProject.in >> _PluginProject

_RocqProject: _RocqProject.in metarocq-config
	cat metarocq-config > _RocqProject
	cat _RocqProject.in >> _RocqProject

Makefile.plugin: _PluginProject
	rocq makefile -f _PluginProject -o Makefile.plugin $(DEPS)
# Avoid conflicting dependency file creation for the template plugin
	sed -e s/coqdeps/coqdeps.plugin/g Makefile.plugin > Makefile.plugin.tmp && mv -f Makefile.plugin.tmp Makefile.plugin

Makefile.erasureplugin: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.erasureplugin $(DEPS)

theory: Makefile.erasureplugin
	$(MAKE) -f Makefile.erasureplugin
	./clean_extraction.sh

plugin: theory Makefile.plugin
# Force building the ML code before the .v's requiring them.
	$(MAKE) -f Makefile.plugin

install: theory plugin
	$(MAKE) -f Makefile.erasureplugin install
	$(MAKE) -f Makefile.plugin install

uninstall: Makefile.erasureplugin Makefile.plugin
	$(MAKE) -f Makefile.erasureplugin uninstall
	$(MAKE) -f Makefile.plugin uninstall

clean: Makefile.erasureplugin Makefile.plugin
	make -f Makefile.erasureplugin clean
	make -f Makefile.plugin clean

mrproper:
	rm -f metarocq-config
	rm -f Makefile.plugin _PluginProject
	rm -f Makefile.erasureplugin _RocqProject

.merlin: Makefile.plugin
	make -f $< $@

cleanplugin: Makefile.plugin
	make -f Makefile.plugin clean

vos: Makefile.erasureplugin
	$(MAKE) -f Makefile.erasureplugin vos

quick: Makefile.erasureplugin
	$(MAKE) -f Makefile.erasureplugin COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
