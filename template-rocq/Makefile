all: coq template-rocq plugin

_PluginProject: _PluginProject.in metarocq-config
	cat metarocq-config > _PluginProject
	cat _PluginProject.in >> _PluginProject

_RocqProject: _RocqProject.in metarocq-config
	cat metarocq-config > _RocqProject
	cat _RocqProject.in >> _RocqProject

_TemplateRocqProject: _TemplateRocqProject.in metarocq-config
	cat metarocq-config > _TemplateRocqProject
	cat _TemplateRocqProject.in >> _TemplateRocqProject


Makefile.rocq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.rocq

Makefile.plugin: _PluginProject
	rocq makefile -f _PluginProject -o Makefile.plugin
# Avoid conflicting dependency file creation for the template plugin
	sed -e s/coqdeps/coqdeps.plugin/g Makefile.plugin > Makefile.plugin.tmp && mv -f Makefile.plugin.tmp Makefile.plugin

Makefile.template: _TemplateRocqProject
	rocq makefile -f _TemplateRocqProject -o Makefile.template
# Avoid conflicting dependency file creation for the template plugin
	sed -e s/coqdeps/coqdeps.template/g Makefile.template > Makefile.template.tmp && mv -f Makefile.template.tmp Makefile.template

.merlin: Makefile.plugin
	[ -e "gen-src/signature.mli" ] && $(MAKE) -f $< $@

coq: Makefile.rocq
	$(MAKE) -f Makefile.rocq

# The template-rocq plugin to run template programs live in Rocq
template-rocq: coq Makefile.template
# Force building the ML code before the .v's requiring them.
	$(MAKE) -f Makefile.template optfiles
	$(MAKE) -f Makefile.template

# The extractable template plugin to run *extracted* template programs in OCaml
# The sources of the plugin are built by the coq target, which calls the
# ./update_plugin.sh after successfull extraction.

plugin: coq template-rocq Makefile.plugin
	$(MAKE) -f Makefile.plugin

.PHONY: install html clean mrproper all plugin

install: Makefile.rocq Makefile.template Makefile.plugin
	$(MAKE) -f Makefile.rocq install
	$(MAKE) -f Makefile.template install
	$(MAKE) -f Makefile.plugin install

uninstall: Makefile.rocq Makefile.template Makefile.plugin
	$(MAKE) -f Makefile.rocq uninstall
	$(MAKE) -f Makefile.template uninstall
	$(MAKE) -f Makefile.plugin uninstall

html: all
	$(MAKE) -f Makefile.rocq html

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq clean
	$(MAKE) -f Makefile.template clean
	$(MAKE) -f Makefile.plugin clean

mrproper:
	rm -f Makefile.rocq
	rm -f Makefile.plugin
	rm -f Makefile.template

cleanplugin: Makefile.plugin
	make -f Makefile.plugin clean

PLUGIN_PROJECT_BLACKLIST := \
	mCUint63 \
	#

space := $(subst ,, )

PLUGIN_PROJECT_BLACKLIST_SED:=\($(subst $(space),\|,$(PLUGIN_PROJECT_BLACKLIST))\)\.\(ml\|mli\)

.PHONY: update-_PluginProject.in
update-_PluginProject.in:
	@echo 'WARNING: This target only works correctly when gen-src has been populated from making Extraction.vo and contains no outdated .ml{,i} files'
	contents="$$(cat _PluginProject.in | grep -v '^\(# \|\)gen-src/.*\.\(mli\|ml\)$$')"; \
	line="$$(printf "%s\n" "$${contents}" | grep -n "^# Generated" | head -1 | cut -d: -f1)"; \
	{ printf "%s\n" "$${contents}" | head -n$${line}; \
	  ls -1 gen-src/*.ml gen-src/*.mli | env LC_COLLATE=C sort | sed 's,^\(gen-src/$(PLUGIN_PROJECT_BLACKLIST_SED)\)$$,# \1,g'; \
	  printf "%s\n" "$${contents}" | tail -n+$$((line+1)); \
	} > _PluginProject.in
