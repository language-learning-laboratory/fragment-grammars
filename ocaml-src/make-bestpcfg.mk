PREFIX := /opt/local
OCAMLOPT := $(PREFIX)/bin/ocamlopt
OCAMLINC := -I $(PREFIX)/lib/ocaml
EXTLIBINC := -I $(PREFIX)/lib/ocaml/site-lib/extlib

INTERFACES := -I pcfg -I fg
FLAGS := -inline 1000  -unsafe 

#for memory profiling support
#OCAMLOPT := /usr/local/bin/ocamlopt
#OCAMLINC :=/usr/local/lib/ocaml

#change this if you want to profile
#OCAMLC := ocamlcp
OCAMLC := ocamlc

globals.cmx: globals.ml
	$(OCAMLOPT) $(FLAGS) -c  $(OCAMLINC)  $(EXTLIBINC)  $(EXTLIBINC)   $(INTERFACES) globals.ml

utils.cmx: utils.ml
	$(OCAMLOPT) $(FLAGS) -c  $(OCAMLINC)  $(EXTLIBINC)  $(INTERFACES) str.cmxa \
	utils.ml

id.cmx: id.ml
	$(OCAMLOPT) $(FLAGS) -c  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES) id.ml

tree.cmx: tree.ml
	$(OCAMLOPT) $(FLAGS) -c  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES) \
	tree.ml

agenda.cmx: agenda.ml
	$(OCAMLOPT) $(FLAGS) -c  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES) \
	agenda.ml

sexp.cmx: sexp.ml tree.cmx
	$(OCAMLOPT) $(FLAGS) -c -pp camlp4oof  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES) \
	tree.cmx \
	sexp.ml

histogram.cmx: histogram.ml utils.cmx
	$(OCAMLOPT) $(FLAGS) -c  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES)  bigarray.cmxa  str.cmxa extLib.cmxa \
	utils.cmx \
	histogram.ml

cyk.cmx: cyk.ml globals.cmx utils.cmx tree.cmx agenda.cmx
	$(OCAMLOPT) $(FLAGS) -c  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES) bigarray.cmxa  str.cmxa extLib.cmxa \
	utils.cmx tree.cmx agenda.cmx \
	cyk.ml

seededCyk.cmx: seededCyk.ml globals.cmx utils.cmx tree.cmx agenda.cmx
	$(OCAMLOPT) $(FLAGS) -c  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES)   bigarray.cmxa  str.cmxa extLib.cmxa \
	utils.cmx tree.cmx agenda.cmx \
	seededCyk.ml

pcfg/pcfg.cmx: pcfg/pcfg.ml globals.cmx utils.cmx  id.cmx
	$(OCAMLOPT) $(FLAGS) -c  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES)  bigarray.cmxa  str.cmxa extLib.cmxa \
	globals.cmx utils.cmx  id.cmx \
	pcfg/pcfg.ml

fg/fragmentGrammar.cmx: fg/fragmentGrammar.ml globals.cmx utils.cmx  id.cmx
	$(OCAMLOPT) $(FLAGS) -c  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES)  bigarray.cmxa  str.cmxa extLib.cmxa \
	globals.cmx utils.cmx  id.cmx \
	fg/fragmentGrammar.ml

fg/fGStats.cmx:  fg/fGStats.ml globals.cmx utils.cmx histogram.cmx tree.cmx id.cmx sexp.cmx fg/fragmentGrammar.cmx 
	$(OCAMLOPT) $(FLAGS) -c  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES)   bigarray.cmxa  str.cmxa extLib.cmxa \
	globals.cmx utils.cmx histogram.cmx tree.cmx id.cmx fg/fragmentGrammar.cmx  \
	fg/fGStats.ml

fg/mHSampler.cmx: fg/mHSampler.ml globals.cmx utils.cmx tree.cmx id.cmx  cyk.cmx seededCyk.cmx fg/fragmentGrammar.cmx
	$(OCAMLOPT) $(FLAGS) -c  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES)   bigarray.cmxa  str.cmxa \
	globals.cmx utils.cmx  tree.cmx id.cmx fg/fragmentGrammar.cmx  cyk.cmx seededCyk.cmx \
	fg/mHSampler.ml

fg/gibbsSampler.cmx: fg/gibbsSampler.ml globals.cmx utils.cmx tree.cmx id.cmx fg/fragmentGrammar.cmx  fg/mHSampler.cmx 
	$(OCAMLOPT) $(FLAGS) -c  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES) bigarray.cmxa  str.cmxa extLib.cmxa \
	globals.cmx utils.cmx  tree.cmx id.cmx fg/fragmentGrammar.cmx fg/mHSampler.cmx  \
	fg/gibbsSampler.ml

fg/mHTableSampler.cmx: fg/mHTableSampler.ml fg/mHSampler.cmx globals.cmx utils.cmx tree.cmx id.cmx  cyk.cmx seededCyk.cmx fg/fragmentGrammar.cmx 
	$(OCAMLOPT) $(FLAGS) -c  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES)   bigarray.cmxa  str.cmxa \
	globals.cmx utils.cmx  tree.cmx id.cmx fg/fragmentGrammar.cmx  cyk.cmx seededCyk.cmx fg/mHSampler.cmx  \
	fg/mHTableSampler.ml

fg/sampler.cmx: fg/sampler.ml utils.cmx tree.cmx id.cmx fg/fragmentGrammar.cmx   fg/mHSampler.cmx fg/gibbsSampler.cmx fg/mHTableSampler.cmx
	$(OCAMLOPT) $(FLAGS) -c  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES)  bigarray.cmxa  str.cmxa \
	globals.cmx utils.cmx  tree.cmx id.cmx fg/fragmentGrammar.cmx  fg/mHSampler.cmx fg/gibbsSampler.cmx  fg/mHTableSampler.cmx \
	fg/sampler.ml

fg/fragmentGrammarIO.cmx: fg/fragmentGrammarIO.ml globals.cmx utils.cmx id.cmx fg/fragmentGrammar.cmx
	$(OCAMLOPT) $(FLAGS) -c  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES)   bigarray.cmxa  str.cmxa extLib.cmxa \
	globals.cmx utils.cmx  id.cmx fg/fragmentGrammar.cmx \
	fg/fragmentGrammarIO.ml

fg/loadCorpus.cmx:fg/loadCorpus.ml fg/fragmentGrammar.cmx sexp.cmx fg/gibbsSampler.cmx 
	$(OCAMLOPT) $(FLAGS) -c -pp camlp4oof  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES) \
	fg/fragmentGrammar.cmx sexp.cmx fg/gibbsSampler.cmx  \
	fg/loadCorpus.ml


#bestpcfg
bestpcfg: fg/bestpcfg.ml globals.cmx utils.cmx tree.cmx id.cmx sexp.cmx fg/fragmentGrammar.cmx  \
	fg/loadCorpus.cmx fg/fragmentGrammarIO.cmx histogram.cmx fg/fGStats.cmx cyk.cmx fg/mHSampler.cmx  \
	fg/sampler.cmx fg/mHTableSampler.cmx
	$(OCAMLOPT) $(FLAGS)  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES)  -pp camlp4oof bigarray.cmxa str.cmxa unix.cmxa extLib.cmxa \
	globals.cmx utils.cmx  tree.cmx id.cmx fg/fragmentGrammar.cmx sexp.cmx fg/gibbsSampler.cmx \
	fg/loadCorpus.cmx fg/fragmentGrammarIO.cmx histogram.cmx fg/fGStats.cmx cyk.cmx fg/mHSampler.cmx fg/mHTableSampler.cmx  \
	fg/sampler.cmx fg/bestpcfg.ml -o ../bin/bestpcfg

bestpcfg-clean: 
	rm -f ../bin/bestpcfg

clean: 
	rm -f *.cmo *.cmi *.o *.cmx *~ 
	rm -f pcfg/*.cmo pcfg/*.cmi pcfg/*.o pcfg/*.cmx pcfg/*~
	rm -f fg/*.cmo fg/*.cmi fg/*.o fg/*.cmx fg/*~
	rm -f ../bin/*
