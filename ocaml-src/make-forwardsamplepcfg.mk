OCAMLOPT := /opt/local/bin/ocamlopt
OCAMLINC := -I /opt/local/lib/ocaml
MLGSLINC := -I /opt/local/lib/ocaml/gsl
EXTLIBINC := -I /opt/local/lib/ocaml/site-lib/extlib

CODEPREFIX ?= fg
INTERFACES := -I pcfg
FLAGS := -inline 1000  -unsafe 

#for memory profiling support
#OCAMLOPT := /usr/local/bin/ocamlopt
#OCAMLINC :=/usr/local/lib/ocaml


#change this if you want to profile
#OCAMLC := ocamlcp
OCAMLC := ocamlc

globals.cmx: globals.ml
	$(OCAMLOPT) $(FLAGS) -c  $(OCAMLINC)  $(EXTLIBINC)  $(EXTLIBINC)  $(INTERFACES) globals.ml

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

cyk.cmx: cyk.ml globals.cmx utils.cmx tree.cmx agenda.cmx
	$(OCAMLOPT) $(FLAGS) -c  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES)   bigarray.cmxa  str.cmxa extLib.cmxa \
	utils.cmx tree.cmx agenda.cmx \
	cyk.ml

pcfg/pcfg.cmx: pcfg/pcfg.ml globals.cmx utils.cmx  id.cmx
	$(OCAMLOPT) $(FLAGS) -c  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES)   bigarray.cmxa  str.cmxa extLib.cmxa \
	globals.cmx utils.cmx  id.cmx \
	pcfg/pcfg.ml


forwardsamplepcfg: pcfg/forwardsamplepcfg.ml id.cmx globals.cmx utils.cmx  pcfg/pcfg.cmx  tree.cmx \
	sexp.cmx cyk.cmx
	$(OCAMLOPT) $(FLAGS)  $(OCAMLINC)  $(EXTLIBINC) $(INTERFACES)   -pp camlp4oof \
	bigarray.cmxa  str.cmxa unix.cmxa extLib.cmxa \
	id.cmx globals.cmx utils.cmx  pcfg/pcfg.cmx tree.cmx \
	sexp.cmx cyk.cmx \
	pcfg/forwardsamplepcfg.ml -o  ../bin/forwardsamplepcfg

forwardsamplefg-clean: 
	rm -f ../bin/forwardsamplepcfg

clean: 
	rm -f *.cmo *.cmi *.o *.cmx *~ 
	rm -f pcfg/*.cmo pcfg/*.cmi pcfg/*.o pcfg/*.cmx pcfg/*~
