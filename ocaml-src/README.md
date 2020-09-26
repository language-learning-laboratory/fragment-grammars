# To install the relevant dependencies.
sudo port install ocaml ocaml-findlib ocaml-extlib
make -f make-bestpcfg.mk bestpcfg
make -f make-runpcfg.mk runpcfg