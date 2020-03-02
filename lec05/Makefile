all:
	ocamlbuild -use-ocamlfind -package qcheck ce.byte

build_ce:
	ocamlbuild -use-ocamlfind -package qcheck ce.byte

hashtable:
	ocamlbuild -use-ocamlfind -package qcheck,qcstm,ppx_deriving.show hashtable.native

queue:
	ocamlbuild -use-ocamlfind -package qcheck,qcstm,ppx_deriving.show queuetest.native
	
clean:
	ocamlbuild -clean
