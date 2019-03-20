compile:
	ocamlbuild -use-ocamlfind -I src run.native

clear:
	$(RM) -r _build *.native
