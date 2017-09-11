all: fmodulo

fmodulo: fmodulo.ml
	ocamlfind ocamlopt -pp pa_ocaml \
		-package bindlib,earley,earley.str -linkpkg -o $@ $^

test: fmodulo test.fm
	./$^

clean:
	rm -f *.cmi *.cmo *.cmx *.o

distclean: clean
	rm -f *~ fmodulo
