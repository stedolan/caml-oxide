OCAMLOPT = ocamlopt -thread -ccopt -pthread unix.cmxa threads.cmxa

main: target/debug/librusty.a caml/allocpair.c caml/rusty.ml caml/main.ml 
	$(OCAMLOPT) -I caml $^ -o $@

printmod: target/debug/librusty.a caml/allocpair.c caml/printmod.ml
	$(OCAMLOPT) $^ -o $@

caml/rusty.ml: printmod
	./$^ > $@

target/debug/librusty.a: src/lib.rs
	cargo build

