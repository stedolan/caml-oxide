main: target/debug/librusty.a caml/main.ml caml/allocpair.c
	ocamlopt -thread unix.cmxa threads.cmxa $^ -o $@

target/debug/librusty.a: src/lib.rs
	cargo build

