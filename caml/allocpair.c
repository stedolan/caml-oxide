#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>

value caml_alloc_pair(uintnat tag, value a, value b) {
  CAMLparam2(a, b);
  CAMLlocal1(r);
  r = caml_alloc(2, tag);
  Field(r, 0) = a;
  Field(r, 1) = b;
  CAMLreturn(r);
}
