#![feature(nll)]
#![allow(dead_code)]
#![allow(non_upper_case_globals)]
#![allow(non_snake_case)]


use std::cell::Cell;
use std::ptr;
use std::marker;
use std::slice;
use std::str;
use std::io::{self, Write};

type Uintnat = u64;

#[allow(non_camel_case_types)]
type intnat = i64;
type RawValue = intnat;


//const Max_young_wosize : usize = 256;

const No_scan_tag: u8 = 251;
const Forward_tag: u8 = 250;
const Infix_tag: u8 = 249;
const Object_tag: u8 = 248;
const Closure_tag: u8 = 247;
const Lazy_tag: u8 = 246;
const Abstract_tag: u8 = 251;
const String_tag: u8 = 252;
const Double_tag: u8 = 253;
const Double_array_tag: u8 = 254;
const Custom_tag: u8 = 255;

fn Is_block(x: RawValue) -> bool {
  (x & 1) == 0
}

fn Hd_val(x: RawValue) -> Uintnat {
  assert!(Is_block(x));
  unsafe {
    *(x as *const Uintnat).offset(-1)
  }
}

fn Wosize_val(x: RawValue) -> Uintnat {
  Hd_val(x) >> 10
}

fn Tag_val(x: RawValue) -> u8 {
  assert!(Is_block(x));
  (Hd_val(x) & 0xff) as u8
}


#[repr(C)]
#[allow(non_camel_case_types)]
struct caml__roots_block {
  next: *mut caml__roots_block,
  ntables: intnat,
  nitems: intnat,
  tables: [*mut RawValue; 5]
}

const LOCALS_BLOCK_SIZE : usize = 8;
type LocalsBlock = [Cell<RawValue>; LOCALS_BLOCK_SIZE];

struct Gc<'gc> {
  _marker: marker::PhantomData<&'gc i32>
}

extern {
  static mut caml_local_roots: *mut caml__roots_block;

//  fn caml_alloc(wosize: Uintnat, tag: Uintnat) -> *mut RawValue;
//  fn caml_alloc_small(wosize: Uintnat, tag: Uintnat) -> *mut RawValue;
//  fn caml_initialize(field: *mut RawValue, value: RawValue) -> ();
  fn caml_alloc_cell(tag: Uintnat, a: RawValue) -> RawValue;
  fn caml_alloc_pair(tag: Uintnat, a: RawValue, b: RawValue) -> RawValue;
  fn caml_alloc_string(len: usize) -> RawValue;
  fn caml_alloc_initialized_string(len: usize, contents: *const u8) -> RawValue;
  fn caml_string_length(s : RawValue) -> usize;

  fn caml_copy_double(f: f64) -> RawValue;
  fn caml_copy_int32(f: i32) -> RawValue;
  fn caml_copy_int64(f: i64) -> RawValue;
  fn caml_copy_nativeint(f: intnat) -> RawValue;
}



unsafe fn alloc_gc_cell<'a, 'gc>(_gc : &'a Gc<'gc>) -> &'gc Cell<RawValue> {
  let block = caml_local_roots;
  if ((*block).nitems as usize) < LOCALS_BLOCK_SIZE {
    let locals : &'gc LocalsBlock = &*((*block).tables[0] as *mut LocalsBlock);
    let idx = (*block).nitems;
    (*block).nitems = idx + 1;
    &locals[idx as usize]
  } else {
    panic!("not enough locals");
  }
}

unsafe fn free_gc_cell(cell: &Cell<RawValue>) {
  let block = caml_local_roots;
  assert!((*block).tables[0].offset(((*block).nitems - 1) as isize)
          ==
          cell.as_ptr());
  (*block).nitems -= 1;
}



fn with_gc<'a, F>(body: F) -> RawValue
    where F: Fn(&mut Gc) -> RawValue {
  let mut gc = Gc {_marker: Default::default()};
  let locals : LocalsBlock = Default::default();
  unsafe {
    let mut block =
      caml__roots_block {
        next: caml_local_roots,
        ntables: 1,
        nitems: 0,
        tables: [locals[0].as_ptr(),
                 ptr::null_mut(),
                 ptr::null_mut(),
                 ptr::null_mut(),
                 ptr::null_mut()]
      };
    caml_local_roots = &mut block;
    let result = body(&mut gc);
    assert!(caml_local_roots == &mut block);
    assert!(block.nitems == 0);
    caml_local_roots = block.next;
    result
  }
}


struct Val<'a, T:'a> {
  _marker: marker::PhantomData<&'a T>,
  raw: RawValue
}


impl<'a, T> Copy for Val<'a, T> { }

impl<'a, T> Clone for Val<'a, T> {
    fn clone(&self) -> Val<'a, T> {
        Val {_marker: Default::default(), raw: self.raw}
    }
}

impl <'a, T> Val<'a, T> {
  unsafe fn new<'gc>(_gc: &'a Gc<'gc>, x: RawValue) -> Val<'a, T> {
    Val { _marker: Default::default(), raw: x }
  }

  fn eval(self) -> RawValue { self.raw }

  fn var<'g, 'gc>(self, gc: &'g Gc<'gc>) -> Var<'gc, T> {
    Var::new(gc, self)
  }

  unsafe fn field<F>(self, i : Uintnat) -> Val<'a, F> {
    assert!(Tag_val(self.raw) < No_scan_tag);
    assert!(i < Wosize_val(self.raw));
    Val { _marker: Default::default(), raw: *(self.raw as *const RawValue).offset(i as isize) }
  }

  fn is_block(self) -> bool { Is_block(self.raw) }
}

trait MLType {
  fn name() -> String;
}

impl MLType for String {
  fn name() -> String { "string".to_owned() }
}

impl MLType for intnat {
  fn name() -> String { "int".to_owned() }
}

struct AA {}
impl MLType for AA {
  fn name() -> String { "'a".to_owned() }
}

struct BB {}
impl MLType for BB {
  fn name() -> String { "'b".to_owned() }
}

struct CC {}
impl MLType for CC {
  fn name() -> String { "'c".to_owned() }
}

struct DD {}
impl MLType for DD {
  fn name() -> String { "'d".to_owned() }
}

struct EE {}
impl MLType for EE {
  fn name() -> String { "'e".to_owned() }
}

fn type_name<T: MLType>() -> String {
  T::name()
}

struct Pair<A: MLType, B: MLType> {
  _a: marker::PhantomData<A>,
  _b: marker::PhantomData<B>
}
impl <A: MLType, B:MLType> MLType for Pair<A, B> {
  fn name() -> String {
    format!("({} * {})", A::name(), B::name())
  }
}

struct List<A: MLType> {
  _a: marker::PhantomData<A>
}
impl <A: MLType> MLType for List<A> {
  fn name() -> String {
    format!("{} list", A::name())
  }
}

struct Option<A: MLType> {
  _a: marker::PhantomData<A>
}
impl <A: MLType> MLType for Option<A> {
  fn name() -> String {
    format!("{} option", A::name())
  }
}

enum CList<'a, A:'a + MLType> {
  Nil,
  Cons { x: Val<'a, A>, xs: Val<'a, List<A>> }
}
impl <'a, A: MLType> Val<'a, List<A>> {
  fn as_list(self) -> CList<'a, A> {
    if self.is_block() {
      CList::Cons { x: unsafe {self.field(0)}, xs: unsafe {self.field(1)} }
    } else {
      CList::Nil
    }
  }
}

impl <'a, A: MLType, B: MLType> Val<'a, Pair<A, B>> {
  fn fst(self) -> Val<'a, A> { unsafe { self.field(0) }}
  fn snd(self) -> Val<'a, B> { unsafe { self.field(1) }}
}

impl <'a> Val<'a, String> {
  fn as_str(self) -> &'a str {
    let s = self.raw;
    assert!(Tag_val(s) == String_tag);
    unsafe {
      let slice = slice::from_raw_parts(s as *const u8, caml_string_length(s));
      str::from_utf8(slice).unwrap()
    }
  }
}

impl <'a> Val<'a, intnat> {
  fn as_int(self) -> intnat {
    assert!(!Is_block(self.raw));
    self.raw >> 1
  }
}



fn of_int(n: i64) -> Val<'static, intnat> {
  Val { _marker: Default::default(), raw: (n << 1) | 1 }
}



/* A location registered with the GC */
struct Var<'a, T> {
  cell: &'a Cell<RawValue>,
  _marker: marker::PhantomData<Cell<T>>
}

impl <'a, T> Var<'a, T> {
  fn new<'gc, 'tmp>(gc : &'a Gc<'gc>, x : Val<'tmp, T>) -> Var<'gc, T> {
    let cell : &'gc Cell<RawValue> = unsafe { alloc_gc_cell(gc) };
    cell.set(x.eval());
    Var { _marker: Default::default(), cell: cell }
  }
  fn set<'gc, 'tmp>(&mut self, x: Val<'tmp, T>) {
    self.cell.set(x.eval());
  }
  fn get<'gc, 'tmp>(&'a self, _gc: &'tmp Gc<'gc>) -> Val<'tmp, T> {
    Val { _marker: Default::default(), raw: self.cell.get() }
  }
}

impl <'a, T> Drop for Var<'a, T> {
  fn drop(&mut self) {
    unsafe{ free_gc_cell(self.cell) }
  }
}

struct GCResult1<T> {
  raw: RawValue,
  _marker: marker::PhantomData<T>
}

struct GCResult2<T> {
  raw: RawValue,
  _marker: marker::PhantomData<T>
}

impl <T> GCResult1<T> {
  fn of(raw: RawValue) -> GCResult1<T> { GCResult1 { _marker: Default::default(), raw: raw }}
  fn mark<'gc>(self, _gc: &mut Gc<'gc>) -> GCResult2<T> {
    GCResult2 { _marker: Default::default(), raw: self.raw }
  }
}
impl <T> GCResult2<T> {
  fn eval<'a, 'gc: 'a>(self, _gc: &'a Gc<'gc>) -> Val<'a, T> {
    Val {_marker: Default::default(), raw: self.raw}
  }
}

struct GCtoken {}

fn alloc_pair<'a,A: MLType,B: MLType>(_token: GCtoken, tag: Uintnat, a: Val<'a, A>, b: Val<'a, B>) -> GCResult1<Pair<A,B>> {
  GCResult1::of(unsafe{caml_alloc_pair(tag, a.eval(), b.eval())})
}

fn alloc_some<'a,A:MLType>(_token: GCtoken, a: Val<'a,A>) -> GCResult1<Option<A>> {
  GCResult1::of(unsafe{caml_alloc_cell(0, a.eval())})
}

fn alloc_blank_string(_token: GCtoken, len: usize) -> GCResult1<String> {
  GCResult1::of(unsafe{ caml_alloc_string(len) })
}

fn alloc_string(token: GCtoken, s: &str) -> GCResult1<String> {
  let r = alloc_blank_string(token, s.len());
  unsafe { ptr::copy_nonoverlapping(s.as_ptr(), r.raw as *mut u8, s.len()); }
  r
}


macro_rules! call {
  {
  $fn:ident
  ( $gc:ident, $( $arg:expr ),* )
  } => {{
    let res = $fn( GCtoken {}, $( $arg ),* );
    res.mark($gc).eval($gc)
  }}
}

macro_rules! camlmod {
  {
    $(
      fn $name:ident( $gc:ident, $($arg:ident : $ty:ty),* ) -> $res:ty $body:block
    )*
  } => {
    $(
      #[no_mangle]
      pub extern fn $name( $($arg: RawValue), *) -> RawValue {
        with_gc(|$gc| {
          $(
            let $arg : Val<$ty> = unsafe { Val::new($gc, $arg) };
          );*
          let retval : Val<$res> = $body;
          retval.raw
        })
      }
    )*

    #[no_mangle]
    pub extern fn print_module(_unused: RawValue) -> RawValue {
      $(
        {
          let mut s = "".to_owned();
          $(
            s.push_str(&type_name::<$ty>());
            s.push_str(" -> ");
          )*
          s.push_str(&type_name::<$res>());
          print!("external {} : {} = \"{}\"\n",
                 stringify!($name),
                 s,
                 stringify!($name));
        }
      )*
      io::stdout().flush().unwrap();
      1
    }
  };
}

camlmod!{
  fn tostring(gc, p: Pair<String, intnat>) -> String {
    let pv = p.var(gc);
    let msg = format!("str: {}, int: {}",
                      p.fst().as_str(),
                      p.snd().as_int());
    let ret = call!{ alloc_string(gc, &msg) };
    
    let _msg2 = format!("str: {}", pv.get(gc).fst().as_str());
    ret
  }

  fn mkpair(gc, x: AA, y: BB) -> Pair<AA, BB> {
    let pair = call!{ alloc_pair(gc, 0, x, y)};
    pair
  }

  fn somestr(gc, x: intnat) -> Option<String> {
    let s = x.as_int().to_string();
    let cell = call!{ alloc_some(gc, call!{alloc_string(gc, &s)} ) };
    let cell2 = call!{ alloc_some(gc, call!{alloc_string(gc, &s)} ) };
    cell
  }
}
