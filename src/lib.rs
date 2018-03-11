#![feature(nll)]

#![allow(dead_code)]
#![allow(non_upper_case_globals)]
#![allow(non_snake_case)]


use std::cell::Cell;
use std::ptr;
use std::marker;
use std::slice;
use std::str;

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



fn with_gc<F, A>(body: F) -> A
    where F: Fn(&mut Gc) -> A {
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

#[derive(Clone, Copy)]
struct Val<'a> {
  _marker: marker::PhantomData<&'a i32>,
  raw: RawValue
}

impl <'a> Val<'a> {
  fn new<'gc>(_gc: &'a Gc<'gc>, x: RawValue) -> Val<'a> { Val { _marker: Default::default(), raw: x } }

  fn eval(self) -> RawValue { self.raw }
  fn var<'g, 'gc>(self, gc: &'g Gc<'gc>) -> Var<'gc> {
    Var::new(gc, self)
  }

  fn as_int(self) -> intnat {
    assert!(!Is_block(self.raw));
    self.raw >> 1
  }

  fn as_str(self) -> &'a str {
    let s = self.raw;
    assert!(Tag_val(s) == String_tag);
    unsafe {
      let slice = slice::from_raw_parts(s as *const u8, caml_string_length(s));
      str::from_utf8(slice).unwrap()
    }
  }

  fn field(self, i : Uintnat) -> Val<'a> {
    assert!(Tag_val(self.raw) < No_scan_tag);
    assert!(i < Wosize_val(self.raw));
    Val { _marker: Default::default(), raw: unsafe {*(self.raw as *const RawValue).offset(i as isize)} }
  }

  fn drop(self) {} 
}

fn of_int(n: i64) -> Val<'static> {
  Val { _marker: Default::default(), raw: (n << 1) | 1 }
}



/* A location registered with the GC */
struct Var<'a> {
  cell: &'a Cell<RawValue>
}

impl <'a> Var<'a> {
  fn new<'gc, 'tmp>(gc : &'a Gc<'gc>, x : Val<'tmp>) -> Var<'gc> {
    let cell : &'gc Cell<RawValue> = unsafe { alloc_gc_cell(gc) };
    cell.set(x.eval());
    Var { cell: cell }
  }
  fn set<'gc, 'tmp>(&mut self, x: Val<'tmp>) {
    self.cell.set(x.eval());
  }
  fn get<'gc, 'tmp>(&'a self, _gc: &'tmp Gc<'gc>) -> Val<'tmp> {
    Val { _marker: Default::default(), raw: self.cell.get() }
  }
}

impl <'a> Drop for Var<'a> {
  fn drop(&mut self) {
    unsafe{ free_gc_cell(self.cell) }
  }
}

struct GCResult1 {
  raw: RawValue
}

struct GCResult2 {
  raw: RawValue
}

impl GCResult1 {
  fn mark<'gc>(self, _gc: &mut Gc<'gc>) -> GCResult2 { GCResult2 { raw: self.raw } }
}
impl GCResult2 {
  fn eval<'a, 'gc: 'a>(self, _gc: &'a Gc<'gc>) -> Val<'a> {
    Val {_marker: Default::default(), raw: self.raw}
  }
}

struct GCtoken {}

fn alloc_pair<'a>(_token: GCtoken, tag: Uintnat, a: Val<'a>, b: Val<'a>) -> GCResult1 {
  GCResult1 { raw: unsafe { caml_alloc_pair(tag, a.eval(), b.eval()) } }
}

fn alloc_blank_string(_token: GCtoken, len: usize) -> GCResult1 {
  GCResult1 { raw: unsafe { caml_alloc_string(len) } }
}

fn alloc_string(token: GCtoken, s: &str) -> GCResult1 {
  let r = alloc_blank_string(token, s.len());
  unsafe { ptr::copy_nonoverlapping(s.as_ptr(), r.raw as *mut u8, s.len()); }
  r
}

/*
fn alloc_string<'a>(_token: GCtoken, s: &'a str) -> GCResult1 {
  GCResult1 { raw: unsafe { caml_alloc_initialized_string(s.len(), s.as_ptr()) } }
}
*/

/*
unsafe fn alloc<'uniq, 'a : 'uniq, 'gc>(gc: &'a mut Gc<'gc>, tag: Uintnat, contents: &[RawValue]) -> RawValue {
    let len = contents.len();
    let b =
      if 1 <= len && len <= Max_young_wosize {
        let block = caml_alloc_small(len as Uintnat, tag);
        for (i, elem) in contents.iter().enumerate() {
          *block.offset(i as isize) = elem.eval(gc);
        }
        block
      } else {
        let block = caml_alloc(len as Uintnat, tag);
        for (i, elem) in contents.iter().enumerate() {
          caml_initialize(block.offset(i as isize), elem.eval(gc));
        }
        block
      };
//    Value::Val(gc, b as RawValue)
    b
}
*/

macro_rules! call {
  {
  $fn:ident
  ( $gc:ident, $( $arg:expr ),* )
  } => {{
    let res : GCResult1 = $fn( GCtoken {}, $( $arg ),* );
    res.mark($gc).eval($gc)
  }}
}

#[no_mangle]
pub extern fn rusty(x: RawValue, y: RawValue) -> RawValue {
  with_gc(|gc| {
    let h1 = Val { _marker: Default::default(), raw: x}.var(gc);
    let h2 = Val { _marker: Default::default(), raw: y}.var(gc);
    let mut h3 = of_int(0).var(gc);
    for _ in 1..1000 {
      //let _x = Val { _gc: gc, raw: 1 };
      let _ = call!{ alloc_pair(gc, 0, of_int(100), h1.get(gc)) };
    }
    let _foo = of_int(100); //call!{ alloc_pair(gc, 0, h1.get(gc), h2.get(gc))};
    h3.set(call!{ alloc_pair(gc, 0, h1.get(gc), h2.get(gc))});

    let pair = call!{ alloc_pair(gc, 0, h1.get(gc), h2.get(gc))}.var(gc);
//    let thing = foo.eval(gc);
    { 
//      let asdf = withalloc(withgc(gc), gc); 
    }
    for _ in 1..1000 {
      let _ = call!{ alloc_pair(gc, 0, of_int(100), of_int(20)) };
    } 
    return pair.get(gc).raw;
  })
}

macro_rules! camlfn {
  (
    $name:ident( $gc:ident, $($arg:ident),* ) $body:block
  ) => {
    #[no_mangle]
    pub extern fn $name( $($arg: RawValue), *) -> RawValue {
      with_gc(|$gc| {
        $(
          let $arg = Val::new($gc, $arg);
        );*
        $body
      })
    }
  } 
}

camlfn!{tostring(gc, p) {
  let s = p.field(0);
  let n = p.field(1).as_int();
  
  let mut r: String = s.as_str().to_owned(); //s.as_str().to_owned();
  r.push_str(&n.to_string());
  
  let r = call!{ alloc_string(gc, &r) };
  r.raw
}}

