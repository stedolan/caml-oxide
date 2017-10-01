use std::cell::Cell;
use std::ptr;
use std::marker;

type Uintnat = u64;
type Intnat = i64;
type RawValue = Intnat;
#[allow(non_upper_case_globals)]
const Max_young_wosize : usize = 256;

#[repr(C)]
#[allow(non_camel_case_types)]
struct caml__roots_block {
  next: *mut caml__roots_block,
  ntables: Intnat,
  nitems: Intnat,
  tables: [*mut RawValue; 5]
}

const LOCALS_BLOCK_SIZE : usize = 8;
type LocalsBlock = [Cell<RawValue>; LOCALS_BLOCK_SIZE];

struct Gc<'gc> {
  _marker: marker::PhantomData<&'gc i32>
}

extern {
  static mut caml_local_roots: *mut caml__roots_block;
}


unsafe fn alloc_gc_cell<'a, 'b>(_gc : &'a Gc<'b>) -> &'b Cell<RawValue> {
  let block = caml_local_roots;
  if ((*block).nitems as usize) < LOCALS_BLOCK_SIZE {
    let locals : &'b LocalsBlock = &*((*block).tables[0] as *mut LocalsBlock);
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



/* A location registered with the GC */
struct Handle<'a> {
  cell: &'a Cell<RawValue>
}

struct Protection<'a> {
  _marker: marker::PhantomData<&'a Gc<'a>>
}

impl <'a> Protection<'a> {
  fn gc<'g>(_gc : &'a Gc<'g>) -> Protection<'a> {
    Protection { _marker: Default::default() }
  }
  fn handle<'g>(_handle: &'a Handle<'g>) -> Protection<'a> {
    Protection { _marker: Default::default() }
  }
  fn imm() -> Protection<'static> {
    Protection { _marker: Default::default() }
  }
}

enum Value<'a> {
  Handle(&'a Handle<'a>),
  Temp(&'a Gc<'a>, RawValue),
  Imm(RawValue)
}

impl <'a> Value<'a> {
  fn of_raw(gc: &'a Gc, x: RawValue) -> Value<'a> {
    Value::Temp(gc, x)
  }

  fn of_int(n: i64) -> Value<'static> {
    Value::Imm((n << 1) | 1)
  }

  unsafe fn to_raw<'l>(&'a self, _gc: &'l Gc<'a>) -> RawValue {
    match *self {
      Value::Handle(h) => h.cell.get(),
      Value::Temp(_, x) => x,
      Value::Imm(x) => x
    }
  }

/*
  /* Field is complicated.
     In multicore, should this take &mut gc? */
  fn field(self: Value<'a>, gc: &Gc, idx: i64) -> Value<'a> {
    return Value::Temp(gc, self.raw + idx) // FIXME
  }
*/
}

/*
struct Value<'a> {
  raw: i64,
  _protect: Protection<'a>
}
*/

impl <'a> Handle<'a> {
  fn new<'gc>(gc : &'a Gc<'gc>, x : Value) -> Handle<'gc> {
    unsafe {
      let cell : &'gc Cell<RawValue> = unsafe { alloc_gc_cell(gc) };
      cell.set(x.to_raw(gc));
      Handle { cell: cell }
    }
  }
  fn set<'gc>(&mut self, gc: &'a Gc<'gc>, x : Value) {
    unsafe {
      self.cell.set(x.to_raw(gc));
    }
  }
  fn get(&'a self) -> Value<'a> {
    Value::Handle(self)
  }
}

impl <'a> Drop for Handle<'a> {
  fn drop(&mut self) {
    unsafe{ free_gc_cell(self.cell) }
  }
}

extern {
  fn caml_alloc(wosize: Uintnat, tag: Uintnat) -> *mut RawValue;
  fn caml_alloc_small(wosize: Uintnat, tag: Uintnat) -> *mut RawValue;
  fn caml_initialize(field: *mut RawValue, value: RawValue) -> ();
}

struct Allocation<'expr, 'vals : 'expr> {
  tag: Uintnat,
  contents: &'expr [Value<'vals>]
}

fn alloc1<'expr, 'vals : 'expr, 'gc, 'gclock : 'vals>
  (gc: &'gclock mut Gc<'gc>,
   tag: Uintnat,
   contents: &'expr [Value<'vals>]) 
   -> Allocation<'expr, 'vals> {
  Allocation {tag: tag, contents: contents}
}

impl <'expr, 'vals : 'expr> Allocation<'expr, 'vals> {
  fn go<'a, 'gc>(self : Allocation<'expr, 'vals>, gc: &'a Gc<'gc>) -> Value<'a> {
    unsafe {
    let contents = self.contents;
    let tag = self.tag;
    let len = contents.len();
    let b =
      if 1 <= len && len <= Max_young_wosize {
        let block = caml_alloc_small(len as Uintnat, tag);
        for (i, elem) in contents.iter().enumerate() {
          *block.offset(i as isize) = elem.to_raw(gc);
        }
        block
      } else {
        let block = caml_alloc(len as Uintnat, tag);
        for (i, elem) in contents.iter().enumerate() {
          caml_initialize(block.offset(i as isize), elem.to_raw(gc));
        }
        block
      };
    Value::Temp(gc, b as RawValue)
    }
  }
}
/*
fn alloc<'a, 'gc>(gc: &'a mut Gc<'gc>, tag: Uintnat, contents: &[Value]) -> Value<'a> {
  unsafe {
    let len = contents.len();
    let b =
      if 1 <= len && len <= Max_young_wosize {
        let block = caml_alloc_small(len as Uintnat, tag);
        for (i, elem) in contents.iter().enumerate() {
          *block.offset(i as isize) = elem.to_raw(gc);
        }
        block
      } else {
        let block = caml_alloc(len as Uintnat, tag);
        for (i, elem) in contents.iter().enumerate() {
          caml_initialize(block.offset(i as isize), elem.to_raw(gc));
        }
        block
      };
    Value::Temp(gc, b as RawValue)
  }
}
*/
#[no_mangle]
pub extern fn rusty(x: RawValue, y: RawValue) -> RawValue {
  with_gc(|gc| {
    let h1 = Handle::new(gc, Value::of_raw(gc, x));
    let h2 = Handle::new(gc, Value::of_raw(gc, y));
    let v2 = h2.get();
    for _ in 1..1000 {
      //let _ = alloc1(gc, 0, &[Value::of_int(100)]).go(gc);
    }
/*    let pair = { let a = alloc1(gc, 0, &[h1.get(), v2]); a.go(gc) };
    for _ in 1..1000 {
      let _ = alloc1(gc, 0, &[Value::of_int(100)]).go(gc);
    } 
    return unsafe { pair.to_raw(gc) } */
      return 0;
  })
}

// #[no_mangle]
// pub extern fn repeat(x: RawValue, y




struct B {
  x: i32
}

fn mk(p: &mut i32) -> B {
  B { x: *p }
}

impl B {
  fn go(self, q: &i32) -> i32{
    self.x + q
  }
}

fn us() {
  let mut x = 42;
  mk(&mut x).go(&x);
}
