(* First-class closures (Pulse.Lib.Closure) under --codegen C.

   Boxes closures of several arities and effects -- total and stateful,
   capturing nothing, values, references and other closures -- calls them
   through the box, and frees them.  A combinator builds a closure internally
   from two others, which is the case explicit environment passing cannot
   express.  [main] checks its own answers. *)
module PulseClosure
#lang-pulse

open Pulse
module U32 = FStar.UInt32
module C = Pulse.Lib.Closure

let add_k (k: U32.t) (x: U32.t) : U32.t = U32.add_mod x k

let double (x: U32.t) : U32.t = U32.add_mod x x

(* A total closure capturing a value. *)
fn mk_adder (k: U32.t)
  returns c: C.closure (U32.t -> U32.t)
  ensures C.is_closure c
{
  C.alloc #(U32.t -> U32.t) (fun x -> U32.add_mod x k)
}

let owns (#a: Type0) (r: ref a) : slprop = exists* v. r |-> v

let incr_t (r: ref U32.t) = x: U32.t -> stt unit (owns r) (fun _ -> owns r)

(* A stateful closure capturing a reference and a value. *)
fn mk_incr (r: ref U32.t) (k: U32.t)
  returns c: C.closure (incr_t r)
  ensures C.is_closure c
{
  fn incr (x: U32.t)
    requires owns r
    ensures owns r
  {
    unfold owns r;
    let v = !r;
    r := U32.add_mod v (U32.add_mod x k);
    fold owns r
  };
  C.alloc #(incr_t r) incr
}

let swap_t = a: ref bool -> b: ref bool -> stt unit (owns a ** owns b) (fun _ -> owns a ** owns b)

(* Two arguments, no captures. *)
fn mk_swap ()
  returns c: C.closure swap_t
  ensures C.is_closure c
{
  fn swap (a b: ref bool)
    requires owns a ** owns b
    ensures owns a ** owns b
  {
    unfold owns a;
    unfold owns b;
    let va = !a;
    let vb = !b;
    a := vb;
    b := va;
    fold owns a;
    fold owns b
  };
  C.alloc #swap_t swap
}

let compose_t (#p #q: perm) (c1: C.closure (U32.t -> U32.t)) (c2: C.closure (U32.t -> U32.t)) =
  x: U32.t -> stt U32.t (C.is_closure c1 #p ** C.is_closure c2 #q)
                        (fun _ -> C.is_closure c1 #p ** C.is_closure c2 #q)

(* A combinator that builds a closure capturing two others. *)
fn compose (#p #q: perm) (c1 c2: C.closure (U32.t -> U32.t))
  returns c: C.closure (compose_t #p #q c1 c2)
  ensures C.is_closure c
{
  fn both (x: U32.t)
    preserves C.is_closure c1 #p ** C.is_closure c2 #q
    returns U32.t
  {
    let f = C.call c1;
    let y = f x;
    let g = C.call c2;
    g y
  };
  C.alloc #(compose_t #p #q c1 c2) both
}

let thunk_t = unit -> stt U32.t emp (fun _ -> emp)

(* A top-level function, boxed with no environment. *)
fn seven () returns r: U32.t { 7ul }

fn main ()
  returns r: U32.t
{
  let a = mk_adder 5ul;
  let f = C.call a;
  let x = f 10ul;

  let mut cell = 0ul;
  fold owns cell;
  let i = mk_incr cell 2ul;
  let g = C.call i;
  g 1ul;
  g 3ul;
  unfold owns cell;
  let y = !cell;

  let mut b1 = true;
  let mut b2 = false;
  fold owns b1;
  fold owns b2;
  let s = mk_swap ();
  let h = C.call s;
  h b1 b2;
  unfold owns b1;
  unfold owns b2;
  let v1 = !b1;
  let v2 = !b2;

  let d = C.alloc #(U32.t -> U32.t) double;
  let cd = compose #1.0R #1.0R a d;
  let k = C.call cd;
  let z = k 1ul;
  C.free cd;

  let t = C.alloc #thunk_t seven;
  let tf = C.call t;
  let w = tf ();

  C.free a;
  C.free i;
  C.free s;
  C.free d;
  C.free t;
  if (x = 15ul && y = 8ul && not v1 && v2 && z = 12ul && w = 7ul) { 0ul } else { 1ul }
}
