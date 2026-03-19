(*
   Tests for the `typedef` keyword, which defines a type alias for
   a Pulse function signature using Pulse computation type syntax.

   For example, `typedef fn ty (x:int) returns int` produces a
   let-binding equivalent to `let ty = int -> stt int emp (fun _ -> emp)`.
*)
module Example.Typedef

#lang-pulse
open Pulse
open Pulse.Lib.WithPure
module Ghost = FStar.Ghost

//
// Basic typedef: a simple pure-returning function type.
// The val ascription checks that the typedef produces
// a type matching the fn definition.
//

typedef fn simple_fn_ty (x : int) returns int

val simple_fn : simple_fn_ty
fn simple_fn (x : int) returns int
{
  (x + 1);
}

//
// Impure spec: requires and ensures with a reference.
//

typedef fn incrementer (r : ref int)
  requires pts_to r 'v
  ensures  pts_to r ('v + 1)

val incr : incrementer
fn incr (r : ref int)
  requires pts_to r 'v
  ensures  pts_to r ('v + 1)
{
  let x = !r;
  r := x + 1;
}

//
// Named return, implicit arguments, and separating conjunction.
//

typedef fn reader (r : ref int) (#p : perm) (#v : erased int)
  requires pts_to r #p v
  returns  x : int
  ensures  pts_to r #p v ** pure (x == Ghost.reveal v)

val read_ref : reader
fn read_ref (r : ref int) (#p : perm) (#v : erased int)
  requires pts_to r #p v
  returns  x : int
  ensures  pts_to r #p v ** pure (x == Ghost.reveal v)
{
  !r
}

//
// Ghost effect typedef.
//

typedef ghost fn ghost_identity_ty (x : int)
  returns y : int
  ensures pure (y == x)

val ghost_identity : ghost_identity_ty
ghost
fn ghost_identity (x : int)
  returns y : int
  ensures pure (y == x)
{
  x
}

//
// Tick-variable existentials in requires/ensures.
//

typedef fn writer (r : ref int) (v : int)
  requires pts_to r 'old
  ensures  pts_to r v

val write_ref : writer
fn write_ref (r : ref int) (v : int)
  requires pts_to r 'old
  ensures  pts_to r v
{
  r := v;
}

//
// Preserves annotation.
//

typedef fn peeker (r : ref int) (#p : perm) (#v : erased int)
  preserves pts_to r #p v
  returns x : int
  ensures pure (x == Ghost.reveal v)

val peek_ref : peeker
fn peek_ref (r : ref int) (#p : perm) (#v : erased int)
  preserves pts_to r #p v
  returns x : int
  ensures pure (x == Ghost.reveal v)
{
  !r
}

//
// Typeclass arguments.
//

class addable (a:Type) = { zero : a; add : a -> a -> a }

instance addable_int : addable int = { zero = 0; add = (fun x y -> x + y) }

typedef fn tc_fn (x : int) {| addable int |} returns y : int

val add_zero : tc_fn
fn add_zero (x : int) {| addable int |} returns y : int
{
  add x zero
}

//
// Atomic effect with invariant opening.
//

assume val myp : slprop
assume val myq : slprop
assume val myr : slprop
assume val myf (_ : unit) : stt_atomic unit emp_inames (myp ** myq) (fun _ -> myp ** myr)

typedef atomic fn atomic_inv_ty (i : iname)
  preserves inv i myp
  requires myq
  requires later_credit 1
  ensures myr
  opens [i]

val atomic_inv_fn : atomic_inv_ty
atomic
fn atomic_inv_fn (i : iname)
  preserves inv i myp
  requires myq
  requires later_credit 1
  ensures myr
  opens [i]
{
  with_invariants_a unit emp_inames i myp myq (fun _ -> myr) fn _ {
    myf ();
  }
}

//
// Impure specs: effectful reads in pre/postconditions.
//

typedef fn impure_spec_ty (r : ref int)
  preserves live r
  requires pure (!r > 10)
  ensures  pure (!r > 15)

val impure_spec_fn : impure_spec_ty
fn impure_spec_fn (r : ref int)
  preserves live r
  requires pure (!r > 10)
  ensures  pure (!r > 15)
{
  r := !r + 10;
}

typedef fn old_spec_ty (r : ref int)
  preserves live r
  ensures pure (!r > old (!r))

val old_spec_fn : old_spec_ty
fn old_spec_fn (r : ref int)
  preserves live r
  ensures pure (!r > old (!r))
{
  r := !r + 1;
}
