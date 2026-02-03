(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Invariant

#lang-pulse
open Pulse
open Pulse.Lib
open Pulse.Lib.Box { box, (:=), (!) }

assume val p : slprop
assume val q : slprop
assume val r : slprop

assume val f () : stt_atomic unit emp_inames (p ** q) (fun _ -> p ** r)


atomic
fn g (i:iname)
  preserves inv i p
  requires q
  requires later_credit 1
  ensures r
  opens [i]
{
  with_invariants_a unit emp_inames i p q (fun _ -> r) fn _ {
    f ();
  }
}


atomic
fn g2 (i:iname)
  preserves inv i p
  requires q
  requires later_credit 1
  ensures r
  opens [i]
{
  with_invariants_a unit emp_inames i p q (fun _ -> r) fn _ {
    f ();
  }
}

assume val f_ghost () : stt_ghost unit emp_inames (p ** q) (fun _ -> p ** r)


ghost
fn g_ghost (i:iname)
  requires inv i p
  requires q
  requires later_credit 1
  ensures (r ** inv i p)
  opens [i]
{
  with_invariants_g unit emp_inames i p q (fun _ -> r) fn _ {
    f_ghost ();
  }
}


let test (i:iname) = assert (
  add_inv emp_inames i
  ==
  join_inames (add_inv emp_inames i) emp_inames
)

assume
val atomic_write_int (r : box int) (v : int) :
  stt_atomic unit emp_inames (exists* v0. pts_to r v0) (fun _ -> pts_to r v)


atomic
fn test_atomic (r : box int)
  requires pts_to r 'v
  ensures pts_to r 0
{
  atomic_write_int r 0;
}



fn package (r:ref int)
   requires pts_to r 123
   returns i : iname
   ensures inv i (pts_to r 123)
{
  let i = new_invariant (pts_to r 123);
  i
}



fn test2 ()
{
  let r = Box.alloc #int 0;
  let i = new_invariant (exists* v. Box.pts_to r v);
  with_invariants unit emp_inames i (exists* v. Box.pts_to r v) emp (fun _ -> emp) fn _ {
    atomic_write_int r 1;
  };
  drop_ (inv i _)
}


// Fails as the with_invariants block is not atomic/ghost

[@@expect_failure [228]]
fn test3 ()
{
  let r = Box.alloc 0;
  let i = new_invariant (exists* v. pts_to r v);
  with_invariants unit emp_inames i (exists* v. pts_to r v) emp (fun _ -> emp) fn _ {
    r := 1;
  };
  drop_ (inv i _)
}


//
// Ghost code overclaiming
//

 ghost
 fn t00 () (i:iname)
   preserves (inv i emp)
   opens [i]
 {
  ()
 }



atomic
fn t0 () (i:iname)
  preserves inv i emp
  requires later_credit 1
  opens [i]
{
  with_invariants_a unit emp_inames i emp emp (fun _ -> emp) fn _ {
    ()
  }
}



assume val i : iname
assume val i2 : iname


ghost
fn basic_ghost ()
{
  (); ()
}


(* Using invariants while claiming not to. *)
[@@expect_failure [19]]

atomic
fn t1 ()
  requires later_credit 1
  preserves inv i emp
  opens []
{
  with_invariants_a unit emp_inames i emp emp (fun _ -> emp) fn _ {
    ()
  }
}


(* Overclaiming, OK *)

atomic
fn t3 ()
  requires later_credit 1
  preserves inv i emp
  opens [i; i2]
{
  with_invariants_a unit emp_inames i emp emp (fun _ -> emp) fn _ {
    ()
  }
}


(* Works, no need to declare opens as its an effectful fn *)

fn t2 ()
  returns _:int
{
  let j = new_invariant emp;
  with_invariants unit emp_inames j emp emp (fun _ -> emp) fn _ {
    ()
  };
  drop_ (inv j _);
  123
}


assume val p_to_q : unit -> stt_atomic unit emp_inames p (fun _ -> p ** q)
assume val ghost_p_to_q : unit -> stt_ghost unit emp_inames p (fun _ -> p ** q)

let folded_inv (i:iname) = inv i p


atomic
fn test_returns0 (i:iname) (b:bool)
  preserves folded_inv i
  requires later_credit 1
  ensures q
  opens [i]
{
  unfold folded_inv i;
  with_invariants_a unit emp_inames i p emp (fun _ -> q) fn _ {
    if b {
      p_to_q ();
    } else {
      ghost_p_to_q ();
    }
  };
  fold folded_inv i
}



ghost
fn test_returns1 (i:iname)
  preserves folded_inv i
  requires later_credit 1
  ensures q
  opens [i]
{
  unfold folded_inv i;
  with_invariants_g unit emp_inames i p emp (fun _ -> q) fn _ {
    ghost_p_to_q ();
  };
  fold folded_inv i
}


(* Testing that the with_invariants checker respects
_unfold. *)

[@@pulse_unfold]
let pp = p


ghost
fn test_returns2 (i:iname)
  preserves folded_inv i
  requires later_credit 1
  ensures q
  opens [i]
{
  unfold folded_inv i;
  with_invariants_g unit emp_inames i p emp (fun _ -> q) fn _ {
    ghost_p_to_q ();
  };
  fold folded_inv i
}

