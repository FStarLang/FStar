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

assume val p : slprop
assume val q : slprop
assume val r : slprop

assume val f () : stt_atomic unit emp_inames (p ** q) (fun _ -> p ** r)


atomic
fn g (i:iname)
  requires inv i p ** q ** later_credit 1
  ensures  r ** inv i p
  opens [i]
{
  with_invariants i {
    later_elim _;
    f ();
    later_intro p;
  }
}


#push-options "--fuel 0"
(* Does it work without fuel? Requires the iname_list coercion
to normalize away. *)

atomic
fn g2 (i:iname)
  requires inv i p ** q ** later_credit 1
  ensures  r ** inv i p
  opens [i]
{
  with_invariants i {
    later_elim _;
    f ();
    later_intro p;
  }
}

#pop-options

assume val f_ghost () : stt_ghost unit emp_inames (p ** q) (fun _ -> p ** r)


ghost
fn g_ghost (i:iname)
  requires (inv i p ** q ** later_credit 1)
  ensures (r ** inv i p)
  opens [i]
{
  with_invariants i {
    later_elim _;
    f_ghost ();
    later_intro p;
  }
}


let test (i:iname) = assert (
  add_inv emp_inames i
  ==
  join_inames (add_inv emp_inames i) emp_inames
)

assume
val atomic_write_int (r : ref int) (v : int) :
  stt_atomic unit emp_inames (exists* v0. pts_to r v0) (fun _ -> pts_to r v)


atomic
fn test_atomic (r : ref int)
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
  requires emp
  ensures emp
{
  let r = alloc #int 0;
  let i = new_invariant (exists* v. pts_to r v);
  with_invariants i
    returns _:unit
    ensures later (exists* v. pts_to r v)
    opens [i] {
      later_elim_timeless _;
      atomic_write_int r 1;
      later_intro (exists* v. pts_to r v);
  };
  drop_ (inv i _)
}


// Fails as the with_invariants block is not atomic/ghost
[@@expect_failure]

fn test3 ()
  requires emp
  ensures emp
{
  let r = alloc #int 0;
  let i = new_invariant (exists* v. pts_to r v);
  with_invariants i
    returns _:unit
    ensures later (exists* v. pts_to r v) {
      later_elim_storable _;
      r := 1;
      later_intro (exists* v. pts_to r v);
  };
  drop_ (inv i _)
}


//
// Ghost code overclaiming
//

 ghost
 fn t00 () (i:iname)
   requires (inv i emp)
   ensures (inv i emp)
   opens [i]
 {
  ()
 }



atomic
fn t0 () (i:iname)
  requires inv i emp
  ensures inv i emp
  opens [i]
{
  with_invariants i {
    ()
  }
}



assume val i : iname
assume val i2 : iname


ghost
fn basic_ghost ()
  requires emp
  ensures emp
{
  (); ()
}


(* Using invariants while claiming not to. *)
[@@expect_failure]

atomic
fn t1 ()
  requires inv i emp
  ensures inv i emp
  opens []
{
  with_invariants i {
    ()
  }
}


(* Overclaiming, OK *)

atomic
fn t3 ()
  requires inv i emp
  ensures inv i emp
  opens [i; i2]
{
  with_invariants i {
    ()
  }
}


(* Works, no need to declare opens as its an effectful fn *)

fn t2 ()
  requires emp
  returns _:int
  ensures emp
{
  let j = new_invariant emp;
  with_invariants j 
    returns _:unit
    ensures later emp {
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
  requires folded_inv i ** later_credit 1
  ensures folded_inv i ** q
  opens [i]
{
  unfold folded_inv i;
  with_invariants i
    returns _:unit
    ensures later p ** q {
    later_elim _;
    if b {
      p_to_q ();
      later_intro p;
    } else {
      ghost_p_to_q ();
      later_intro p;
    }
  };
  fold folded_inv i
}



ghost
fn test_returns1 (i:iname)
  requires folded_inv i ** later_credit 1
  ensures folded_inv i ** q
  opens [i]
{
  unfold folded_inv i;
  with_invariants i
    returns _:unit
    ensures later p ** q {
    later_elim _;
    ghost_p_to_q ();
    later_intro p;
  };
  fold folded_inv i
}


(* Testing that the with_invariants checker respects
_unfold. *)

[@@pulse_unfold]
let pp = p


ghost
fn test_returns2 (i:iname)
  requires folded_inv i ** later_credit 1
  ensures folded_inv i ** q
  opens [i]
{
  unfold folded_inv i;
  with_invariants i
    returns _:unit
    ensures later pp ** q {
    later_elim _;
    ghost_p_to_q ();
    later_intro pp;
  };
  fold folded_inv i
}

