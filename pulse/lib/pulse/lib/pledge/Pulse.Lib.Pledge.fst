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

module Pulse.Lib.Pledge
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module GR = Pulse.Lib.GhostReference

open FStar.Tactics.V2

let slprop_equiv_refl_eq (v1 v2 : slprop) (_ : squash (v1 == v2)) : slprop_equiv v1 v2 =
  slprop_equiv_refl v1

let __tac () : Tac unit =
  apply (`slprop_equiv_refl_eq)

let pledge is f v = inames_live is ** trade #is f (f ** v)


ghost
fn pledge_inames_live (is:inames) (f p:slprop)
  requires pledge is f p
  ensures inames_live is ** pledge is f p
{
  unfold pledge;
  dup_inames_live is;
  fold pledge;
}

ghost
fn pledge_sub_inv (is1:inames) (is2:inames { inames_subset is1 is2 })(f:slprop) (v:slprop)
  requires pledge is1 f v ** inames_live is2
  ensures pledge is2 f v
{
  unfold pledge;
  trade_sub_inv #is1 #is2 _ _;
  gather_inames_live is1 is2;
  GhostSet.lemma_equal_intro (GhostSet.union is1 is2) is2;
  rewrite (inames_live (GhostSet.union is1 is2)) as inames_live is2;
  fold pledge;
} 

ghost
fn return_pledge (f v : slprop)
  requires v
  ensures pledge emp_inames f v
{
  ghost
  fn aux ()
    requires v ** f
    ensures f ** v
  {
    ()
  };
  intro_trade #emp_inames f (f ** v) v aux;
  fold (trade #emp_inames f (f ** v));
  inames_live_empty ();
  fold pledge;
}


ghost
fn make_pledge
  (is:inames) (f v extra:slprop)
  (k:unit -> stt_ghost unit is (f ** extra) (fun _ -> f ** v))
  requires extra ** inames_live is
  ensures pledge is f v
{
  ghost
  fn aux ()
    requires extra ** f
    ensures f ** v
    opens is
  {
    k ()
  };

  intro_trade #is f (f ** v) extra aux;
  fold pledge;
}



ghost
fn redeem_pledge_aux (is:inames) (f v:slprop)
  requires f ** pledge is f v
  ensures f ** v ** inames_live is
  opens is
{
  unfold pledge;
  elim_trade #is f (f ** v);
}

ghost
fn redeem_pledge (is:inames) (f v:slprop)
  requires f ** pledge is f v
  ensures f ** v
  opens is
{
  redeem_pledge_aux is f v;
  drop_ (inames_live is)
}



ghost
fn squash_pledge (is:inames) (f:slprop) (v1:slprop)
  requires pledge is f (pledge is f v1)
  ensures pledge is f v1
{
  ghost
  fn aux ()
    requires f ** pledge is f (pledge is f v1)
    ensures f ** v1
    opens is
  {
    redeem_pledge is f (pledge is f v1);
    redeem_pledge is f v1
  };
  pledge_inames_live is f (pledge is f v1);
  make_pledge is f v1 (pledge is f (pledge is f v1)) aux
}



ghost
fn bind_pledge
  (#is:inames)
  (#f #v1 #v2 extra:slprop)
  (#is_k:inames { inames_subset is_k is })
  (k:unit -> stt_ghost unit is_k (f ** extra ** v1) (fun _ -> f ** pledge is f v2))
  requires pledge is f v1 ** extra
  ensures pledge is f v2
{
  ghost
  fn aux ()
    requires f ** (extra ** pledge is f v1)
    ensures f ** pledge is f v2
    opens is
  {
    redeem_pledge is f v1;
    k ()
  };

  pledge_inames_live is f v1;
  make_pledge is f (pledge is f v2) (extra ** pledge is f v1) aux;
  squash_pledge is f v2
}



ghost
fn bind_pledge'
  (#is:inames)
  (#f #v1 #v2 extra:slprop)
  (#is_k:inames { inames_subset is_k is })
  (k:unit -> stt_ghost unit is_k (extra ** v1) (fun _ -> pledge is f v2))
  requires pledge is f v1 ** extra
  ensures pledge is f v2
{
  ghost
  fn aux ()
    requires f ** extra ** v1
    ensures f ** pledge is f v2
    opens is
  {
    k ()
  };
  bind_pledge #is #f #v1 #v2 extra aux
}



ghost
fn rewrite_pledge_full
  (#is:inames)
  (#f v1 v2:slprop)
  (#is_k:inames { inames_subset is_k is })
  (k:unit -> stt_ghost unit is_k (f ** v1) (fun _ -> f ** v2))
  requires pledge is f v1
  ensures pledge is f v2
{
  ghost
  fn aux ()
    requires f ** pledge is f v1
    ensures f ** v2
    opens is
  {
    redeem_pledge is f v1;
    k ()
  };
  pledge_inames_live is f v1;
  make_pledge is f v2 (pledge is f v1) aux;
}



ghost
fn rewrite_pledge
  (#is:inames)
  (#f v1 v2:slprop)
  (#is_k:inames { inames_subset is_k is })
  (k:unit -> stt_ghost unit is_k v1 (fun _ -> v2))
  requires pledge is f v1
  ensures pledge is f v2
{
  ghost
  fn aux ()
    requires f ** v1
    ensures f ** v2
    opens is
  {
    k ()
  };

  rewrite_pledge_full #is #f v1 v2 aux  
}



ghost
fn join_pledge
  (#is:inames)
  (#f v1 v2:slprop)
  requires pledge is f v1 ** pledge is f v2
  ensures pledge is f (v1 ** v2)
{
  ghost
  fn aux ()
    requires f ** (pledge is f v1 ** pledge is f v2)
    ensures f ** (v1 ** v2)
    opens is
  {
    redeem_pledge is f v1;
    redeem_pledge is f v2;
  };
  pledge_inames_live is f v1;
  make_pledge is f (v1 ** v2) (pledge is f v1 ** pledge is f v2) aux;
}



ghost
fn squash_pledge'
  (is1 is2 is:inames)
  (f v1:slprop)
  requires pure (inames_subset is1 is) **
           pure (inames_subset is2 is) **
           pledge is1 f (pledge is2 f v1) **
           inames_live is
  ensures pledge is f v1
{
  ghost
  fn aux ()
    requires f ** (pledge is1 f (pledge is2 f v1))
    ensures f ** v1
    opens is
  {
    redeem_pledge is1 f (pledge is2 f v1);
    redeem_pledge is2 f v1
  };
  make_pledge is f v1 (pledge is1 f (pledge is2 f v1)) aux
}


//
// This proof below requires inv_p to be big ...
//

(* A big chunk follows for split_pledge *)

[@@no_mkeys]
let split_switch (is : inames) (b1 b2 : bool) (f v1 v2 : slprop) : slprop =
  match b1, b2 with
  | false, false -> pledge is f (v1 ** v2)
  | false, true -> v1
  | true, false -> v2
  | true, true -> emp

let inv_p' (is:inames) (f v1 v2 : slprop) (r1 r2 : GR.ref bool) (b1 b2 : bool) =
     (r1 |-> Frac 0.5R b1)
  ** (r2 |-> Frac 0.5R b2)
  ** split_switch is b1 b2 f v1 v2

let inv_p (is:inames) (f v1 v2 : slprop) (r1 r2 : GR.ref bool) : slprop =
  exists* b1 b2. inv_p' is f v1 v2 r1 r2 b1 b2

ghost
fn do_elim_body_l
  (#is:inames) (#f:slprop) (v1:slprop) (v2:slprop) (r1 r2 : GR.ref bool)
  ()
  requires inv_p is f v1 v2 r1 r2 ** f ** (r1 |-> Frac 0.5R false)
  ensures  inv_p is f v1 v2 r1 r2 ** f ** v1
  opens is
{
  open Pulse.Lib.GhostReference;
  unfold inv_p;
  unfold inv_p';

  gather r1;

  let b1 = !r1;
  let b2 = !r2;

  let b1 : bool = reveal b1;
  let b2 : bool = reveal b2;

  if b2 {
    (* The "easy" case: the big pledge has already been claimed
    by the other subpledge, so we just extract our resource. *)
    assert (r1 |-> false);
    r1 := true;
    rewrite emp ** split_switch is false true f v1 v2
        as  split_switch is true true f v1 v2 ** v1;

    (* This should just disappear when we start normalizing
    the context. *)
    rewrite (match true, true with
              | false, false -> pledge is f (v1 ** v2)
              | false, true -> v1
              | true, false -> v2
              | true, true -> emp)
        as emp;

    share #_ r1;
    fold (inv_p' is f v1 v2 r1 r2 true true);
    fold inv_p;
    assert (f ** v1 ** inv_p is f v1 v2 r1 r2);
    drop_ (r1 |-> Frac 0.5R true);
  } else {
    (* The "hard" case: the big pledge has not been claimed.
    Claim it, split it, and store the leftover in the invariant. *)
    assert (r1 |-> false);

    rewrite split_switch is false false f v1 v2
        as  pledge is f (v1 ** v2);

    redeem_pledge is f (v1 ** v2);

    r1 := true;
    fold (split_switch is true false f v1 v2);

    share r1;

    fold (inv_p' is f v1 v2 r1 r2 true false);
    fold inv_p;
    assert (f ** v1 ** inv_p is f v1 v2 r1 r2);
    drop_ (r1 |-> Frac 0.5R true);
  }
}

ghost
fn elim_body_l1
  (#is:inames) (#f:slprop) (i : iname) (v1:slprop) (v2:slprop) (r1 r2 : GR.ref bool)
  ()
  requires f ** ((r1 |-> Frac 0.5R false) ** later_credit 1 ** inv i (inv_p is f v1 v2 r1 r2)) ** pure (not (mem_inv is i))
  ensures  f ** v1 ** inv i (inv_p is f v1 v2 r1 r2)
  opens add_inv is i
{
  open Pulse.Lib.GhostReference;
  assert (pure (not (mem_inv is i)));
  with_invariants i
  {
    later_elim _;
    do_elim_body_l #is #f v1 v2 r1 r2 ();
    later_intro (inv_p is f v1 v2 r1 r2);
  };
}

ghost
fn elim_body_l
  (#is:inames) (#f:slprop) (i : iname) (v1:slprop) (v2:slprop) (r1 r2 : GR.ref bool)
  ()
  requires f ** ((r1 |-> Frac 0.5R false) ** later_credit 1 ** inv i (inv_p is f v1 v2 r1 r2) ** pure (not (mem_inv is i)))
  ensures  f ** v1
  opens add_inv is i
{
  elim_body_l1 #is #f i v1 v2 r1 r2 ();
  drop_ (inv i (inv_p is f v1 v2 r1 r2));
  (* I couldn't make this work with an (annotated) with_invariants and
  then a drop, so I used an auxiliary _l1 function. *)
}


ghost
fn flip_invp
  (is:inames) (f:slprop) (v1:slprop) (v2:slprop) (r1 r2 : GR.ref bool)
  requires inv_p is f v1 v2 r1 r2
  ensures  inv_p is f v2 v1 r2 r1
{
  unfold inv_p;

  with b1 b2. assert (inv_p' is f v1 v2 r1 r2 b1 b2);

  unfold inv_p';

  (* This is now true with PulseCore. *)
  let _ = elim_slprop_equiv (slprop_equiv_comm v1 v2);
  assert (pure (v1 ** v2 == v2 ** v1));

  rewrite split_switch is b1 b2 f v1 v2
       as split_switch is b2 b1 f v2 v1
    by __tac ();

  fold (inv_p' is f v2 v1 r2 r1 b2 b1);
  fold inv_p;
}


// ghost
// fn elim_body_r
//   (#is:inames) (#f:slprop) (i : iname{not (mem_inv is i)}) (v1:slprop) (v2:slprop) (r1 r2 : GR.ref bool)
//   ()
//   requires f ** ((r2 |-> Frac 0.5R false) ** later_credit 1 ** inv i (inv_p is f v1 v2 r1 r2))
//   ensures  f ** v2 ** inv i (inv_p is f v1 v2 r1 r2)
//   opens add_inv is i
// {
//   // flip_invp is f v1 v2 r1 r2;
//   // elim_body_l #is #f v2 v1 r2 r1 ();
//   // flip_invp is f v2 v1 r2 r1;
// }

ghost
fn elim_body_r1
  (#is:inames) (#f:slprop) (i : iname) (v1:slprop) (v2:slprop) (r1 r2 : GR.ref bool)
  ()
  requires f ** ((r2 |-> Frac 0.5R false) ** later_credit 1 ** inv i (inv_p is f v1 v2 r1 r2) ** pure (not (mem_inv is i)))
  ensures  f ** v2 ** inv i (inv_p is f v1 v2 r1 r2)
  opens add_inv is i
{
  open Pulse.Lib.GhostReference;
  assert (pure (not (mem_inv is i)));
  with_invariants i
  {
    later_elim _;
    flip_invp is f v1 v2 r1 r2;
    do_elim_body_l #is #f v2 v1 r2 r1 ();
    flip_invp is f v2 v1 r2 r1;
    later_intro (inv_p is f v1 v2 r1 r2);
  };
}

ghost
fn elim_body_r
  (#is:inames) (#f:slprop) (i : iname) (v1:slprop) (v2:slprop) (r1 r2 : GR.ref bool)
  ()
  requires f ** ((r2 |-> Frac 0.5R false) ** later_credit 1 ** inv i (inv_p is f v1 v2 r1 r2) ** pure (not (mem_inv is i)))
  ensures  f ** v2
  opens add_inv is i
{
  elim_body_r1 #is #f i v1 v2 r1 r2 ();
  drop_ (inv i (inv_p is f v1 v2 r1 r2));
}

ghost
fn ghost_split_pledge (#is:inames) (#f:slprop) (v1:slprop) (v2:slprop)
  // requires pledge is f (v1 ** v2)
  // returns r : (e : inames_elem { not (mem_inv (inames_names is) (snd e)) })
  // ensures pledge (add_one r is) f v1 ** pledge (add_one r is) f v2
  // opens (inames_names is)
  requires pledge is f (v1 ** v2) ** later_credit 2
  returns i : iname
  ensures pledge (add_inv is i) f v1 ** pledge (add_inv is i) f v2 ** pure (not (mem_inv is i))
{
  pledge_inames_live is f (v1 ** v2);
  let r1 = GR.alloc false;
  let r2 = GR.alloc false;
  GR.share r1;
  GR.share r2;
  fold split_switch is false false f v1 v2;
  fold (inv_p' is f v1 v2 r1 r2 false false);
  fold inv_p;
  let i = fresh_invariant is (inv_p is f v1 v2 r1 r2);
  inames_live_inv i (inv_p is f v1 v2 r1 r2);
  gather_inames_live is (single i);
  Pulse.Class.Duplicable.dup (inv i (inv_p is f v1 v2 r1 r2)) ();

  let is' = add_inv is i;
  GhostSet.lemma_equal_intro (GhostSet.union is (single i)) is';
  rewrite (inames_live (GhostSet.union is (single i))) as (inames_live is');
  dup_inames_live is';
  later_credit_add 1 1;
  rewrite
    later_credit 2
  as
    later_credit 1 ** later_credit 1;

  make_pledge
    is'
    f
    v1
    ((r1 |-> Frac 0.5R false) ** later_credit 1 ** inv i (inv_p is f v1 v2 r1 r2) ** pure (not (mem_inv is i)))
    (elim_body_l #is #f i v1 v2 r1 r2);

  make_pledge
    is'
    f
    v2
    ((r2 |-> Frac 0.5R false) ** later_credit 1 ** inv i (inv_p is f v1 v2 r1 r2) ** pure (not (mem_inv is i)))
    (elim_body_r #is #f i v1 v2 r1 r2);

  rewrite each
    is'
  as
    add_inv is i;

  i
}

fn split_pledge (#is:inames) (#f:slprop) (v1:slprop) (v2:slprop)
  requires pledge is f (v1 ** v2)
  returns i : iname
  ensures pledge (add_inv is i) f v1 ** pledge (add_inv is i) f v2 ** pure (not (mem_inv is i))
{
  later_credit_buy 2;
  let i = ghost_split_pledge #is #f v1 v2;
  i
}

(* /split_pledge *)
