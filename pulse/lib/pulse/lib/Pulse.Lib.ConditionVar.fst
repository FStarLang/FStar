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

module Pulse.Lib.ConditionVar
#lang-pulse
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
module OR = Pulse.Lib.OnRange
module SLT = Pulse.Lib.SLPropTable
module Box = Pulse.Lib.Box

noeq
type cvar_t_core = {
  r: Box.box U32.t;
  tab : SLT.table
}

noeq
type cvar_t = {
  core: cvar_t_core;
  i: iname
}

let singleton #a (i:a) = Seq.create 1 i
let full_perm : perm = 1.0R

let predicate_at (t:SLT.table) (f:perm) (pred:Seq.seq slprop) (i:nat)
: slprop
= if i < Seq.length pred
  then SLT.pts_to t i #f (Seq.index pred i)
  else emp

[@@pulse_unfold]
let stored_predicates (t:SLT.table) (n:nat) (f:perm) (pred:Seq.seq slprop) 
= OR.on_range (predicate_at t f pred) 0 n

let index_preds (pred:Seq.seq slprop) (i:nat)
= if i < Seq.length pred then Seq.index pred i else emp

let istar (pred:Seq.seq slprop) 
= OR.on_range (index_preds pred) 0 (Seq.length pred)

ghost
fn weaken_on_range (f g: (nat -> slprop))
                   (i j:nat)
requires
  pure (
    (forall (x:nat { i <= x /\ x < j }). f x == g x)
  ) **
  OR.on_range f i j
ensures
  OR.on_range g i j
{
  OR.on_range_weaken f g i j = k { rewrite f k as g k }
}

let istar_singleton (p:slprop)
: Lemma (istar (singleton p) == p)
= slprop_equivs ();
  OR.on_range_eq_emp (index_preds (singleton p)) 1 1;
  OR.on_range_eq_cons (index_preds (singleton p)) 0 1

let maybe_holds (v:U32.t) (p:slprop) (pred:Seq.seq slprop)
: slprop
= if v = 0ul then equiv (istar pred) p else istar pred


let cvar_inv (b: cvar_t_core) (p:slprop)
: slprop
= exists* n preds v.
    SLT.is_table b.tab n **
    stored_predicates b.tab n 0.5R preds **
    Box.pts_to b.r #0.5R v **
    pure (Seq.length preds == n) **
    maybe_holds v p preds

let cvar (b: cvar_t) (p:slprop)
: slprop
= inv b.i (cvar_inv b.core p)

let inv_name (b:cvar_t) = b.i

let send (b: cvar_t) (p:slprop)
: slprop
= cvar b p **
  pts_to b.core.r #0.5R 0ul

let recv (b: cvar_t) (p:slprop)
: slprop
= exists* q i.
    cvar b q **
    SLT.pts_to b.core.tab i #0.5R p

fn create (p:slprop)
  requires emp
  returns c:cvar_t
  ensures send c p ** recv c p
{
  let r = Box.alloc 0ul;
  let tab = SLT.create ();
  SLT.alloc tab p;
  SLT.share tab 0 0.5R 0.5R;
  rewrite (SLT.pts_to tab 0 #0.5R p)
      as (predicate_at tab 0.5R (singleton p) 0);
  OR.on_range_singleton_intro (predicate_at tab 0.5R (singleton p)) 0;
  Box.share r;
  istar_singleton p;
  equiv_refl (istar (singleton p));
  rewrite (equiv (istar (singleton p)) (istar (singleton p)))
      as  (maybe_holds 0ul p (singleton p));
  let core = { r; tab };
  rewrite each r as core.r;
  rewrite each tab as core.tab;
  fold (cvar_inv core p);
  let i = new_invariant (cvar_inv core p);
  let cv = { core; i };
  rewrite each core as cv.core;
  rewrite each i as cv.i;
  dup_inv cv.i _;
  fold (cvar cv p);
  fold (send cv p);
  fold (cvar cv p);
  fold (recv cv p);
  cv
}

atomic
fn signal_atomic (b:cvar_t) (#p:slprop)
requires 
  send b p ** p ** later_credit 1
ensures 
  emp
  opens [inv_name b]
{
  unfold send;
  unfold cvar;
  with_invariants b.i
  returns _:unit
  ensures later (cvar_inv b.core p)
  {
     later_elim _;
     unfold cvar_inv;
     Box.gather b.core.r;
     with v preds. assert (maybe_holds v p preds);
     assert pure (v == 0ul);
     write_atomic_box b.core.r 1ul;
     rewrite (maybe_holds v p preds)
        as  (equiv (istar preds) p);
     equiv_comm _ _;
     equiv_elim p (istar preds);
     rewrite (istar preds) as (maybe_holds 1ul p preds);
     Box.share b.core.r;
     fold (cvar_inv b.core p);
     later_intro (cvar_inv b.core p);
     drop_ (Box.pts_to b.core.r #0.5R _)
  };
  drop_ _
}

fn signal (c:cvar_t) (#p:slprop)
  requires send c p ** p
  ensures emp
{
  later_credit_buy 1;
  signal_atomic c #p
}

ghost
fn weaken_and_put
  (f g: (nat -> slprop))
  (i j k:nat)
requires
  OR.on_range f i j **
  g j **
  OR.on_range f (j + 1) k **
  pure (
    i <= j /\ j < k /\
    (forall (x:nat { i <= x /\ x < k /\ x <> j }). f x == g x)
  )
ensures
  OR.on_range g i k
{
  weaken_on_range f g i j;
  weaken_on_range f g (j + 1) k; 
  OR.on_range_put i j k #g
}

ghost
fn get_predicate_at_i 
    (t:SLT.table)
    (i:nat)
    (p:slprop)
    (preds:Seq.seq slprop)
requires
  SLT.is_table t (Seq.length preds) **
  SLT.pts_to t i #0.5R p **
  stored_predicates t (Seq.length preds) 0.5R preds
  returns _:squash (i < Seq.length preds)
ensures
  SLT.is_table t (Seq.length preds) **
  SLT.pts_to t i #1.0R (Seq.index preds i) **
  OR.on_range (predicate_at t 0.5R preds) 0 i **
  OR.on_range (predicate_at t 0.5R preds) (i + 1) (Seq.length preds) **
  later (equiv (Seq.index preds i) p)
{
  SLT.in_bounds t;
  OR.on_range_get i;
  rewrite (predicate_at t 0.5R preds i)
       as (SLT.pts_to t i #0.5R (Seq.index preds i));
  SLT.gather t i #0.5R #0.5R #(Seq.index preds i) #p;
  ()
}

fn rec wait (b:cvar_t) (#p:slprop)
requires 
  recv b p
ensures
  p
{
  unfold recv;
  with i. assert (SLT.pts_to b.core.tab i #0.5R p);
  with q. assert (cvar b q);
  unfold cvar;
  later_credit_buy 1;
  later_credit_buy 1;
  // show_proof_state;
  let res:bool =
    with_invariants b.i
    returns res:bool
    ensures later (cvar_inv b.core q) **
            (if res then p else SLT.pts_to b.core.tab i #0.5R p)
    {
      later_elim _;
      unfold cvar_inv;
      let vv = read_atomic_box b.core.r;
      if (vv = 0ul)
      {
        fold (cvar_inv b.core q);
        later_intro (cvar_inv b.core q);
        drop_ (later_credit 1);
        false;
      }
      else
      {
        with v preds. assert (maybe_holds v q preds);
        rewrite (maybe_holds v q preds)
          as (istar preds);
        get_predicate_at_i b.core.tab i p preds;
        later_elim _;
        unfold istar;
        OR.on_range_get i #(index_preds preds);
        rewrite (index_preds preds i) as (Seq.index preds i);
        equiv_elim _ _;
        SLT.update b.core.tab i emp;
        let preds' : erased (Seq.seq slprop) = FStar.Seq.upd preds i emp;
        rewrite emp as (index_preds preds' i);
        weaken_and_put
            (index_preds preds)
            (index_preds preds')
            0 i (Seq.length preds');
        SLT.share b.core.tab i 0.5R 0.5R;
        rewrite SLT.pts_to b.core.tab i #0.5R emp 
            as (predicate_at b.core.tab 0.5R preds' i);
        weaken_and_put
            (predicate_at b.core.tab 0.5R preds) 
            (predicate_at b.core.tab 0.5R preds')
            0 i (Seq.length preds');
        fold (istar preds');
        rewrite (istar preds') as (maybe_holds v q preds');
        // fold (maybe_holds v q preds');
        fold (cvar_inv b.core q);
        later_intro (cvar_inv b.core q);
        drop_ (SLT.pts_to b.core.tab i #0.5R _);
        true
      }
    };
  if res { drop_ (inv b.i _); () } 
  else { 
    fold (cvar b q);
    fold (recv b p);
    wait b #p
  }
}

ghost
fn equiv_star_cong_r (p q r x:slprop)
requires
  equiv (p ** x) r **
  equiv x q
ensures
  equiv (p ** q) r
{
  equiv_star_congr p x q;
  rewrite (equiv x q) as (equiv x q ** equiv (p ** x) (p ** q));
  equiv_comm (p ** x) (p ** q);
  equiv_trans (p ** q) (p ** x) r;
  drop_ (equiv x q)
}

let istar_preds_preds'_eq
      (preds:Seq.seq slprop) 
      (i:nat{ i < Seq.length preds })
      (p1 p2:slprop)
: Lemma (
  let preds' = FStar.Seq.(snoc (snoc (Seq.upd preds i emp) p1) p2) in
  istar preds == 
  OR.on_range (index_preds preds') 0 (Seq.length preds) ** Seq.index preds i)
= let preds' = FStar.Seq.(snoc (snoc (Seq.upd preds i emp) p1) p2) in
  calc (==) {
    istar preds;
  (==) {}
    OR.on_range (index_preds preds) 0 (Seq.length preds);
  (==) { OR.on_range_eq_get (index_preds preds) 0 i (Seq.length preds) }
    OR.on_range (index_preds preds) 0 i ** index_preds preds i ** OR.on_range (index_preds preds) (i + 1) (Seq.length preds);
  (==) { 
      OR.on_range_frame (index_preds preds) (index_preds preds') 0 i;
      OR.on_range_frame (index_preds preds) (index_preds preds') (i + 1) (Seq.length preds) 
      }
    OR.on_range (index_preds preds') 0 i ** index_preds preds i ** OR.on_range (index_preds preds') (i + 1) (Seq.length preds);
  (==) { slprop_equivs () }
    (OR.on_range (index_preds preds') 0 i ** index_preds preds' i ** OR.on_range (index_preds preds') (i + 1) (Seq.length preds)) **
    index_preds preds i;
  (==) { OR.on_range_eq_get (index_preds preds') 0 i (Seq.length preds) }
    OR.on_range (index_preds preds') 0 (Seq.length preds) ** Seq.index preds i;
  }

let istar_preds'_tail 
      (preds:Seq.seq slprop) 
      (i:nat{ i < Seq.length preds })
      (p1 p2:slprop)
: Lemma (
    let preds' = FStar.Seq.(snoc (snoc (Seq.upd preds i emp) p1) p2) in
    p1 ** p2 == (OR.on_range (index_preds preds') (Seq.length preds) (Seq.length preds')))
=     let preds' = FStar.Seq.(snoc (snoc (Seq.upd preds i emp) p1) p2) in
  OR.on_range_eq_emp (index_preds preds') (Seq.length preds') (Seq.length preds');
  OR.on_range_eq_cons (index_preds preds') (Seq.length preds) (Seq.length preds');
  OR.on_range_eq_cons (index_preds preds') (Seq.length preds + 1) (Seq.length preds');
  slprop_equivs ()

ghost
fn rewrite_istar_equiv (preds:Seq.seq slprop) (preds':Seq.seq slprop) (i:nat{ i < Seq.length preds }) (p1 p2 q:slprop)
requires
  pure (preds' == FStar.Seq.(snoc (snoc (Seq.upd preds i emp) p1) p2)) **
  equiv (istar preds) q **
  later (equiv (Seq.index preds i) (p1 ** p2)) **
  later_credit 1
ensures
  equiv (istar preds') q
{
  later_elim _;
  istar_preds_preds'_eq preds i p1 p2;
  rewrite
    equiv (istar preds) q
  as
    equiv (OR.on_range (index_preds preds') 0 (Seq.length preds) ** Seq.index preds i) q
  ;
  equiv_star_cong_r _ _ _ _;
  istar_preds'_tail preds i p1 p2;
  OR.on_range_join_eq 0 (Seq.length preds) (Seq.length preds') (index_preds preds');

  rewrite equiv (OR.on_range (index_preds preds') 0 (Seq.length preds) ** (p1 ** p2)) q
       as equiv (istar preds') q;
}

ghost
fn rewrite_istar (preds:Seq.seq slprop) (preds':Seq.seq slprop) (i:nat{ i < Seq.length preds }) (p1 p2 q:slprop)
requires
  pure (preds' == FStar.Seq.(snoc (snoc (Seq.upd preds i emp) p1) p2)) **
  istar preds **
  later (equiv (Seq.index preds i) (p1 ** p2)) **
  later_credit 1
ensures
  istar preds'
{ 
  later_elim _;
  istar_preds_preds'_eq preds i p1 p2;
  rewrite (istar preds) as (OR.on_range (index_preds preds') 0 (Seq.length preds) ** Seq.index preds i);
  equiv_elim _ _;
  istar_preds'_tail preds i p1 p2;
  rewrite (p1 ** p2)
  as (OR.on_range (index_preds preds') (Seq.length preds) (Seq.length preds'));
  OR.on_range_join 0 (Seq.length preds) (Seq.length preds') #(index_preds preds');
  fold (istar preds')
}

ghost
fn split (b:cvar_t) (#p1 #p2:slprop)
requires 
  recv b (p1 ** p2) ** later_credit 2
ensures
  recv b p1 **
  recv b p2
opens
  add_inv emp_inames (inv_name b)
{
  later_credit_add 1 1;
  rewrite (later_credit 2) as (later_credit 1 ** later_credit 1);
  unfold recv;
  with i. assert (SLT.pts_to b.core.tab i #0.5R (p1 ** p2));
  with q. assert (cvar b q);
  unfold cvar;
  let _ : unit =
    with_invariants b.i
    returns _:unit
    ensures
      later (cvar_inv b.core q) **
      (exists* j k.
        SLT.pts_to b.core.tab j #0.5R p1 **
        SLT.pts_to b.core.tab k #0.5R p2)
    {
      later_elim _;
      unfold cvar_inv;
      with v preds. assert (maybe_holds v q preds);
      get_predicate_at_i b.core.tab i (p1 ** p2) preds;
      SLT.update b.core.tab i emp;
      SLT.share b.core.tab i 0.5R 0.5R;
      let preds' : erased (Seq.seq slprop) = 
        FStar.Seq.(snoc (snoc (upd preds i emp) p1) p2);
      rewrite SLT.pts_to b.core.tab i #0.5R emp
          as (predicate_at b.core.tab 0.5R preds' i);
      weaken_and_put
          (predicate_at b.core.tab 0.5R preds)
          (predicate_at b.core.tab 0.5R preds')
          0 i (Seq.length preds);
      SLT.alloc b.core.tab p1;
      SLT.share b.core.tab (Seq.length preds) 0.5R 0.5R;
      rewrite SLT.pts_to b.core.tab (Seq.length preds) #0.5R p1
          as (predicate_at b.core.tab 0.5R preds' (Seq.length preds));
      OR.on_range_snoc ();
      SLT.alloc b.core.tab p2;
      SLT.share b.core.tab (Seq.length preds + 1) 0.5R 0.5R;
      rewrite SLT.pts_to b.core.tab (Seq.length preds + 1) #0.5R p2
          as (predicate_at b.core.tab 0.5R preds' (Seq.length preds + 1));
      OR.on_range_snoc();
      let vz = (reveal v = 0ul);
      if (vz)
      {
        rewrite (maybe_holds v q preds) as (equiv (istar preds) q);
        OR.on_range_eq_get (index_preds preds) 0 i (Seq.length preds);
        rewrite_istar_equiv preds preds' i p1 p2 q;
        // show_proof_state;
        // step ();
        rewrite equiv (istar preds') q as maybe_holds v q preds';
        fold (cvar_inv b.core q);
        later_intro (cvar_inv b.core q);
        drop_ (SLT.pts_to b.core.tab i #0.5R emp);
      }
      else
      { 
        rewrite (maybe_holds v q preds) as (istar preds);
        rewrite_istar preds preds' i p1 p2 q;
        rewrite istar preds' as maybe_holds v q preds';
        fold (cvar_inv b.core q);
        later_intro (cvar_inv b.core q);
        drop_ (SLT.pts_to b.core.tab i #0.5R emp);
      }
    };
  dup_inv b.i _;
  fold (cvar b q);
  fold (recv b p1);
  fold (cvar b q);
  fold (recv b p2)
}
