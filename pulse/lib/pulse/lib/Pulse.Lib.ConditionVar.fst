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
open Pulse.Lib.SendableTrade
module U32 = FStar.UInt32
open Pulse.Lib.ForEvery
open Pulse.Lib.ForEvery.Range
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

let predicate_at (t:SLT.table) (f:perm) (pred:Seq.seq slprop) (i:nat)
: slprop
= if i < Seq.length pred
  then SLT.pts_to t i #f (Seq.index pred i)
  else emp

instance placeless_predicate_at t f pred i : placeless (predicate_at t f pred i) =
  if i < Seq.length pred then
    SLT.placeless_pts_to t i #f (Seq.index pred i)
  else
    placeless_emp

[@@pulse_unfold]
let stored_predicates (t:SLT.table) (n:nat) (f:perm) (pred:Seq.seq slprop) 
= forall+ (k:nat{0 <= k /\ k < n}). predicate_at t f pred k

let index_preds (pred:Seq.seq slprop) (i:nat)
= if i < Seq.length pred then sendable (Seq.index pred i) else emp

instance is_send_index_preds pred i : is_send (index_preds pred i) =
  if i < Seq.length pred then is_send_sendable (Seq.index pred i) else is_send_placeless emp

let istar (pred:Seq.seq slprop) 
= forall+ (k:nat{0 <= k /\ k < Seq.length pred}). index_preds pred k

ghost
fn weaken_on_range (f g: (nat -> slprop))
                   (i j:nat)
requires
  pure (
    (forall (x:nat { i <= x /\ x < j }). f x == g x)
  ) **
  (forall+ (k:nat{i <= k /\ k < j}). f k)
ensures
  forall+ (k:nat{i <= k /\ k < j}). g k
{
  range_weaken f g i j fn k { rewrite f k as g k }
}

let maybe_holds (v:U32.t) (p:slprop) (pred:Seq.seq slprop)
: slprop
= if v = 0ul then trade p (istar pred) else istar pred

instance is_send_maybe_holds v p pred : is_send (maybe_holds v p pred) =
  if v = 0ul then is_send_trade #emp_inames p (istar pred)
    else is_send_forevery #(k:nat{0 <= k /\ k < Seq.length pred}) (fun k -> index_preds pred k)

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

instance is_send_send c p : is_send (send c p) = Tactics.Typeclasses.solve
instance is_send_recv c p : is_send (recv c p) = Tactics.Typeclasses.solve

fn create (p:slprop) {| is_send p |}
  returns c:cvar_t
  ensures send c p
  ensures recv c p
{
  let r = Box.alloc 0ul;
  let tab = SLT.create ();
  SLT.alloc tab p;
  SLT.share tab 0 0.5R 0.5R;
  rewrite (SLT.pts_to tab 0 #0.5R p)
      as (predicate_at tab 0.5R (singleton p) 0);
  range_singleton_intro (predicate_at tab 0.5R (singleton p)) 0;
  Box.share r;
  intro (p @==> istar (singleton p)) fn _ {
    sendable_intro p #_;
    rewrite sendable p as index_preds (singleton p) 0;
    range_singleton_intro (index_preds (singleton p)) 0;
    forevery_refine_ext
      (fun (k:nat) -> 0 <= k /\ k < Seq.length (singleton p))
      (index_preds (singleton p));
    fold istar (singleton p);
  };
  fold maybe_holds 0ul p (singleton p);
  let core = { r; tab };
  rewrite each r as core.r;
  rewrite each tab as core.tab;
  fold (cvar_inv core p);
  let i = new_invariant (cvar_inv core p);
  let cv = { core; i };
  rewrite each core as cv.core;
  rewrite each i as cv.i;
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
  with_invariants_a unit emp_inames b.i (cvar_inv b.core p)
    (p ** Box.pts_to b.core.r #0.5R 0ul) (fun _ -> emp) fn _
  {
     unfold cvar_inv;
     Box.gather b.core.r;
     with v preds. unfold (maybe_holds (reveal v) p preds);
     assert rewrites_to v 0ul;
     write_atomic_box b.core.r 1ul;
     elim_trade p (istar preds);
     fold (maybe_holds 1ul p preds);
     Box.share b.core.r;
     fold (cvar_inv b.core p);
     drop_ (Box.pts_to b.core.r #0.5R _)
  };
}

fn signal (c:cvar_t) (#p:slprop)
  requires send c p
  requires p
{
  later_credit_buy 1;
  signal_atomic c #p
}

ghost
fn weaken_and_put
  (f g: (nat -> slprop))
  (i j k:nat)
requires
  (forall+ (kk:nat{i <= kk /\ kk < j}). f kk) **
  g j **
  (forall+ (kk:nat{j + 1 <= kk /\ kk < k}). f kk) **
  pure (
    i <= j /\ j < k /\
    (forall (x:nat { i <= x /\ x < k /\ x <> j }). f x == g x)
  )
ensures
  forall+ (kk:nat{i <= kk /\ kk < k}). g kk
{
  weaken_on_range f g i j;
  weaken_on_range f g (j + 1) k; 
  range_put g i j k
}

ghost
fn get_predicate_at_i 
    (t:SLT.table)
    (i:nat)
    (n:nat)
    (p:slprop)
    (preds:Seq.seq slprop)
requires
  SLT.is_table t n **
  SLT.pts_to t i #0.5R p **
  stored_predicates t n 0.5R preds **
  pure (Seq.length preds == n)
  returns _:squash (i < Seq.length preds)
ensures
  SLT.is_table t n **
  SLT.pts_to t i #1.0R (Seq.index preds i) **
  (forall+ (kk:nat{0 <= kk /\ kk < i}). predicate_at t 0.5R preds kk) **
  (forall+ (kk:nat{i + 1 <= kk /\ kk < n}). predicate_at t 0.5R preds kk) **
  later (equiv (Seq.index preds i) p)
{
  SLT.in_bounds t;
  range_get (predicate_at t 0.5R preds) 0 i n;
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
  let res =
    with_invariants bool emp_inames b.i (cvar_inv b.core q)
      (SLT.pts_to b.core.tab i #0.5R p ** later_credit 1)
      (fun res -> cond res p (SLT.pts_to b.core.tab i #0.5R p))
      fn _
    {
      unfold cvar_inv;
      let vv = read_atomic_box b.core.r;
      if (vv = 0ul)
      {
        fold (cvar_inv b.core q);
        fold cond false p (SLT.pts_to b.core.tab i #0.5R p);
        drop_ (later_credit 1);
        false;
      }
      else
      {
        with n preds v. assert (stored_predicates b.core.tab n 0.5R preds ** maybe_holds v q preds);
        rewrite (maybe_holds v q preds)
          as (istar preds);
        get_predicate_at_i b.core.tab i n p preds;
        unfold istar;
        range_get (index_preds preds) 0 i (Seq.length preds);
        rewrite (index_preds preds i) as sendable (Seq.index preds i);
        sendable_elim (Seq.index preds i);
        later_elim (equiv _ _);
        equiv_elim _ _;
        SLT.update b.core.tab i emp;
        let preds' : erased (Seq.seq slprop) = FStar.Seq.upd preds i emp;
        sendable_intro emp #_;
        rewrite sendable emp as (index_preds preds' i);
        weaken_and_put
            (index_preds preds)
            (index_preds preds')
            0 i (Seq.length preds);
        range_rebound (index_preds preds') 0 (Seq.length preds) 0 (Seq.length preds');
        SLT.share b.core.tab i 0.5R 0.5R;
        rewrite SLT.pts_to b.core.tab i #0.5R emp 
            as (predicate_at b.core.tab 0.5R preds' i);
        weaken_and_put
            (predicate_at b.core.tab 0.5R preds) 
            (predicate_at b.core.tab 0.5R preds')
            0 i n;
        fold (istar preds');
        rewrite (istar preds') as (maybe_holds v q preds');
        // fold (maybe_holds v q preds');
        fold (cvar_inv b.core q);
        drop_ (SLT.pts_to b.core.tab i #0.5R _);
        fold cond true p (SLT.pts_to b.core.tab i #0.5R p);
        true
      }
    };
  if res { elim_cond_true _ _ _; } 
  else { 
    elim_cond_false _ _ _;
    fold (cvar b q);
    fold (recv b p);
    wait b #p
  }
}

ghost
fn split (b:cvar_t) (#p1 #p2:slprop) {| is_send p1, is_send p2 |}
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
  with_invariants_g unit emp_inames b.i (cvar_inv b.core q)
    (later_credit 1 ** SLT.pts_to b.core.tab i #0.5R (p1 ** p2))
    (fun _ ->
      (exists* j k.
        SLT.pts_to b.core.tab j #0.5R p1 **
        SLT.pts_to b.core.tab k #0.5R p2))
    fn _ {
      unfold cvar_inv;
      with n preds v. assert (stored_predicates b.core.tab n 0.5R preds ** maybe_holds v q preds);
      get_predicate_at_i b.core.tab i n (p1 ** p2) preds;
      SLT.update b.core.tab i emp;
      SLT.share b.core.tab i 0.5R 0.5R;
      let preds' : erased (Seq.seq slprop) = 
        FStar.Seq.(snoc (snoc (upd preds i emp) p1) p2);
      rewrite SLT.pts_to b.core.tab i #0.5R emp
          as (predicate_at b.core.tab 0.5R preds' i);
      weaken_and_put
          (predicate_at b.core.tab 0.5R preds)
          (predicate_at b.core.tab 0.5R preds')
          0 i n;
      SLT.alloc b.core.tab p1;
      SLT.share b.core.tab n 0.5R 0.5R;
      rewrite SLT.pts_to b.core.tab n #0.5R p1
          as (predicate_at b.core.tab 0.5R preds' n);
      range_snoc (predicate_at b.core.tab 0.5R preds') 0 n;
      SLT.alloc b.core.tab p2;
      SLT.share b.core.tab (n + 1) 0.5R 0.5R;
      rewrite SLT.pts_to b.core.tab (n + 1) #0.5R p2
          as (predicate_at b.core.tab 0.5R preds' (n + 1));
      range_snoc (predicate_at b.core.tab 0.5R preds') 0 (n + 1);
      later_elim (equiv _ _);
      intro (istar preds @==> istar preds')
          #(equiv (Seq.Base.index preds i) (p1 ** p2)) fn _ {
        unfold istar preds;
        range_get (index_preds preds) 0 i (Seq.length preds);
        weaken_on_range (index_preds preds) (index_preds preds') 0 i;
        weaken_on_range (index_preds preds) (index_preds preds') (i+1) (Seq.length preds);
        sendable_intro emp #_;
        rewrite sendable emp as index_preds preds' i;
        range_put (index_preds preds') 0 i (Seq.length preds);
        rewrite index_preds preds i as sendable (Seq.index preds i);
        sendable_elim (Seq.index preds i);
        equiv_elim _ _;
        sendable_intro p1 #_; rewrite sendable p1 as index_preds preds' (Seq.length preds);
        sendable_intro p2 #_; rewrite sendable p2 as index_preds preds' (Seq.length preds + 1);
        range_snoc (index_preds preds') 0 (Seq.length preds);
        range_snoc (index_preds preds') 0 (Seq.length preds + 1);
        range_rebound (index_preds preds') 0 (Seq.length preds + 1 + 1) 0 (Seq.length preds');
        fold istar preds';
      };
      let vz = (reveal v = 0ul);
      if (vz)
      {
        rewrite (maybe_holds v q preds) as (q @==> istar preds);
        intro (q @==> istar preds')
            #(trade q (istar preds) ** trade (istar preds) (istar preds')) fn _ {
          elim_trade q (istar preds);
          elim_trade (istar preds) (istar preds');
        };
        rewrite (q @==> istar preds') as (maybe_holds v q preds');
        fold (cvar_inv b.core q);
        drop_ (SLT.pts_to b.core.tab i #0.5R emp);
      }
      else
      { 
        rewrite (maybe_holds v q preds) as (istar preds);
        elim_trade (istar preds) (istar preds');
        rewrite (istar preds') as (maybe_holds v q preds');
        fold (cvar_inv b.core q);
        drop_ (SLT.pts_to b.core.tab i #0.5R emp);
      }
    };
  fold (cvar b q);
  fold (recv b p1);
  fold (cvar b q);
  fold (recv b p2)
}
