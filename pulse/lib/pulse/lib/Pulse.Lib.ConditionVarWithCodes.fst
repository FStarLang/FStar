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

module Pulse.Lib.ConditionVarWithCodes
#lang-pulse
open Pulse.Lib.Pervasives
// open Pulse.Lib.Codeable
module PM = Pulse.Lib.PCMMap
module PF = Pulse.Lib.PCM.Fraction
module U32 = FStar.UInt32
module GR = Pulse.Lib.GhostReference
module OR = Pulse.Lib.OnRange
#push-options "--fuel 0 --ifuel 2"
let small_slprop_map (#c:code) = PM.pointwise nat (PF.pcm_frac #c.t)
let carrier (c:code) = PM.map nat (PF.fractional c.t)

noeq
type cvar_t_core (c:code) = {
  r: Box.box U32.t;
  ctr : GR.ref nat;
  gref: ghost_pcm_ref (small_slprop_map #c);
}

noeq type cvar_t c = {
  core: cvar_t_core c;
  i: iname
}

let full_perm : perm = 1.0R

let empty_map_below #c (n:nat)
: carrier c
= Map.map_literal 
  (fun (k:nat) -> 
    if k < n
    then None
    else Some (c.emp, full_perm))

let predicate_at #c (m:carrier c) (i:nat)
: slprop3
= match Map.sel m i with
  | None ->
    pure False
  | Some f ->
    c.up (fst f)

let all_perms #c (m:carrier c) (i j:nat) (p:perm) =
  forall k. 
    i <= k /\ k < j ==>
    (match Map.sel m k with
     | None -> False
     | Some (_, q) -> p == q)

let map_invariant0 #c (m:carrier c) (n:nat) (p:slprop)
= pure (p == OR.on_range (predicate_at m) 0 n /\ all_perms m 0 n 0.5R)

let map_invariant #c (v:U32.t) (m:carrier c) (n:nat) (p:slprop)
: slprop3
= if v = 0ul
  then map_invariant0 m n p
  else OR.on_range (predicate_at m) 0 n ** pure (all_perms m 0 n 0.5R)

let cvar_inv #c (b: cvar_t_core c) (p:slprop)
: slprop3
= exists* v n m.
    pts_to b.r #0.5R v **
    pts_to b.ctr n **
    big_ghost_pcm_pts_to b.gref m **
    big_ghost_pcm_pts_to b.gref (empty_map_below n) **
    map_invariant v m n p

let cvar #c (b: cvar_t c) (p:slprop)
: slprop
= inv b.i (cvar_inv b.core p)

let inv_name #c (b:cvar_t c) = b.i

let send #c (b: cvar_t c) (p:slprop)
: slprop
= cvar b p **
  pts_to b.core.r #0.5R 0ul

let singleton #c (i:nat) (#p:perm) (code:c.t)
: carrier c
= Map.map_literal 
    (fun (k:nat) ->
        if k = i
        then Some (code, p)
        else None)

let recv #c (b:cvar_t c) (q:slprop)
: slprop
= exists* p i code.
    cvar b p **
    big_ghost_pcm_pts_to b.core.gref (singleton i #0.5R code) **
    pure (c.up code == q)


ghost
fn unfold_map_invariant0 #c v (m:carrier c) n p
requires map_invariant #c v m n p ** pure (v == 0ul)
ensures pure (p == OR.on_range (predicate_at m) 0 n /\ all_perms m 0 n 0.5R)
{
  rewrite each v as 0ul;
  unfold map_invariant;
  unfold map_invariant0;
}



ghost
fn fold_map_invariant0 #c (m:carrier c) n p
requires pure (p == OR.on_range (predicate_at m) 0 n /\ all_perms m 0 n 0.5R)
ensures map_invariant 0ul m n p
{
  fold (map_invariant0 m n p);
  fold (map_invariant 0ul m n p)
}



ghost
fn fold_map_invariant1 #c v (m:carrier c) n p
requires
  OR.on_range (predicate_at m) 0 n **
  pure (all_perms m 0 n 0.5R) **
  pure (v =!= 0ul)
ensures
  map_invariant v m n p
{
  rewrite (OR.on_range (predicate_at m) 0 n ** pure (all_perms m 0 n 0.5R))
  as      map_invariant v m n p
}



ghost
fn unfold_map_invariant1 #c v (m:carrier c) n p
requires map_invariant v m n p ** pure (v =!= 0ul)
ensures
  OR.on_range (predicate_at m) 0 n **
  pure (all_perms m 0 n 0.5R)
{
  rewrite (map_invariant v m n p)
       as (OR.on_range (predicate_at m) 0 n ** pure (all_perms m 0 n 0.5R));
}




ghost
fn map_invariant_all_perms #c v (m:carrier c) n p
requires map_invariant v m n p
ensures  map_invariant v m n p ** pure (all_perms m 0 n 0.5R)
{
  if (v = 0ul)
  {
     unfold_map_invariant0 #c _ _ _ _; //without the #c I get a inference failure
     fold_map_invariant0 m n p;
     rewrite each 0ul as v;
  }
  else {
    unfold_map_invariant1 #c _ _ _ _;
    fold_map_invariant1 v m n p;
  }
}



ghost
fn flip_map_invariant #c (v:U32.t) (p:slprop) (m:carrier c) (n:nat)
requires map_invariant v m n p ** p ** pure (v == 0ul)
ensures map_invariant 1ul m n p
{
  unfold_map_invariant0 v m n p;
  rewrite p as OR.on_range (predicate_at m) 0 n;
  fold_map_invariant1 1ul m n p;
}


let composable #c (c0:carrier c) (c1:carrier c)
= PM.composable_maps PF.pcm_frac c0 c1

let comp #c (c0:carrier c) (c1:carrier c { composable c0 c1 })
: carrier c
= PM.compose_maps PF.pcm_frac c0 c1

let on_range_singleton (#c:code) (p:c.t)
: Lemma (OR.on_range (predicate_at (singleton 0 #0.5R p)) 0 1 == c.up p)
= let m = (singleton 0 #0.5R p) in
  calc (==) {
    OR.on_range (predicate_at m) 0 1;
  (==) { OR.on_range_eq_cons (predicate_at m) 0 1;
         OR.on_range_eq_emp (predicate_at m) 1 1 }
    predicate_at m 0 ** emp;
  (==) { slprop_equivs () }
    predicate_at m 0;
  (==) {}
    c.up p;
  }
  
  

ghost
fn intro_init_map_invariant (#c:code) (p:slprop) (code_of_p:codeable c p)
requires emp
ensures map_invariant 0ul (singleton 0 #0.5R code_of_p.c) 1 p
{
  on_range_singleton code_of_p.c; //inlining the calc does not work
  fold_map_invariant0 (singleton 0 #0.5R code_of_p.c) 1 p;
}


let initial_map (#c:code) (p:c.t)
: c:carrier c { small_slprop_map.refine c }
= comp (singleton 0 #1.0R p) (empty_map_below 1)



ghost
fn fold_cvar_inv #c (b: cvar_t_core c) (p:slprop)
                    (v n m:_)
requires
    pts_to b.r #0.5R v **
    pts_to b.ctr n **
    big_ghost_pcm_pts_to b.gref m **
    big_ghost_pcm_pts_to b.gref (empty_map_below n) **
    map_invariant v m n p
ensures
    cvar_inv b p
{
  fold cvar_inv
}



ghost
fn frame_predicate_at #c (m0:carrier c) (i j:nat) (k:nat) (v:_)
requires OR.on_range (predicate_at m0) i j ** 
         pure ((j <= k \/ k < i))
ensures OR.on_range (predicate_at (Map.upd m0 k v)) i j
{
  OR.on_range_frame (predicate_at m0) (predicate_at (Map.upd m0 k v)) i j;
  rewrite (OR.on_range (predicate_at m0) i j)
       as (OR.on_range (predicate_at (Map.upd m0 k v)) i j);
}



ghost
fn predicate_at_singleton #c (m:carrier c) (i:nat) (q:slprop) (code_of_q:codeable c q)
requires q ** pure (Map.sel m i == Some (code_of_q.c, 0.5R))
ensures predicate_at m i
{
  rewrite q as (predicate_at m i)
}




fn create (#c:code) (p:slprop) (code_of_p:codeable c p)
requires emp
returns b:cvar_t c
ensures send b p ** recv b p
{ 
  let r = Box.alloc 0ul;
  let ctr = GR.alloc #nat 1;
  let gref = big_ghost_alloc #_ #small_slprop_map (initial_map code_of_p.c);
  big_ghost_share gref (singleton 0 #1.0R code_of_p.c) (empty_map_below 1);
  assert pure (singleton 0 #1.0R code_of_p.c `Map.equal` comp (singleton 0 #0.5R code_of_p.c) (singleton 0 #0.5R code_of_p.c));
  rewrite each (singleton 0 #1.0R code_of_p.c) 
          as (comp (singleton 0 #0.5R code_of_p.c) (singleton 0 #0.5R code_of_p.c));
  big_ghost_share gref (singleton 0 #0.5R code_of_p.c) (singleton 0 #0.5R code_of_p.c);
  Box.share2 r;
  intro_init_map_invariant p code_of_p;
  let b = { r; ctr; gref };
  rewrite each r as b.r, gref as b.gref, ctr as b.ctr;
  fold (cvar_inv b p);
  let i = new_invariant (cvar_inv b p);
  let bb = { core = b; i = i };
  rewrite each b as bb.core;
  rewrite each i as bb.i;
  dup_inv _ _;
  fold (cvar bb p);
  fold (send bb p);
  fold (cvar bb p);
  with v. rewrite (big_ghost_pcm_pts_to bb.core.gref v) as
          (big_ghost_pcm_pts_to bb.core.gref (singleton 0 #0.5R code_of_p.c));
  fold (recv bb p);
  bb
}




fn signal #c (b:cvar_t c) (#p:slprop)
requires send b p ** p
ensures emp
{
  unfold send;
  unfold cvar;
  with_invariants b.i 
  returns u:unit
  ensures cvar_inv b.core p ** emp
  {
    unfold cvar_inv;
    Box.gather b.core.r;
    write_atomic_box b.core.r 1ul;
    Box.share b.core.r;
    drop_ (pts_to b.core.r #0.5R 1ul);
    flip_map_invariant #c _ _ _ _;
    fold (cvar_inv b.core p);
  };
  drop_ (inv b.i _)
}



let predicate_at_i_is_q_lemma #c (m:carrier c) (i:nat) (n:nat) (q:c.t)
: Lemma
  (requires
    composable (singleton i #0.5R q) m /\
    composable (comp (singleton i #0.5R q) m) (empty_map_below n))
  (ensures
    i < n /\
    (Some? (Map.sel m i) ==> fst (Some?.v (Map.sel m i)) == q))
= if i < n
  then (
    match Map.sel m i with
    | None -> ()
    | Some (qq, pp) -> ()
  )
  else (
    match Map.sel (empty_map_below #c n) i with
    | None -> ()
    | Some (_, pp) ->
      assert (pp == 1.0R);
      ()
  )


ghost
fn elim_on_range_at_i #c (m:carrier c) (i n:nat)
requires OR.on_range (predicate_at m) 0 n ** pure (i < n)
ensures OR.on_range (predicate_at m) 0 n ** pure (Some? (Map.sel m i))
{
  OR.on_range_get i;
  match Map.sel m i {
    None -> {
      rewrite (predicate_at m i) as pure False;
      unreachable();
    }

    Some _ -> {
      OR.on_range_put 0 i n;
    }
  }
}



ghost
fn composable_three #c (gref:ghost_pcm_ref small_slprop_map) (c0 c1 c2:carrier c)
requires
  big_ghost_pcm_pts_to gref c0 **
  big_ghost_pcm_pts_to gref c1 **
  big_ghost_pcm_pts_to gref c2
ensures
  big_ghost_pcm_pts_to gref c0 **
  big_ghost_pcm_pts_to gref c1 **
  big_ghost_pcm_pts_to gref c2 **
  pure (composable c0 c1 /\ composable (comp c0 c1) c2)
{
  big_ghost_gather gref c0 c1;
  big_ghost_gather gref (comp c0 c1) c2;
  big_ghost_share gref (comp c0 c1) c2;
  big_ghost_share gref c0 c1;
}



ghost
fn elim_predicate_at_alt #c (m:carrier c) (i:nat) (_:squash (Some? (Map.sel m i)))
requires predicate_at m i
ensures c.up (fst (Some?.v (Map.sel m i)))
{
  rewrite (predicate_at m i) 
      as  (c.up (fst (Some?.v (Map.sel m i))));
}



ghost
fn q_at_i #c (#gref:ghost_pcm_ref small_slprop_map) (#m:carrier c) (#i #n:nat) (#q:c.t) ()
requires
  big_ghost_pcm_pts_to gref (singleton i #0.5R q) **
  big_ghost_pcm_pts_to gref m **
  big_ghost_pcm_pts_to gref (empty_map_below n) **
  pure (all_perms m 0 n 0.5R)
ensures
  big_ghost_pcm_pts_to gref (singleton i #0.5R q) **
  big_ghost_pcm_pts_to gref m **
  big_ghost_pcm_pts_to gref (empty_map_below n) **
  pure (Map.sel m i == Some (q, 0.5R) /\
        i < n /\
        (forall j. n <= j ==> Map.sel m j == None))
{
  composable_three _ (empty_map_below n) m _; (* disambig *)
  predicate_at_i_is_q_lemma m i n q;
  ()
}



ghost
fn predicate_at_i_is_q #c (#gref:ghost_pcm_ref small_slprop_map) (#v:U32.t) (#m:carrier c) (#i #n:nat) (#p:slprop) (#q:c.t) ()
requires
  big_ghost_pcm_pts_to gref (singleton i #0.5R q) **
  big_ghost_pcm_pts_to gref m **
  big_ghost_pcm_pts_to gref (empty_map_below n) **
  map_invariant v m n p **
  pure (v =!= 0ul)
ensures
  big_ghost_pcm_pts_to gref (singleton i #0.5R q) **
  big_ghost_pcm_pts_to gref m **
  big_ghost_pcm_pts_to gref (empty_map_below n) **
  OR.on_range (predicate_at m) 0 i **
  c.up q **
  OR.on_range (predicate_at m) (i + 1) n **
  pure (Map.sel m i == Some (q, 0.5R)) **
  pure (i < n /\ all_perms m 0 n 0.5R)
{
  map_invariant_all_perms v m n p;
  q_at_i #c ();
  unfold_map_invariant1 v m n p;
  elim_on_range_at_i m i n;
  OR.on_range_get i;
  match Map.sel m i {
    None -> {
      rewrite (predicate_at m i) as pure False;
      unreachable();
    }

    Some f -> {
      elim_predicate_at_alt m i ();
      ()
    }   
  }
}


let code_of_emp #c : codeable c emp =  { c = c.emp; laws = () }



ghost
fn clear_i #c (#gref:ghost_pcm_ref small_slprop_map) (#m:carrier c) (#i #n:nat) (#q:c.t) ()
requires
  big_ghost_pcm_pts_to gref (singleton i #0.5R q) **
  big_ghost_pcm_pts_to gref m **
  pure (Map.sel m i == Some (q, 0.5R)) **
  OR.on_range (predicate_at m) 0 i **
  OR.on_range (predicate_at m) (i + 1) n **
  pure (i < n /\ all_perms m 0 n 0.5R)
returns m': erased (carrier c)
ensures
  big_ghost_pcm_pts_to gref m' **
  big_ghost_pcm_pts_to gref (singleton i #0.5R c.emp) **
  OR.on_range (predicate_at m') 0 n **
  pure (all_perms m' 0 n 0.5R)
{
  (* big_ghost_gather is ambiguous, but we need
  to gather in this order, so make it explicit. Maybe
  pcm ops should not be allow_ambiguous? It's commutative,
  of course, but the expressions are different. *)
  big_ghost_gather gref (singleton i #0.5R q) m;
  big_ghost_write gref _ _
    (PM.lift_frame_preserving_upd
        _ _
        (PF.mk_frame_preserving_upd q c.emp)
        (comp (singleton i #0.5R q) m)
        i);
  with m'. assert (big_ghost_pcm_pts_to gref m');
  assert pure (Map.equal m' (comp (singleton i #0.5R c.emp) (Map.upd m i (Some (c.emp, 0.5R)))));
  rewrite (big_ghost_pcm_pts_to gref m') as
          (big_ghost_pcm_pts_to gref (comp (singleton i #0.5R c.emp) (Map.upd m i (Some (c.emp, 0.5R)))));
  big_ghost_share gref (singleton i #0.5R c.emp) (Map.upd m i (Some (c.emp, 0.5R)));
  frame_predicate_at m 0 i i (Some (c.emp, 0.5R));
  frame_predicate_at m (i + 1) n i (Some (c.emp, 0.5R));
  predicate_at_singleton (Map.upd m i (Some (c.emp, 0.5R))) i emp (code_of_emp #c);
  OR.on_range_put 0 i n;
  rewrite (OR.on_range (predicate_at (Map.upd m i (Some (c.emp, 0.5R)))) 0 n)
      as  OR.on_range (predicate_at (reveal (hide (Map.upd m i (Some (c.emp, 0.5R))) ))) 0 n;
  hide #(carrier c) (Map.upd m i (Some (c.emp, 0.5R))) 
}



fn rec wait #c (b:cvar_t c) (#q:slprop)
requires recv b q
ensures q
{
  unfold recv;
  with pp i code. _;
  assert (cvar b pp);
  assert (big_ghost_pcm_pts_to b.core.gref (singleton i #0.5R code));
  unfold cvar;
  let res : bool =
    with_invariants b.i
    returns res:bool
    ensures cvar_inv b.core pp **
            (cond res q (big_ghost_pcm_pts_to b.core.gref (singleton i #0.5R code)))
    {
      unfold cvar_inv;
      with _v m n. assert (map_invariant #c _v m n pp);
      let v = read_atomic_box b.core.r;
      if (v = 0ul)
      {
        intro_cond_false
          q
          (big_ghost_pcm_pts_to b.core.gref (singleton i #0.5R code));
        fold (cvar_inv b.core pp);
        false;
      }
      else
      {
        predicate_at_i_is_q #c ();
        let m' = clear_i #c ();
        rewrite (c.up code) as q;
        intro_cond_true q (big_ghost_pcm_pts_to b.core.gref (singleton i #0.5R code));
        rewrite (OR.on_range (predicate_at m') 0 n ** pure (all_perms m' 0 n 0.5R))
            as  (map_invariant #c _v m' n pp);
        fold_cvar_inv _ _ _ _ m';
        drop_ (big_ghost_pcm_pts_to b.core.gref _);
        true;
      }
    };
  if res
  {
    elim_cond_true _ _ _;
    drop_ (inv b.i _);
  }
  else 
  {
    elim_cond_false _ _ _;
    fold (cvar b pp);
    fold (recv b q);
    wait b #q;
  }
}


let split_aux_post #c (b:cvar_t c) (q r:c.t)
: slprop
= exists* j k.
    big_ghost_pcm_pts_to b.core.gref (singleton j #0.5R q) **
    big_ghost_pcm_pts_to b.core.gref (singleton k #0.5R r)





ghost
fn upd_i #c (#gref:ghost_pcm_ref small_slprop_map) (#m:carrier c) (#i:nat) (#q:c.t) ()
requires
  big_ghost_pcm_pts_to gref (singleton i #0.5R q) **
  big_ghost_pcm_pts_to gref m **
  pure (Map.sel m i == Some (q, 0.5R))
returns m': erased (carrier c)
ensures
  big_ghost_pcm_pts_to gref m' **
  pure (m' == Map.upd m i (Some (c.emp, 0.5R)))
{
  big_ghost_gather gref (singleton i #0.5R q) m;
  big_ghost_write gref _ _
    (PM.lift_frame_preserving_upd
        _ _
        (PF.mk_frame_preserving_upd q c.emp)
        (comp (singleton i #0.5R q) m)
        i);
  with m'. assert (big_ghost_pcm_pts_to gref m');
  assert pure (Map.equal m' (comp (singleton i #0.5R c.emp) (Map.upd m i (Some (c.emp, 0.5R)))));
  rewrite (big_ghost_pcm_pts_to gref m') as
          (big_ghost_pcm_pts_to gref (comp (singleton i #0.5R c.emp) (Map.upd m i (Some (c.emp, 0.5R)))));
  big_ghost_share gref (singleton i #0.5R c.emp) (Map.upd m i (Some (c.emp, 0.5R)));
  drop_ (big_ghost_pcm_pts_to gref (singleton i #0.5R c.emp));
  hide #(carrier c) (Map.upd m i (Some (c.emp, 0.5R))) 
}



ghost
fn alloc #c (#b:cvar_t_core c) (#n:nat) (q:c.t)
requires big_ghost_pcm_pts_to b.gref (empty_map_below n) **
         pts_to b.ctr n
ensures  GR.pts_to b.ctr (n + 1) **
         big_ghost_pcm_pts_to b.gref (empty_map_below (n + 1)) **
         big_ghost_pcm_pts_to b.gref (singleton n #0.5R q) **
         big_ghost_pcm_pts_to b.gref (singleton n #0.5R q)
{
  GR.write b.ctr (n + 1);
//  down3_emp();
  assert pure (Map.equal (empty_map_below n) (comp (singleton n #1.0R c.emp) (empty_map_below (n + 1))));
  rewrite (big_ghost_pcm_pts_to b.gref (empty_map_below n))
  as      (big_ghost_pcm_pts_to b.gref (comp (singleton n #1.0R c.emp) (empty_map_below (n + 1))));
  big_ghost_share b.gref (singleton n #1.0R c.emp) (empty_map_below (n + 1));
  big_ghost_write b.gref _ _
   (PM.lift_frame_preserving_upd
        _ _
        (PF.mk_frame_preserving_upd c.emp q)
        (singleton n #1.0R c.emp)
        n);
  with m. assert (
    big_ghost_pcm_pts_to b.gref (empty_map_below (n + 1)) ** (* frame *)
    big_ghost_pcm_pts_to b.gref m
  );
  assert pure (Map.equal m
                         (comp (singleton n #0.5R q) (singleton n #0.5R q)));
  rewrite (big_ghost_pcm_pts_to b.gref m)
  as      (big_ghost_pcm_pts_to b.gref (comp (singleton n #0.5R q) (singleton n #0.5R q)));
  big_ghost_share b.gref (singleton n #0.5R q) (singleton n #0.5R q);
}


let up_i #c (m:carrier c) (i:nat) (p:c.t) = Map.upd m i (Some (p, 0.5R))
let split_map #c (m:carrier c) (i n:nat) (q r:c.t) = (up_i (up_i (up_i m i c.emp) n q) (n + 1) r)

let split_lemma #c 
  (b:cvar_t_core c) 
  (m:carrier c)
  (q r:slprop) 
  (cq:codeable c q)
  (cr:codeable c r)
  (cqr:c.t)
  (i n:nat)
: Lemma
(requires
  c.up cqr == (q ** r) /\
  i < n /\
  Map.sel m i == Some (cqr, 0.5R))
(ensures OR.on_range (predicate_at m) 0 n ==
         OR.on_range (predicate_at (split_map m i n cq.c cr.c)) 0 (n + 2))
= let m' = (split_map m i n cq.c cr.c) in
  calc (==) {
    OR.on_range (predicate_at m) 0 n;
  (==) { OR.on_range_eq_get (predicate_at m) 0 i n }
    OR.on_range (predicate_at m) 0 i **
    c.up cqr **
    OR.on_range (predicate_at m) (i + 1) n;
  (==) { }
    OR.on_range (predicate_at m) 0 i **
    (q ** r) **
    OR.on_range (predicate_at m) (i + 1) n;
  (==) { slprop_equivs () }
   (OR.on_range (predicate_at m) 0 i **
    emp **
    OR.on_range (predicate_at m) (i + 1) n) **
    q ** r;
  (==){
        OR.on_range_frame (predicate_at m) (predicate_at m') 0 i;
        OR.on_range_frame (predicate_at m) (predicate_at m') (i + 1) n
      }
    (OR.on_range (predicate_at m') 0 i **
    emp ** 
    OR.on_range (predicate_at m') (i + 1) n) ** q ** r;
  (==) { OR.on_range_eq_get (predicate_at m') 0 i n }
    (OR.on_range (predicate_at m') 0 n ** q) ** r;
  (==) { OR.on_range_eq_snoc (predicate_at m') 0 n }
    OR.on_range (predicate_at m') 0 (n + 1) ** r;
  (==) { OR.on_range_eq_snoc (predicate_at m') 0 (n + 1) }
    OR.on_range (predicate_at m') 0 (n + 2);
  }


ghost
fn split_aux #c (b:cvar_t c) (p:erased slprop) 
    (q r:slprop)
    (cq:codeable c q)
    (cr:codeable c r)
    (i:erased nat)
    (cqr:c.t)
requires cvar_inv b.core p **
         big_ghost_pcm_pts_to b.core.gref (singleton i #0.5R cqr) **
         pure (c.up cqr == (q ** r))
ensures  cvar_inv b.core p ** split_aux_post b cq.c cr.c
{
  unfold cvar_inv;
  with v m n. assert (map_invariant #c v m n p);
  map_invariant_all_perms v m n p;
  q_at_i #c ();
  let m' = upd_i #c #_ #m #_ ();
  alloc #c cq.c;
  alloc #c cr.c;
  big_ghost_gather b.core.gref m' (singleton n #0.5R cq.c);
  big_ghost_gather b.core.gref (comp m' (singleton n #0.5R cq.c)) (singleton (n + 1) #0.5R cr.c);
  assert (pure (Map.equal (comp (comp m' (singleton n #0.5R cq.c)) (singleton (n + 1) #0.5R cr.c))
                          (split_map m i n cq.c cr.c)));
  rewrite (big_ghost_pcm_pts_to b.core.gref (comp (comp m' (singleton n #0.5R cq.c)) (singleton (n + 1) #0.5R cr.c)))
       as (big_ghost_pcm_pts_to b.core.gref (split_map m i n cq.c cr.c));
  fold (split_aux_post b cq.c cr.c);
  split_lemma b.core m q r cq cr cqr i n;
  let vv = reveal v;
  if (vv = 0ul)
  {
    rewrite (map_invariant v m n p) as (map_invariant0 m n p);
    unfold map_invariant0;
    fold (map_invariant0 (split_map m i n cq.c cr.c) (n + 2) p);
    fold (map_invariant 0ul (split_map m i n cq.c cr.c) (n + 2) p);
    fold_cvar_inv b.core p 0ul (n + 2) (split_map m i n cq.c cr.c);
  }
  else
  {
    unfold_map_invariant1 #c _ _ _ _;
    rewrite (OR.on_range (predicate_at m) 0 n)
    as      (OR.on_range (predicate_at (split_map m i n cq.c cr.c)) 0 (n + 2));
    fold_map_invariant1 v (split_map m i n cq.c cr.c) (n + 2) p;
    fold_cvar_inv b.core p v (n + 2) (split_map m i n cq.c cr.c);
  }
 
}



ghost
fn fold_recv #c (b:cvar_t c) (q:slprop) (#code:c.t) (#p:slprop) (#i:nat)
requires
    cvar b p **
    big_ghost_pcm_pts_to b.core.gref (singleton i #0.5R code) **
    pure (q == c.up code)
ensures
    recv b q
{
  fold (recv b q)
}



ghost
fn split #c (b:cvar_t c) (#q #r:slprop) (cq:codeable c q) (cr:codeable c r)
requires recv b (q ** r)
ensures recv b q ** recv b r
opens [b.i]
{
  unfold recv;
  with p i code. _;
  unfold cvar;
  with_invariants b.i
  returns u:unit
  ensures cvar_inv b.core (reveal p) **
         (exists* j k.
            big_ghost_pcm_pts_to b.core.gref (singleton j #0.5R cq.c) **
            big_ghost_pcm_pts_to b.core.gref (singleton k #0.5R cr.c))
  {
    split_aux b p q r cq cr i code;
    unfold split_aux_post;
  };
  with j k. _;
  dup_inv _ _;
  fold (cvar b p);
  fold_recv #c b q #cq.c;
  fold (cvar b p);
  fold (recv b r)
}



let cvinv #c (cv:cvar_t c) (p:slprop): slprop = cvar cv p


ghost
fn dup_cvinv #c (cv:cvar_t c) (#p:slprop)
requires cvinv cv p
ensures cvinv cv p ** cvinv cv p
{
  unfold cvinv;
  unfold cvar;
  dup_inv _ _;
  fold cvar;
  fold cvar;
  fold (cvinv cv p);
  fold (cvinv cv p);
}


let send_core #c (cv:cvar_t c) : slprop3 =
  pts_to cv.core.r #0.5R 0ul


ghost
fn decompose_send #c (cv:cvar_t c) (p:slprop)
requires send cv p
ensures cvinv cv p ** send_core cv
{
  unfold send;
  fold (cvinv cv p);
  fold (send_core cv);
}



ghost
fn recompose_send #c (cv:cvar_t c) (p:slprop)
requires cvinv cv p ** send_core cv
ensures send cv p
{
  unfold send_core;
  unfold cvinv;
  fold send;
}


let recv_core #c (cv:cvar_t c) (q:slprop)
: slprop3
= exists* i code.
    big_ghost_pcm_pts_to cv.core.gref (singleton i #0.5R code) **
    pure (c.up code == q)


ghost
fn decompose_recv #c (cv:cvar_t c) (p:slprop)
requires recv cv p
ensures (exists* q. cvinv cv q) ** recv_core cv p
{
  unfold recv;
  fold cvinv;
  fold recv_core;
}



ghost
fn recompose_recv #c (cv:cvar_t c) (p:slprop) (#q:_)
requires cvinv cv q ** recv_core cv p
ensures recv cv p
{
  unfold recv_core;
  unfold cvinv;
  fold recv;
}

