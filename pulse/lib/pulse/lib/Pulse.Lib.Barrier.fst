module Pulse.Lib.Barrier
open Pulse.Lib.Pervasives
module PM = Pulse.Lib.PCMMap
module PF = Pulse.Lib.PCM.Fraction
module U32 = FStar.UInt32
module GR = Pulse.Lib.GhostReference
module OR = Pulse.Lib.OnRange
#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --fuel 0 --ifuel 2"
let small_vprop_map = PM.pointwise nat (PF.pcm_frac #small_vprop)
let carrier = PM.map nat (PF.fractional small_vprop)
let small_emp : small_vprop = cm_small_vprop.unit
noeq
type barrier_t_core = {
  r: Box.box U32.t;
  ctr : GR.ref nat;
  gref: ghost_pcm_ref small_vprop_map;
}

noeq type barrier_t = {
  core: barrier_t_core;
  i: iref
}

let full_perm : perm = 1.0R

let empty_map_below (n:nat)
: carrier
= Map.map_literal 
  (fun (k:nat) -> 
    if k < n
    then None
    else Some (small_emp, full_perm))


let up2_is_small (p:small_vprop)
  : Lemma (is_small (up2 p))
          [SMTPat (up2 p)]
  = up2_is_small p

let predicate_at (m:carrier) (i:nat)
: boxable
= match Map.sel m i with
  | None ->
    pure False
  | Some f ->
    up2 (fst f)

let all_perms (m:carrier) (i j:nat) (p:perm) =
  forall k. 
    i <= k /\ k < j ==>
    (match Map.sel m k with
     | None -> False
     | Some (_, q) -> p == q)

let map_invariant0 (m:carrier) (n:nat) (p:storable)
= pure (p == OR.on_range (predicate_at m) 0 n /\ all_perms m 0 n 0.5R)

let map_invariant (v:U32.t) (m:carrier) (n:nat) (p:storable)
: boxable
= if v = 0ul
  then map_invariant0 m n p
  else OR.on_range (predicate_at m) 0 n ** pure (all_perms m 0 n 0.5R)

let barrier_inv (b: barrier_t_core) (p:storable)
: boxable
= exists* v n m.
    Box.pts_to b.r #0.5R v **
    GR.pts_to #nat b.ctr n **
    big_ghost_pcm_pts_to b.gref m **
    big_ghost_pcm_pts_to b.gref (empty_map_below n) **
    map_invariant v m n p

let barrier (b: barrier_t) (p:storable)
: vprop
= inv b.i (barrier_inv b.core p)

let send (b: barrier_t) (p:storable)
: vprop
= barrier b p **
  Box.pts_to b.core.r #0.5R 0ul

let singleton (i:nat) (#p:perm) (q:storable)
: carrier
= Map.map_literal 
    (fun (k:nat) ->
        if k = i
        then Some (down2 q, p)
        else None)

let recv (b:barrier_t) (q:storable)
: vprop
= exists* p i.
    barrier b p **
    big_ghost_pcm_pts_to b.core.gref (singleton i #0.5R q)

```pulse
ghost
fn unfold_map_invariant0 v m n p
requires map_invariant v m n p ** pure (v == 0ul)
ensures pure (p == OR.on_range (predicate_at m) 0 n /\ all_perms m 0 n 0.5R)
{
  rewrite each v as 0ul;
  unfold map_invariant;
  unfold map_invariant0;
}
```

```pulse
ghost
fn fold_map_invariant0 m n (p:storable)
requires pure (p == OR.on_range (predicate_at m) 0 n /\ all_perms m 0 n 0.5R)
ensures map_invariant 0ul m n p
{
  fold (map_invariant0 m n p);
  fold (map_invariant 0ul m n p)
}
```

```pulse
ghost
fn fold_map_invariant1 v m n p
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
```

```pulse
ghost
fn unfold_map_invariant1 v m n p
requires map_invariant v m n p ** pure (v =!= 0ul)
ensures
  OR.on_range (predicate_at m) 0 n **
  pure (all_perms m 0 n 0.5R)
{
  rewrite (map_invariant v m n p)
       as (OR.on_range (predicate_at m) 0 n ** pure (all_perms m 0 n 0.5R));
}
```

let comp (c0:carrier) (c1:carrier { PM.composable_maps (PF.pcm_frac #small_vprop) c0 c1 })
: carrier 
= PM.compose_maps (PF.pcm_frac #small_vprop) c0 c1

let initial_map (p:storable)
: c:carrier { small_vprop_map.refine c }
= comp (singleton 0 #1.0R p) (empty_map_below 1)


let on_range_singleton (p:storable)
: Lemma (OR.on_range (predicate_at (singleton 0 #0.5R p)) 0 1 == p)
= let m = (singleton 0 #0.5R p) in
  calc (==) {
    OR.on_range (predicate_at m) 0 1;
  (==) { OR.on_range_eq_cons (predicate_at m) 0 1;
         OR.on_range_eq_emp (predicate_at m) 1 1 }
    predicate_at m 0 ** emp;
  (==) { elim_vprop_equiv (vprop_equiv_unit (predicate_at m 0));
         elim_vprop_equiv (vprop_equiv_comm emp (predicate_at m 0)) }
    predicate_at m 0;
  (==) {}
    up2 (down2 p);
  (==) {}
    p;
  }
  
  
```pulse
ghost
fn intro_init_map_invariant (p:storable)
requires emp
ensures map_invariant 0ul (singleton 0 #0.5R p) 1 p
{
  on_range_singleton p; //inlining the calc does not work
  fold_map_invariant0 (singleton 0 #0.5R p) 1 p;
}
```

```pulse
fn new_barrier (p:storable)
requires emp
returns b:barrier_t
ensures send b p ** recv b p
{
  let r = Box.alloc 0ul;
  let ctr = GR.alloc #nat 1;
  let gref = big_ghost_alloc #_ #small_vprop_map (initial_map p);
  big_ghost_share gref (singleton 0 #1.0R p) (empty_map_below 1);
  assert pure (singleton 0 #1.0R p `Map.equal` comp (singleton 0 #0.5R p) (singleton 0 #0.5R p));
  rewrite each (singleton 0 #1.0R p) 
          as (comp (singleton 0 #0.5R p) (singleton 0 #0.5R p));
  big_ghost_share gref (singleton 0 #0.5R p) (singleton 0 #0.5R p);
  Box.share2 r;
  intro_init_map_invariant p;
  let b = { r; ctr; gref };
  rewrite each r as b.r, gref as b.gref, ctr as b.ctr;
  fold (barrier_inv b p);
  let i = new_invariant (barrier_inv b p);
  let bb = { core = b; i = i };
  rewrite each b as bb.core;
  rewrite each i as bb.i;
  dup_inv _ _;
  fold (barrier bb p);
  fold (send bb p);
  fold (barrier bb p);
  with v. rewrite (big_ghost_pcm_pts_to bb.core.gref v) as
          (big_ghost_pcm_pts_to bb.core.gref (singleton 0 #0.5R p));
  fold (recv bb p);
  bb
}
```


module T = FStar.Tactics

```pulse
ghost
fn flip_map_invariant (v:U32.t) (p:storable) (m:carrier) (n:nat)
requires map_invariant v m n p ** p ** pure (v == 0ul)
ensures map_invariant 1ul m n p
{
  rewrite each v as 0ul;
  rewrite (map_invariant 0ul m n p) as (map_invariant0 m n p);
  unfold map_invariant0;
  rewrite p as OR.on_range (predicate_at m) 0 n;
  rewrite (OR.on_range (predicate_at m) 0 n ** pure (all_perms m 0 n 0.5R))
       as (map_invariant 1ul m n p);
}
```

```pulse
fn signal (b:barrier_t) (#p:storable)
requires send b p ** p
ensures emp
{
  unfold send;
  unfold barrier;
  with_invariants b.i 
  returns u:unit
  ensures inv b.i (barrier_inv b.core p) ** emp
  {
    unfold barrier_inv;
    Box.gather b.core.r;
    write_atomic_box b.core.r 1ul;
    Box.share b.core.r;
    drop_ (Box.pts_to b.core.r #0.5R 1ul);
    flip_map_invariant _ _ _ _;
    fold (barrier_inv b.core p);
  };
  drop_ (inv b.i _)
}
```

let composable (c0:carrier) (c1:carrier)
= PM.composable_maps (PF.pcm_frac #small_vprop) c0 c1

let predicate_at_i_is_q_lemma (m:carrier) (i:nat) (n:nat) (q:storable)
: Lemma
  (requires
    composable (singleton i #0.5R q) m /\
    composable (comp (singleton i #0.5R q) m) (empty_map_below n))
  (ensures
    i < n /\
    (Some? (Map.sel m i) ==> fst (Some?.v (Map.sel m i)) == down2 q))
= if i < n
  then (
    match Map.sel m i with
    | None -> ()
    | Some (qq, pp) -> ()
  )
  else (
    match Map.sel (empty_map_below n) i with
    | None -> ()
    | Some (_, pp) ->
      assert (pp == 1.0R);
      ()
  )

```pulse
ghost
fn elim_on_range_at_i (m:carrier) (i n:nat)
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
```

```pulse
ghost
fn composable_three (gref:ghost_pcm_ref small_vprop_map) (c0 c1 c2:carrier)
requires big_ghost_pcm_pts_to gref c0 ** big_ghost_pcm_pts_to gref c1 ** big_ghost_pcm_pts_to gref c2
ensures  big_ghost_pcm_pts_to gref c0 ** big_ghost_pcm_pts_to gref c1 ** big_ghost_pcm_pts_to gref c2
         ** pure (composable c0 c1 /\ composable (comp c0 c1) c2)
{
  big_ghost_gather gref c0 c1;
  big_ghost_gather gref (comp c0 c1) c2;
  big_ghost_share gref (comp c0 c1) c2;
  big_ghost_share gref c0 c1;
}
```

module T = FStar.Tactics
let norm_tac (_:unit) : T.Tac unit =
    T.mapply (`vprop_equiv_refl)

let elim_predicate_at (m:carrier) (i:nat) 
: Lemma 
  (requires Some? (Map.sel m i))
  (ensures predicate_at m i ==
           up2 (fst (Some?.v (Map.sel m i)))) // ** pure (snd (Some?.v (Map.sel m i)) == 0.5R))
= ()


```pulse
ghost
fn elim_predicate_at_alt (m:carrier) (i:nat) (_:squash (Some? (Map.sel m i)))
requires predicate_at m i
ensures up2 (fst (Some?.v (Map.sel m i)))
{
  rewrite (predicate_at m i) 
      as  (up2 (fst (Some?.v (Map.sel m i))));
}
```

```pulse
ghost
fn predicate_at_i_is_q (#gref:ghost_pcm_ref small_vprop_map) (#v:U32.t) (#m:carrier) (#i #n:nat) (#p #q:storable) ()
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
  q **
  OR.on_range (predicate_at m) (i + 1) n **
  pure (Map.sel m i == Some (down2 q, 0.5R)) **
  pure (i < n /\ all_perms m 0 n 0.5R)
{
  rewrite (map_invariant v m n p) as (OR.on_range (predicate_at m) 0 n ** pure (all_perms m 0 n 0.5R));
  composable_three _ _ _ _;
  predicate_at_i_is_q_lemma m i n q;
  elim_on_range_at_i m i n;
  OR.on_range_get i;
  match Map.sel m i {
    None -> {
      rewrite (predicate_at m i) as pure False;
      unreachable();
    }

    Some f -> {
      elim_predicate_at_alt m i ();
      rewrite (up2 (fst f)) as q;
      ()
    }   
  }
}
```

```pulse
ghost
fn frame_predicate_at (m0:carrier) (i j:nat) (k:nat) (v:_)
requires OR.on_range (predicate_at m0) i j ** 
         pure ((j <= k \/ k < i))
ensures OR.on_range (predicate_at (Map.upd m0 k v)) i j
{
  ghost
  fn aux (kk:nat { i <= kk /\ kk < j})
  requires (predicate_at m0 kk)
  ensures (predicate_at (Map.upd m0 k v) kk)
  {
    rewrite (predicate_at m0 kk)
        as  (predicate_at (Map.upd m0 k v) kk);
  };
  OR.on_range_weaken
    (predicate_at m0)
    (predicate_at (Map.upd m0 k v))
    i j
    aux
}
```

```pulse
ghost
fn predicate_at_singleton (m:carrier) (i:nat) (q:storable)
requires q ** pure (Map.sel m i == Some (down2 q, 0.5R))
ensures predicate_at m i
{
  rewrite q as (predicate_at m i)
}
```

```pulse
ghost
fn clear_i  (#gref:ghost_pcm_ref small_vprop_map) (#m:carrier) (#i #n:nat) (#q:storable) ()
requires
  big_ghost_pcm_pts_to gref (singleton i #0.5R q) **
  big_ghost_pcm_pts_to gref m **
  pure (Map.sel m i == Some (down2 q, 0.5R)) **
  OR.on_range (predicate_at m) 0 i **
  OR.on_range (predicate_at m) (i + 1) n **
  pure (i < n /\ all_perms m 0 n 0.5R)
returns m': erased carrier
ensures
  big_ghost_pcm_pts_to gref m' **
  big_ghost_pcm_pts_to gref (singleton i #0.5R emp) **
  OR.on_range (predicate_at m') 0 n **
  pure (all_perms m' 0 n 0.5R)
{
  big_ghost_gather gref _ _;
  big_ghost_write gref _ _
    (PM.lift_frame_preserving_upd
        _ _
        (PF.mk_frame_preserving_upd (down2 q) (down2 emp))
        (comp (singleton i #0.5R q) m)
        i);
  with m'. assert (big_ghost_pcm_pts_to gref m');
  assert pure (Map.equal m' (comp (singleton i #0.5R emp) (Map.upd m i (Some (down2 emp, 0.5R)))));
  rewrite (big_ghost_pcm_pts_to gref m') as
          (big_ghost_pcm_pts_to gref (comp (singleton i #0.5R emp) (Map.upd m i (Some (down2 emp, 0.5R)))));
  big_ghost_share gref (singleton i #0.5R emp) (Map.upd m i (Some (down2 emp, 0.5R)));
  frame_predicate_at m 0 i i (Some (down2 emp, 0.5R));
  frame_predicate_at m (i + 1) n i (Some (down2 emp, 0.5R));
  predicate_at_singleton (Map.upd m i (Some (down2 emp, 0.5R))) i emp;
  OR.on_range_put 0 i n;
  rewrite (OR.on_range (predicate_at (Map.upd m i (Some (down2 emp, 0.5R)))) 0 n)
      as  OR.on_range (predicate_at (reveal (hide (Map.upd m i (Some (down2 emp, 0.5R))) ))) 0 n;
  hide #carrier (Map.upd m i (Some (down2 emp, 0.5R))) 
}
```

```pulse
ghost
fn fold_barrier_inv (b: barrier_t_core) (p:storable)
                    (v n m:_)
requires
    Box.pts_to b.r #0.5R v **
    GR.pts_to #nat b.ctr n **
    big_ghost_pcm_pts_to b.gref m **
    big_ghost_pcm_pts_to b.gref (empty_map_below n) **
    map_invariant v m n p
ensures
    barrier_inv b p
{
  fold barrier_inv
}
```

```pulse
fn rec wait (b:barrier_t) (q:storable)
requires recv b q
ensures q
{
  unfold recv;
  with p. assert (barrier b p);
  with i. assert (big_ghost_pcm_pts_to b.core.gref (singleton i #0.5R q));
  unfold barrier;
  let res : bool =
    with_invariants b.i
    returns res:bool
    ensures inv b.i (barrier_inv b.core p) **
            (cond res q (big_ghost_pcm_pts_to b.core.gref (singleton i #0.5R q)))
    {
      unfold barrier_inv;
      with _v m n. assert (map_invariant _v m n p);
      let v = read_atomic_box b.core.r;
      if (v = 0ul)
      {
        intro_cond_false
          q
          (big_ghost_pcm_pts_to b.core.gref (singleton i #0.5R q));
        fold (barrier_inv b.core p);
        false;
      }
      else
      {
        predicate_at_i_is_q ();
        let m' = clear_i ();
        intro_cond_true q (big_ghost_pcm_pts_to b.core.gref (singleton i #0.5R q));
        rewrite (OR.on_range (predicate_at m') 0 n ** pure (all_perms m' 0 n 0.5R))
            as  (map_invariant _v m' n p);
        fold_barrier_inv _ _ _ _ m';
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
    fold (barrier b p);
    fold (recv b q);
    wait b q;
  }
}
```

let split_aux_post (b:barrier_t) (q r:storable)
: vprop
= exists* j k.
    big_ghost_pcm_pts_to b.core.gref (singleton j #0.5R q) **
    big_ghost_pcm_pts_to b.core.gref (singleton k #0.5R r)



```pulse
ghost
fn map_invariant_all_perms v m n p
requires map_invariant v m n p
ensures  map_invariant v m n p ** pure (all_perms m 0 n 0.5R)
{
  if (v = 0ul)
  {
     unfold_map_invariant0 _ _ _ _;
     fold_map_invariant0 m n p;
     rewrite each 0ul as v;
  }
  else {
    unfold_map_invariant1 _ _ _ _;
    fold_map_invariant1 v m n p;
  }
}
```

```pulse
ghost
fn q_at_i (#gref:ghost_pcm_ref small_vprop_map) (#v:U32.t) (#m:carrier) (#i #n:nat) (#p #q:storable) ()
requires
  big_ghost_pcm_pts_to gref (singleton i #0.5R q) **
  big_ghost_pcm_pts_to gref m **
  big_ghost_pcm_pts_to gref (empty_map_below n) **
  map_invariant v m n p
ensures
  big_ghost_pcm_pts_to gref (singleton i #0.5R q) **
  big_ghost_pcm_pts_to gref m **
  big_ghost_pcm_pts_to gref (empty_map_below n) **
  map_invariant v m n p **
  pure (Map.sel m i == Some (down2 q, 0.5R) /\
        i < n /\
        all_perms m 0 n 0.5R /\
        (forall j. n <= j ==> Map.sel m j == None))
{
  map_invariant_all_perms v m n p;
  composable_three _ _ _ _;
  predicate_at_i_is_q_lemma m i n q;
  ()
}
```


```pulse
ghost
fn upd_i  (#gref:ghost_pcm_ref small_vprop_map) (#m:carrier) (#i:nat) (#q:storable) ()
requires
  big_ghost_pcm_pts_to gref (singleton i #0.5R q) **
  big_ghost_pcm_pts_to gref m **
  pure (Map.sel m i == Some (down2 q, 0.5R))
returns m': erased carrier
ensures
  big_ghost_pcm_pts_to gref m' **
  // big_ghost_pcm_pts_to gref (singleton i #0.5R emp) **
  pure (m' == Map.upd m i (Some (down2 emp, 0.5R)))
{
  big_ghost_gather gref _ _;
  big_ghost_write gref _ _
    (PM.lift_frame_preserving_upd
        _ _
        (PF.mk_frame_preserving_upd (down2 q) (down2 emp))
        (comp (singleton i #0.5R q) m)
        i);
  with m'. assert (big_ghost_pcm_pts_to gref m');
  assert pure (Map.equal m' (comp (singleton i #0.5R emp) (Map.upd m i (Some (down2 emp, 0.5R)))));
  rewrite (big_ghost_pcm_pts_to gref m') as
          (big_ghost_pcm_pts_to gref (comp (singleton i #0.5R emp) (Map.upd m i (Some (down2 emp, 0.5R)))));
  big_ghost_share gref (singleton i #0.5R emp) (Map.upd m i (Some (down2 emp, 0.5R)));
  drop_ (big_ghost_pcm_pts_to gref (singleton i #0.5R emp));
  hide #carrier (Map.upd m i (Some (down2 emp, 0.5R))) 
}
```

```pulse
ghost
fn alloc (#b:barrier_t_core) (#n:nat) (q:storable)
requires big_ghost_pcm_pts_to b.gref (empty_map_below n) **
         GR.pts_to b.ctr n
ensures  GR.pts_to b.ctr (n + 1) **
         big_ghost_pcm_pts_to b.gref (empty_map_below (n + 1)) **
         big_ghost_pcm_pts_to b.gref (singleton n #0.5R q) **
         big_ghost_pcm_pts_to b.gref (singleton n #0.5R q)
{
  GR.write b.ctr (n + 1);
  down2_emp();
  assert pure (Map.equal (empty_map_below n) (comp (singleton n #1.0R emp) (empty_map_below (n + 1))));
  rewrite (big_ghost_pcm_pts_to b.gref (empty_map_below n))
  as      (big_ghost_pcm_pts_to b.gref (comp (singleton n #1.0R emp) (empty_map_below (n + 1))));
  big_ghost_share b.gref (singleton n #1.0R emp) (empty_map_below (n + 1));
  big_ghost_write b.gref _ _
   (PM.lift_frame_preserving_upd
        _ _
        (PF.mk_frame_preserving_upd (down2 emp) (down2 q))
        (singleton n #1.0R emp)
        n);
  with m. assert (big_ghost_pcm_pts_to b.gref m);
  assert pure (Map.equal m
                         (comp (singleton n #0.5R q) (singleton n #0.5R q)));
  rewrite (big_ghost_pcm_pts_to b.gref m)
  as      (big_ghost_pcm_pts_to b.gref (comp (singleton n #0.5R q) (singleton n #0.5R q)));
  big_ghost_share b.gref (singleton n #0.5R q) (singleton n #0.5R q);
}
```

let up_i (m:carrier) (i:nat) (p:storable) = Map.upd m i (Some (down2 p, 0.5R))
let split_map (m:carrier) (i n:nat) (q r:storable) = (up_i (up_i (up_i m i emp) n q) (n + 1) r)

assume
val on_range_eq_get (p:nat -> vprop) (i j k:nat)
: Lemma 
  (requires i <= j /\ j < k)
  (ensures OR.on_range p i k == (OR.on_range p i j ** p j ** OR.on_range p (j + 1) k))

assume
val on_range_eq_snoc (p:nat -> vprop) (i j:nat)
: Lemma 
  (ensures OR.on_range p i (j + 1) == OR.on_range p i j ** p j)

assume
val on_range_frame (p q:nat -> vprop) (i j:nat)
: Lemma 
  (requires forall k. i <= k /\ k < j ==> p k == q k)
  (ensures OR.on_range p i j == OR.on_range q i j)

let star_assoc (p q r:vprop)
: Lemma (p ** (q ** r) == (p ** q) ** r)
= elim_vprop_equiv (vprop_equiv_assoc p q r)
let star_comm (p q:vprop)
: Lemma (p ** q == q ** p)
= elim_vprop_equiv (vprop_equiv_comm p q)
let emp_unit (p:vprop)
: Lemma (emp ** p == p)
= elim_vprop_equiv (vprop_equiv_unit p)

let split_lemma (b:barrier_t_core) (m:carrier) (q r:storable) (i n:nat)
: Lemma
(requires i < n /\ Map.sel m i == Some (down2 (q ** r), 0.5R))
(ensures OR.on_range (predicate_at m) 0 n ==
         OR.on_range (predicate_at (split_map m i n q r)) 0 (n + 2))
= let m' = (split_map m i n q r) in
  calc (==) {
    OR.on_range (predicate_at m) 0 n;
  (==) { on_range_eq_get (predicate_at m) 0 i n }
    OR.on_range (predicate_at m) 0 i **
    up2 (down2 (q ** r)) **
    OR.on_range (predicate_at m) (i + 1) n;
  (==) { down2_star q r; up2_star (down2 q) (down2 r) }
    OR.on_range (predicate_at m) 0 i **
    (q ** r) **
    OR.on_range (predicate_at m) (i + 1) n;
  (==) { 
         FStar.Classical.(
          forall_intro_3 star_assoc;
          forall_intro_2 star_comm;
          forall_intro emp_unit 
         )
       }
   (OR.on_range (predicate_at m) 0 i **
    emp **
    OR.on_range (predicate_at m) (i + 1) n) **
    q ** r;
  (==){
        on_range_frame (predicate_at m) (predicate_at m') 0 i;
        on_range_frame (predicate_at m) (predicate_at m') (i + 1) n
      }
    (OR.on_range (predicate_at m') 0 i **
    emp ** 
    OR.on_range (predicate_at m') (i + 1) n) ** q ** r;
  (==) { on_range_eq_get (predicate_at m') 0 i n }
    (OR.on_range (predicate_at m') 0 n ** q) ** r;
  (==) { on_range_eq_snoc (predicate_at m') 0 n }
    OR.on_range (predicate_at m') 0 (n + 1) ** r;
  (==) { on_range_eq_snoc (predicate_at m') 0 (n + 1) }
    OR.on_range (predicate_at m') 0 (n + 2);
  }

```pulse
ghost
fn split_aux (b:barrier_t) (p:erased storable) (q r:storable) (i:erased nat)
requires barrier_inv b.core p **
         big_ghost_pcm_pts_to b.core.gref (singleton i #0.5R (q ** r))
ensures  barrier_inv b.core p ** split_aux_post b q r
{
  unfold barrier_inv;
  q_at_i ();
  let m' = upd_i ();
  with v m n. assert (map_invariant v m n p);
  alloc q;
  alloc r;
  big_ghost_gather b.core.gref m' (singleton n #0.5R q);
  big_ghost_gather b.core.gref (comp m' (singleton n #0.5R q)) (singleton (n + 1) #0.5R r);
  assert (pure (Map.equal (comp (comp m' (singleton n #0.5R q)) (singleton (n + 1) #0.5R r))
                          (split_map m i n q r)));
  rewrite (big_ghost_pcm_pts_to b.core.gref (comp (comp m' (singleton n #0.5R q)) (singleton (n + 1) #0.5R r)))
       as (big_ghost_pcm_pts_to b.core.gref (split_map m i n q r));
  fold (split_aux_post b q r);
  split_lemma b.core m q r i n;
  let vv = reveal v;
  if (vv = 0ul)
  {
    rewrite (map_invariant v m n p) as (map_invariant0 m n p);
    unfold map_invariant0;
    fold (map_invariant0 (split_map m i n q r) (n + 2) p);
    fold (map_invariant 0ul (split_map m i n q r) (n + 2) p);
    fold_barrier_inv b.core p 0ul (n + 2) (split_map m i n q r);
  }
  else
  {
    unfold_map_invariant1 _ _ _ _;
    rewrite (OR.on_range (predicate_at m) 0 n)
    as      (OR.on_range (predicate_at (split_map m i n q r)) 0 (n + 2));
    fold_map_invariant1 v (split_map m i n q r) (n + 2) p;
    fold_barrier_inv b.core p v (n + 2) (split_map m i n q r);
  }
 
}
```

```pulse
ghost
fn split (b:barrier_t) (q r:storable)
requires recv b (q ** r)
ensures recv b q ** recv b r
opens (add_inv emp_inames b.i)
{
  unfold recv;
  with i. assert (big_ghost_pcm_pts_to b.core.gref (singleton i #0.5R (q ** r)));
  with p. assert (barrier b p);
  unfold barrier;
  with_invariants b.i
  returns u:unit
  ensures inv b.i (barrier_inv b.core (reveal p)) **
         (exists* j k.
            big_ghost_pcm_pts_to b.core.gref (singleton j #0.5R q) **
            big_ghost_pcm_pts_to b.core.gref (singleton k #0.5R r))
  {
    split_aux b p q r i;
    unfold split_aux_post;
  };
  dup_inv _ _;
  fold (barrier b p);
  fold (recv b q);
  fold (barrier b p);
  fold (recv b r)
}
```
