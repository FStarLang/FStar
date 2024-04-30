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

let on_range_is_big (p: nat -> boxable) (i j:nat)
: Lemma (is_big (OR.on_range p i j))
        [SMTPat (is_big (OR.on_range p i j))]
= admit()

let all_perms (m:carrier) (i j:nat) (p:perm) =
  forall k. 
    i <= k /\ k < j ==>
    (match Map.sel m k with
     | None -> False
     | Some (_, q) -> p == q)

let map_invariant (v:U32.t) (m:carrier) (n:nat) (p:storable)
: boxable
= if v = 0ul
  then pure (p == OR.on_range (predicate_at m) 0 n /\ all_perms m 0 n 0.5R)
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

let comp (c0:carrier) (c1:carrier { PM.composable_maps (PF.pcm_frac #small_vprop) c0 c1 })
: carrier 
= PM.compose_maps (PF.pcm_frac #small_vprop) c0 c1

let initial_map (p:storable)
: c:carrier { small_vprop_map.refine c }
= comp (singleton 0 #1.0R p) (empty_map_below 1)

assume
val on_range_eq_emp (p:nat -> vprop) (i j:nat)
: Lemma 
  (requires i >= j)
  (ensures OR.on_range p i j == emp)

assume
val on_range_eq_cons (p:nat -> vprop) (i j:nat)
: Lemma 
  (requires i < j)
  (ensures OR.on_range p i j == (p i ** OR.on_range p (i + 1) j))

let on_range_singleton (p:storable)
: Lemma (OR.on_range (predicate_at (singleton 0 #0.5R p)) 0 1 == p)
= let m = (singleton 0 #0.5R p) in
  calc (==) {
    OR.on_range (predicate_at m) 0 1;
  (==) { on_range_eq_cons (predicate_at m) 0 1;
        on_range_eq_emp (predicate_at m) 1 1 }
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
  rewrite pure (p == OR.on_range (predicate_at (singleton 0 #0.5R p)) 0 1 /\ all_perms (singleton 0 #0.5R p) 0 1 0.5R)
     as  map_invariant 0ul (singleton 0 #0.5R p) 1 p;
}
```


#push-options "--print_implicits"
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

let unfold_map_invariant_0  (v:U32.t) (p:storable) (m:carrier) (n:nat)
: Lemma
  (requires v == 0ul)
  (ensures map_invariant v m n p == pure (p == OR.on_range (predicate_at m) 0 n /\ all_perms m 0 n 0.5R))
= ()

module T = FStar.Tactics
let apply_map_invariant_0_tac () = 
  T.mapply (`vprop_equiv_ext);
  // T.mapply (`unfold_map_invariant_0)
  T.tadmit()

```pulse
ghost
fn flip_map_invariant (v:U32.t) (p:storable) (m:carrier) (n:nat)
requires map_invariant v m n p ** p ** pure (v == 0ul)
ensures map_invariant 1ul m n p
{
  unfold_map_invariant_0 v p m n;
  rewrite each v as 0ul;
  rewrite_by (map_invariant 0ul m n p)
             (pure (p == OR.on_range (predicate_at m) 0 n /\ all_perms m 0 n 0.5R))
             (apply_map_invariant_0_tac) ();
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
#pop-options

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

let apply_equiv (_:unit) : T.Tac unit = 
  T.dump "A";
  T.mapply (`vprop_equiv_ext);
  T.dump "B";
  T.tadmit()
  // T.mapply (`elim_predicate_at)

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
//        fold (map_invariant _v m' n p);
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

let small_star = cm_small_vprop.mult
let small_emp : small_vprop = cm_small_vprop.unit
let small_emp_unit (x:small_vprop)
: Lemma (small_star small_emp x == x)
        [SMTPat (small_star small_emp x == x)]
= cm_small_vprop.identity x
let small_star_assoc (x y z:small_vprop)
: Lemma (small_star x (small_star y z) == small_star (small_star x y) z)
= cm_small_vprop.associativity x y z
let small_star_comm (x y:small_vprop)
: Lemma (small_star x y == small_star y x)
        [SMTPat (small_star x y)]
= cm_small_vprop.commutativity x y

let up2_small_emp : squash (up2 small_emp == emp) = up2_emp()

let down2_star (p q:storable)
: Lemma (down2 (p ** q) == down2 p `small_star` down2 q)
= down2_star p q

let small_star_inj (p q r0 r1:small_vprop)
: Lemma 
  (p == q `small_star` r0 /\
   p == q `small_star` r1 ==> r0 == r1)
= admit() //!! not true !!!

let up2_is_small (p:small_vprop)
  : Lemma (is_small (up2 p))
          [SMTPat (up2 p)]
  = up2_is_small p

let up2_small_star (p q:small_vprop)
: Lemma (up2 (p `small_star` q) == (up2 p ** up2 q))
= up2_star p q

noeq
type barrier_t_core = {
  r: Box.box U32.t;
  gref: core_ghost_pcm_ref;
}

noeq type barrier_t = {
  core: barrier_t_core;
  i: iref
}

let pcm_of (p:storable) = M.pcm_of cm_small_vprop (down2 p)

let barrier_inv (b: barrier_t_core) (p:storable)
: w:vprop { is_big w }
= exists* v r q.
    Box.pts_to b.r #0.5R v **
    big_ghost_pcm_pts_to #_ #(pcm_of p) b.gref q **
    up2 r **
    pure(
     if v = 0ul
     then q == small_emp /\ r == small_emp
     else down2 p == small_star q r
    )

let barrier (b: barrier_t) (p:storable)
: vprop
= inv b.i (barrier_inv b.core p)

let send (b: barrier_t) (p:storable)
: vprop
= barrier b p **
  Box.pts_to b.core.r #0.5R 0ul

let recv (b:barrier_t) (q:storable)
: vprop
= exists* p.
    barrier b p **
    big_ghost_pcm_pts_to #_ #(pcm_of p) b.core.gref (down2 q)


```pulse
fn new_barrier (p:storable)
requires emp
returns b:barrier_t
ensures send b p ** recv b p
{
  let r = Box.alloc 0ul;
  let gref = big_ghost_alloc #_ #(pcm_of p) (down2 p);
  let b = { r = r; gref = gref };
  rewrite each r as b.r, gref as b.gref;
  small_emp_unit (down2 p);
  big_ghost_share #_ #(pcm_of p) b.gref small_emp (down2 p);
  Box.share b.r;
  rewrite emp as (up2 small_emp);
  fold (barrier_inv b p);
  let i = new_invariant (barrier_inv b p);
  dup_inv _ _;
  let bb = { core = b; i = i };
  rewrite each b as bb.core;
  rewrite each i as bb.i;
  fold (barrier bb p);
  fold (send bb p);
  fold (barrier bb p);
  fold (recv bb p);
  bb
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
    with r. rewrite (up2 r) as emp;
    with q. assert (big_ghost_pcm_pts_to #_ #(pcm_of p) b.core.gref q);
    assert pure (q == small_emp);
    write_atomic_box b.core.r 1ul;
    Box.share b.core.r;
    drop_ (Box.pts_to b.core.r #0.5R 1ul);
    rewrite p as (up2 (down2 p));
    small_emp_unit (down2 p);
    assert pure (down2 p == small_star q (down2 p));
    fold (barrier_inv b.core p);
  };
  drop_ (inv b.i _)
}
```

let pcm_refine (#p:storable) (x:small_vprop)
  : Lemma ((pcm_of p).refine x ==> x == down2 p)
  = ()

let extract_frame 
      (p:storable) (claim:storable) (q:small_vprop)
      (_:squash (FStar.PCM.compatible (pcm_of p) (small_star (down2 claim) q) (down2 p)))
: Tot 
  (frame:small_vprop {
    q `small_star` (frame `small_star` down2 claim) == down2 p /\
    (down2 claim `small_star` q) `small_star` frame == down2 p
  })
= let open FStar.PCM in
  let frame = FStar.IndefiniteDescription.indefinite_description_tot _
    (fun frame -> 
      composable (pcm_of p)
                 (small_star (down2 claim) q) frame /\
      small_star frame (small_star (down2 claim) q) == (down2 p)) in
  FStar.Classical.forall_intro_3 small_star_assoc;
  frame

```pulse
fn rec wait_alt (b:barrier_t) (p claim:storable)
requires barrier b p **
         big_ghost_pcm_pts_to #_ #(pcm_of p) b.core.gref (down2 claim)
ensures claim
{
  unfold barrier;
  let res : bool =
    with_invariants b.i
    returns res:bool
    ensures inv b.i (barrier_inv b.core p) **
            (cond res claim (big_ghost_pcm_pts_to #_ #(pcm_of p) b.core.gref (down2 claim)))
    {
      unfold barrier_inv;
      let v = read_atomic_box b.core.r;
      if (v = 0ul)
      {
        intro_cond_false
          claim
          (big_ghost_pcm_pts_to #_ #(pcm_of p) b.core.gref (down2 claim));
        fold (barrier_inv b.core p);
        false;
      }
      else 
      {
        with r. assert (up2 r);
        big_ghost_gather #_ #(pcm_of p) b.core.gref _ _;
        with q. assert (big_ghost_pcm_pts_to #_ #(pcm_of p) b.core.gref (small_star (down2 claim) q));
        assert pure (down2 p == small_star r q);
        let x = big_ghost_read_simple #_ #(pcm_of p) b.core.gref;
        pcm_refine #p x;
        assert pure (x == down2 p);
        assert pure (FStar.PCM.compatible (pcm_of p) (small_star (down2 claim) q) (down2 p));
        let frame = extract_frame p claim q ();
        //p == q ** r
        //p == q ** (frame ** claim)
        small_star_inj (down2 p) q (small_star frame (down2 claim)) r;
        rewrite (up2 r) as (up2 (small_star frame (down2 claim)));
        up2_small_star frame (down2 claim);
        rewrite (up2 (small_star frame (down2 claim))) as
                (up2 frame ** claim);
        intro_cond_true
            claim
            (big_ghost_pcm_pts_to #_ #(pcm_of p) b.core.gref (down2 claim));
        fold (barrier_inv b.core p);
        true
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
    wait_alt b p claim;
  }
}
```

```pulse
fn wait (b:barrier_t) (claim:storable)
requires recv b claim
ensures claim
{
  unfold recv;
  wait_alt b _ claim
}
```

```pulse
ghost
fn dup_barrier (b:barrier_t) (#p:storable)
requires barrier b p
ensures barrier b p ** barrier b p
{
  unfold barrier;
  dup_inv _ _;
  fold (barrier b p);
  fold (barrier b p);
}
```

```pulse
ghost
fn split (b:barrier_t) (#q r s:storable)
requires recv b q ** pure (q == r ** s)
ensures recv b r ** recv b s
{
  unfold recv;
  with p. assert (barrier b p);
  rewrite each q as (r ** s);
  down2_star r s;
  rewrite each (down2 (r ** s)) as (down2 r `small_star` down2 s);
  big_ghost_share #_ #(pcm_of p) b.core.gref (down2 r) (down2 s);
  dup_barrier b;
  fold (recv b r);
  fold (recv b s)
}
```