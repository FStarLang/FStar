module Pulse.Lib.Barrier
open Pulse.Lib.Pervasives
module CM = FStar.Algebra.CommMonoid
module M = Pulse.Lib.PCM.MonoidShares
module U32 = FStar.UInt32
#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --fuel 0 --ifuel 2"

let identity_frame_compatible
      #a (p:FStar.PCM.pcm a)
      (x:a)
      (v:a{FStar.PCM.compatible p x v})
: y:a { FStar.PCM.compatible p y v /\ FStar.PCM.frame_compatible p x v y }
= x

let big_ghost_read_simple
    (#a:Type)
    (#p:FStar.PCM.pcm a)
    (r:ghost_pcm_ref p)
    (#x:erased a)
: stt_ghost (erased (v:a{FStar.PCM.compatible p x v /\ p.refine v}))
    emp_inames
    (big_ghost_pcm_pts_to r x)
    (fun v -> big_ghost_pcm_pts_to r x)
= big_ghost_read #a #p r x (identity_frame_compatible p x)


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