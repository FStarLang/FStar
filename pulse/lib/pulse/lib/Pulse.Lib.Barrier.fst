module Pulse.Lib.Barrier
open Pulse.Lib.Pervasives
module CM = FStar.Algebra.CommMonoid
module M = Pulse.Lib.PCM.MonoidShares
module U32 = FStar.UInt32

assume
val small_star (p q:small_vprop) : small_vprop
assume
val small_emp : small_vprop
let up2_small_emp : squash (up2 small_emp == emp) = admit()
let small_emp_unit (x:small_vprop)
: Lemma (small_star small_emp x == x)
        [SMTPat (small_star small_emp x == x)]
= admit()
let small_star_assoc (x y z:small_vprop)
: Lemma (small_star x (small_star y z) == small_star (small_star x y) z)
= admit()
let small_star_comm (x y:small_vprop)
: Lemma (small_star x y == small_star y x)
        [SMTPat (small_star x y)]
= admit()
let small_vprop_cm
: CM.cm small_vprop
= CM.CM small_emp small_star
    small_emp_unit
    small_star_assoc
    small_star_comm

let storable = p:vprop { is_small p }

noeq
type barrier_t_core = {
  r: Box.box U32.t;
  gref: core_ghost_pcm_ref;
}

noeq type barrier_t = {
  core: barrier_t_core;
  i: iref
}

let pcm_of (p:storable) = M.pcm_of small_vprop_cm (down2 p)

let barrier_inv (b: barrier_t_core) (p:storable)
: vprop
= exists* v r q.
    Box.pts_to b.r #0.5R v **
    big_ghost_pcm_pts_to #_ #(pcm_of p) b.gref q **
    up2 r **
    pure(
     if v = 0ul
     then q == small_emp /\ r == small_emp
     else down2 p == small_star q r
    )

let barrier_inv_i_big (b:barrier_t_core) (p:storable)
: Lemma (is_big (barrier_inv b p))
        [SMTPat (is_big (barrier_inv b p))]
= admit()

let barrier (b: barrier_t) (p:storable)
: vprop
= inv b.i (barrier_inv b.core p)

let send (b: barrier_t) (p:storable)
: vprop
= barrier b p **
  Box.pts_to b.core.r #0.5R 0ul

let recv (b:barrier_t) (p q:storable)
: vprop
= barrier b p **
  big_ghost_pcm_pts_to #_ #(pcm_of p) b.core.gref (down2 q)


```pulse
fn new_barrier (p:storable)
requires emp
returns b:barrier_t
ensures send b p ** recv b p p
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
  fold (recv bb p p);
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
#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --fuel 0 --ifuel 2"
assume
val big_ghost_read_simple
    (#a:Type)
    (#p:FStar.PCM.pcm a)
    (r:ghost_pcm_ref p)
    (#x:erased a)
: stt_ghost (erased (v:a{FStar.PCM.compatible p x v /\ p.refine v}))
    emp_inames
    (big_ghost_pcm_pts_to r x)
    (fun v -> big_ghost_pcm_pts_to r x)

```pulse
ghost
fn extract_frame (p:storable) (claim:storable) (q:small_vprop)
requires pure (FStar.PCM.compatible (pcm_of p) (small_star (down2 claim) q) (down2 p))
returns frame:erased small_vprop
ensures pure (q `small_star` (frame `small_star` down2 claim) == down2 p /\
              (down2 claim `small_star` q) `small_star` frame == down2 p)
{
  admit()
}
```

let small_star_inj (p q r0 r1:small_vprop)
: Lemma 
  (p == q `small_star` r0 /\
   p == q `small_star` r1 ==> r0 == r1)
= admit()

let up2_small_star (p q:small_vprop)
: Lemma (up2 (p `small_star` q) == (up2 p ** up2 q))
= admit()

```pulse
fn rec wait (b:barrier_t) (p claim:storable)
requires recv b p claim
ensures claim
{
  unfold recv;
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
        let frame = extract_frame p claim q;
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
    fold (recv b p claim);
    wait b p claim;
  }
}
```

```pulse
fn split (b:barrier_t) (q r s:storable)
requires recv b 'p q ** pure (q == r ** s)
ensures recv b 'p r ** recv b 'p s
{
  admit()
}
```