module Pulse.Lib.ArraySwap
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
module Prf = Steel.ST.GenArraySwap.Proof
module SZ = FStar.SizeT
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --fuel 2 --ifuel 1"
#restart-solver

```pulse
fn gcd (n0: SZ.t) (l0: SZ.t)
  requires (emp ** pure (
    SZ.v l0 < SZ.v n0
  ))
  returns res : SZ.t
  ensures (emp ** pure (
    SZ.v l0 < SZ.v n0 /\
    SZ.v res == (Prf.mk_bezout (SZ.v n0) (SZ.v l0)).d  
  ))
{
  let mut pn = n0;
  let mut pl = l0;
  while (let l = !pl ; (l `SZ.gt` 0sz))
  invariant b . exists n l . (
    pts_to pn n **
    pts_to pl l **
    pure (
      SZ.v l < SZ.v n /\
      (Prf.mk_bezout (SZ.v n0) (SZ.v l0)).d == (Prf.mk_bezout (SZ.v n) (SZ.v l)).d /\
      b == (SZ.v l > 0)
    ))
  {
    let n = !pn;
    let l = !pl;
    let l' = SZ.rem n l;
    pn := l;
    pl := l';
    ()
  };
  let res = !pn;
  res
}
```

inline_for_extraction
let impl_jump
  (lb rb mb: SZ.t)
  (idx: SZ.t)
  (_: squash (
      SZ.v lb < SZ.v mb /\
      SZ.v mb < SZ.v rb /\
      SZ.v lb <= SZ.v idx /\
      SZ.v idx < SZ.v rb
  ))
: Tot (idx': SZ.t {
      SZ.v idx' == SZ.v lb + Prf.jump (SZ.v rb - SZ.v lb) (SZ.v mb - SZ.v lb) (SZ.v idx - SZ.v lb)
  })
= Prf.jump_if (SZ.v rb - SZ.v lb) (SZ.v mb - SZ.v lb) () (SZ.v idx - SZ.v lb);
  [@@inline_let]
  let nl = rb `SZ.sub` mb in
  if (idx `SZ.sub` lb) `SZ.gte` nl
  then idx `SZ.sub` nl
  else idx `SZ.add` (mb `SZ.sub` lb)

inline_for_extraction
let size_add
  (a: SZ.t)
  (b: SZ.t)
  (_: squash (SZ.fits (SZ.v a + SZ.v b)))
: Tot (c: SZ.t {
    SZ.v c == SZ.v a + SZ.v b
  })
= a `SZ.add` b

inline_for_extraction
let size_lt
  (a: SZ.t)
  (b: SZ.t)
: Tot (c: bool { c == (SZ.v a < SZ.v b) })
= a `SZ.lt` b

inline_for_extraction
let size_sub
  (a: SZ.t)
  (b: SZ.t)
  (_: squash (SZ.v a >= SZ.v b))
: Tot (c: SZ.t { SZ.v c == (SZ.v a - SZ.v b) })
= a `SZ.sub` b

(*
```pulse
fn get_array_pts_to (#t: Type0) (#p: perm) (#s: Ghost.erased (Seq.seq t)) (a: A.array t)
  requires (A.pts_to a p s)
  returns s': Ghost.erased (Seq.seq t)
  ensures (A.pts_to a p s ** pure (s' == s))
  {
    s
  }
```
*)

(*
assume val get_array_pts_to (#opened: _) (#t: Type0) (#p: perm) (#s: Seq.seq t) (a: A.array t)
: stt_ghost (Ghost.erased (Seq.seq t)) opened
    (A.pts_to a p s)
    (fun s' -> A.pts_to a p s ** pure (Ghost.reveal s' == s))
*)

(*
assume val get_array_pts_to (#t: Type0) (#p: perm) (#s: Ghost.erased (Seq.seq t)) (a: A.array t)
: stt (Ghost.erased (Seq.seq t))
    (A.pts_to a p s)
    (fun s' -> A.pts_to a p s ** pure (s' == s))
*)

```pulse
fn get_array_pts_to (#t: Type0) (a: A.array t) (#p: perm) (#s: Ghost.erased (Seq.seq t))
  requires A.pts_to a #p s
  returns s': Ghost.erased (Seq.seq t)
  ensures A.pts_to a #p s ** pure (s' == s)
  {
    s
  }
```

```pulse
fn get_pts_to (#t: Type0) (a: ref t) (#p: perm) (#s: erased (t))
  requires pts_to a #p s
  returns s': Ghost.erased (t)
  ensures pts_to a #p s ** pure (s' == s)
  {
    s
  }
```

```pulse
fn pulse_assert (p: prop)
  requires (pure p)
  returns res: squash p
  ensures emp
  {
    ()
  }
```

#restart-solver

#push-options "--z3rlimit_factor 4"

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn array_swap'(#t: Type0) (#s0: Ghost.erased (Seq.seq t)) (a: A.array t) (lb: SZ.t) (rb: SZ.t) (mb: (mb: SZ.t {SZ.v mb > SZ.v lb /\ SZ.v mb < SZ.v rb})) (bz: Prf.bezout (SZ.v rb - SZ.v lb) (SZ.v mb - SZ.v lb)) (d: SZ.t) (q: SZ.t)
  requires (
    A.pts_to_range a (Ghost.reveal (SZ.v lb)) (Ghost.reveal (SZ.v rb)) s0 **
    pure (
      Seq.length s0 == SZ.v rb - SZ.v lb /\
      SZ.v d == bz.d /\
      SZ.v q == bz.q_n
    )
  )
  ensures exists s . (
    A.pts_to_range a (Ghost.reveal (SZ.v lb)) (Ghost.reveal (SZ.v rb)) s **
    pure (Prf.array_swap_post s0 (SZ.v rb - SZ.v lb) (SZ.v mb - SZ.v lb) s) // hoisted out because of the SMT pattern on array_as_ring_buffer_swap
  )
{   
    let mut pi = lb;
    while (let i = !pi; ((i `SZ.sub` lb) `size_lt` d))
    invariant b . exists s i . (
      A.pts_to_range a (Ghost.reveal (SZ.v lb)) (Ghost.reveal (SZ.v rb)) s **
      R.pts_to pi i **
      pure (
        SZ.v i >= SZ.v lb /\
        SZ.v i < SZ.v rb /\
        Prf.array_swap_outer_invariant s0 (SZ.v rb - SZ.v lb) (SZ.v mb - SZ.v lb) bz s (SZ.v i - SZ.v lb) /\
        b == (SZ.v i - SZ.v lb < bz.d)
    )) {
      let i = !pi;
      let save = A.pts_to_range_index a i;
      let mut pj = 0sz;
      let mut pidx = i;
      while (let j = !pj; (j `size_lt` (size_sub q 1sz ())))
      invariant b . exists s j idx . (
        A.pts_to_range a (Ghost.reveal (SZ.v lb)) (Ghost.reveal (SZ.v rb)) s **
        R.pts_to pi i **
        R.pts_to pj j **
        R.pts_to pidx idx **
        pure (
          SZ.v idx >= SZ.v lb /\
          SZ.v idx < SZ.v rb /\
          Prf.array_swap_inner_invariant s0 (SZ.v rb - SZ.v lb) (SZ.v mb - SZ.v lb) bz s (SZ.v i - SZ.v lb) (SZ.v j) (SZ.v idx - SZ.v lb) /\
          b == (SZ.v j < bz.q_n - 1)
        )
      ) {
        let j = !pj;
        let idx = !pidx;
        let idx' = impl_jump lb rb mb idx ();
        let x = A.pts_to_range_index a idx';
        let j' = size_add j 1sz ();
        A.pts_to_range_upd a idx x;
        pj := j';
        pidx := idx';
        ()
      };
      ();
      let idx = !pidx;
      A.pts_to_range_upd a idx save;
      let i' = size_add i 1sz ();
      pi := i';
      ()
    };
    ()
}
```
