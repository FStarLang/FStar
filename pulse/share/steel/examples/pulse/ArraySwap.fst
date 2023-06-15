module ArraySwap
module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util 
open Steel.FractionalPermission
module U32 = FStar.UInt32
open Pulse.Steel.Wrapper
module A = Steel.ST.Array
module R = Steel.ST.Reference
module Prf = Steel.ST.GenArraySwap.Proof
module SZ = FStar.SizeT

#set-options "--ide_id_info_off"

#restart-solver

```pulse
fn gcd (n0: SZ.t) (l0: SZ.t)
  requires (emp `star` pure (
    SZ.v l0 < SZ.v n0
  ))
  returns res : SZ.t
  ensures (emp `star` pure (
    SZ.v l0 < SZ.v n0 /\
    SZ.v res == (Prf.mk_bezout (SZ.v n0) (SZ.v l0)).d  
  ))
{
  let mut pn = n0;
  let mut pl = l0;
  while (let l = !pl ; (l `SZ.gt` 0sz))
  invariant b . exists n l . (
    R.pts_to pn full_perm n `star`
    R.pts_to pl full_perm l `star`
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
  (n: SZ.t)
  (l: SZ.t)
  (idx: SZ.t)
: Pure SZ.t
    (requires (
      SZ.v l < SZ.v n /\
      SZ.v idx < SZ.v n
    ))
    (ensures (fun idx' ->
      SZ.v idx' == Prf.jump (SZ.v n) (SZ.v l) (SZ.v idx)
    ))
= Prf.jump_if (SZ.v n) (SZ.v l) () (SZ.v idx);
  [@@inline_let]
  let nl = n `SZ.sub` l in
  if idx `SZ.gte` nl
  then idx `SZ.sub` nl
  else idx `SZ.add` l

#push-options "--query_stats --z3rlimit 256"
#restart-solver

```pulse
fn array_swap(#t: Type0) (#s0: Ghost.erased (Seq.seq t)) (a: A.array t) (n: SZ.t) (l: SZ.t) (bz: Prf.bezout (SZ.v n) (SZ.v l)) (d: SZ.t) (q: SZ.t)
  requires (
    A.pts_to a full_perm s0 `star`
    pure (
      SZ.v n == A.length a /\
      SZ.v n == Seq.length s0 /\
      0 < SZ.v l /\
      SZ.v l < SZ.v n /\
      SZ.v d == bz.d /\
      SZ.v q == bz.q_n
    )
  )
  ensures exists s . (
    A.pts_to a full_perm s `star`
    pure (Prf.array_swap_post s0 (SZ.v n) (SZ.v l) s) // hoisted out because of the SMT pattern on array_as_ring_buffer_swap
  )
{
    let mut pi = 0sz;
    while (let i = !pi; (i `SZ.lt` d))
    invariant b . exists s i . (
      A.pts_to a full_perm s `star`
      R.pts_to pi full_perm i `star`
      pure (
        Prf.array_swap_outer_invariant s0 (SZ.v n) (SZ.v l) bz s (SZ.v i) /\
        eq2_prop #bool b (SZ.v i < bz.d)
    )) {
      let i = !pi;
      let save = a.(i);
      let save_eq0 = magic () <: squash (save == Seq.index s0 (SZ.v i));
      let mut pj = 0sz;
      let mut pidx = i;
      while (let j = !pj; (j `SZ.lt` (q `SZ.sub` 1sz)))
      invariant b . exists s i j idx . (
        A.pts_to a full_perm s `star`
        R.pts_to pi full_perm i `star`
        R.pts_to pj full_perm j `star`
        R.pts_to pidx full_perm idx `star`
        pure (
          Prf.array_swap_inner_invariant s0 (SZ.v n) (SZ.v l) bz s (SZ.v i) (SZ.v j) (SZ.v idx) /\
          eq2_prop #bool b (SZ.v j < bz.q_n - 1)
        )
      ) {
        let j = !pj;
        let idx = !pidx;
        let idx' = impl_jump n l idx;
        let idx'_eq = () <: squash (SZ.v idx' == Prf.jump (SZ.v n) (SZ.v l) (SZ.v idx));
        let x = a.(idx');
        let j' = j `SZ.add` 1sz;
        (a.(idx) <- x);
        pj := j';
        pidx := idx';
        ()
      };
      let idx = !pidx;
      (a.(idx) <- save);
      let i' = i `SZ.add` 1sz;
      let i'_eq = () <: squash (SZ.v i' == SZ.v i + 1);
      pi := i';
      ()
    };
    ()
}
```

#pop-options
