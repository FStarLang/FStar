module Steel.ST.GenArraySwap
open Steel.ST.GenElim

module Prf = Steel.ST.GenArraySwap.Proof
module R = Steel.ST.Reference

let gcd_inv_prop
  (n0: nat)
  (l0: nat)
  (n: nat)
  (l: nat)
  (b: bool)
: Tot prop
= l0 < n0 /\
  l < n /\
  (Prf.mk_bezout n0 l0).d == (Prf.mk_bezout n l).d /\
  b == (l > 0)

[@@__reduce__]
let gcd_inv0
  (n0: SZ.t)
  (l0: SZ.t)
  (pn: R.ref SZ.t)
  (pl: R.ref SZ.t)
  (b: bool)
: Tot vprop
= exists_ (fun n -> exists_ (fun l ->
    R.pts_to pn full_perm n `star`
    R.pts_to pl full_perm l `star`
    pure (gcd_inv_prop (SZ.v n0) (SZ.v l0) (SZ.v n) (SZ.v l) b)
  ))

let gcd_inv
  (n0: SZ.t)
  (l0: SZ.t)
  (pn: R.ref SZ.t)
  (pl: R.ref SZ.t)
  (b: bool)
: Tot vprop
= gcd_inv0 n0 l0 pn pl b

let gcd_post
  (n0: SZ.t)
  (l0: SZ.t)
  (res: SZ.t)
: Tot prop
= SZ.v l0 < SZ.v n0 /\
  SZ.v res == (Prf.mk_bezout (SZ.v n0) (SZ.v l0)).d

#push-options "--z3rlimit 16"

#restart-solver
let gcd
  (n0: SZ.t)
  (l0: SZ.t)
: ST SZ.t
    emp
    (fun _ -> emp)
    (SZ.v l0 < SZ.v n0)
    (fun res -> gcd_post n0 l0 res)
= let res =
    R.with_local n0 (fun pn ->
      R.with_local l0 (fun pl ->
        noop ();
        rewrite (gcd_inv0 n0 l0 pn pl (l0 `SZ.gt` 0sz)) (gcd_inv n0 l0 pn pl (l0 `SZ.gt` 0sz));
        Steel.ST.Loops.while_loop
          (gcd_inv n0 l0 pn pl)
          (fun _ ->
            let gb = elim_exists () in
            rewrite (gcd_inv n0 l0 pn pl gb) (gcd_inv0 n0 l0 pn pl gb);
            let _ = gen_elim () in
            let l = R.read pl in
            [@@inline_let]
            let b = l `SZ.gt` 0sz in
            noop ();
            rewrite (gcd_inv0 n0 l0 pn pl b) (gcd_inv n0 l0 pn pl b);
            return b
          )
          (fun _ ->
            rewrite (gcd_inv n0 l0 pn pl true) (gcd_inv0 n0 l0 pn pl true);
            let _ = gen_elim () in
            let n = R.read pn in
            let l = R.read pl in
            [@@inline_let]
            let l' = SZ.rem n l in
            R.write pn l;
            R.write pl l';
            rewrite (gcd_inv0 n0 l0 pn pl (l' `SZ.gt` 0sz)) (gcd_inv n0 l0 pn pl (l' `SZ.gt` 0sz));
            noop ()
          );
        rewrite (gcd_inv n0 l0 pn pl false) (gcd_inv0 n0 l0 pn pl false);
        let _ = gen_elim () in
        let res = R.read pn in
        return res
      )
    )
  in
  elim_pure (gcd_post n0 l0 res);
  return res

#pop-options

let array_swap_partial_invariant
  (#t: Type)
  (n: nat)
  (l: nat)
  (bz: Prf.bezout n l)
  (s0: Ghost.erased (Seq.seq t))
  (s: Ghost.erased (Seq.seq t))
  (i: nat)
: GTot prop
= n == Seq.length s0 /\
  n == Seq.length s /\
  0 < l /\
  l < n /\
  i <= bz.d /\
  (forall (i': Prf.nat_up_to bz.d) .
    (forall (j: Prf.nat_up_to bz.q_n) .
      (i' < i) ==> (
      let idx = Prf.iter_fun #(Prf.nat_up_to n) (Prf.jump n l) j i' in
      Seq.index s idx == Seq.index s0 (Prf.jump n l idx)
  ))) /\
  (forall (i': Prf.nat_up_to bz.d) .
    (forall (j: Prf.nat_up_to bz.q_n) .
      (i' > i) ==> (
      let idx = Prf.iter_fun #(Prf.nat_up_to n) (Prf.jump n l) j i' in
      Seq.index s idx == Seq.index s0 idx
  )))

let array_swap_inner_invariant_prop
  (#t: Type)
  (n: nat)
  (l: nat)
  (bz: Prf.bezout n l)
  (s0: Ghost.erased (Seq.seq t))
  (s: Ghost.erased (Seq.seq t))
  (i: nat)
  (j: nat)
  (idx: nat)
  (b: bool)
: GTot prop
= Prf.array_swap_inner_invariant s0 n l bz s i j idx /\
  (b == (j < bz.q_n - 1))

let array_swap_outer_invariant_prop
  (#t: Type)
  (n: nat)
  (l: nat)
  (bz: Prf.bezout n l)
  (s0: Ghost.erased (Seq.seq t))
  (s: Ghost.erased (Seq.seq t))
  (i: nat)
  (b: bool)
: GTot prop
= Prf.array_swap_outer_invariant s0 n l bz s i /\
  (b == (i < bz.d))

[@@__reduce__]
let array_swap_outer_invariant_body0
  (#t: Type)
  (pts_to: array_pts_to_t t)
  (pi: R.ref SZ.t)
  (i: SZ.t)
  (s: Ghost.erased (Seq.seq t))
: Tot vprop
=
    R.pts_to pi full_perm i `star`
    pts_to s

[@@erasable]
noeq
type array_swap_outer_invariant_t (t: Type)
= {
    i: SZ.t;
    s: Ghost.erased (Seq.seq t);
  }

[@@__reduce__]
let array_swap_outer_invariant0
  (#t: Type)
  (pts_to: array_pts_to_t t)
  (n: SZ.t)
  (l: SZ.t)
  (bz: Prf.bezout (SZ.v n) (SZ.v l))
  (s0: Ghost.erased (Seq.seq t))
  (pi: R.ref SZ.t)
  (b: bool)
: Tot vprop
= exists_ (fun w ->
    array_swap_outer_invariant_body0 pts_to pi w.i w.s `star`
    pure (array_swap_outer_invariant_prop (SZ.v n) (SZ.v l) bz s0 w.s (SZ.v w.i) b)
 )

let array_swap_outer_invariant
  (#t: Type)
  (pts_to: array_pts_to_t t)
  (n: SZ.t)
  (l: SZ.t)
  (bz: Prf.bezout (SZ.v n) (SZ.v l))
  (s0: Ghost.erased (Seq.seq t))
  (pi: R.ref SZ.t)
  (b: bool)
: Tot vprop
= array_swap_outer_invariant0 pts_to n l bz s0 pi b

let intro_array_swap_outer_invariant
  (#opened: _)
  (#t: Type)
  (pts_to: array_pts_to_t t)
  (n: SZ.t)
  (l: SZ.t)
  (bz: Prf.bezout (SZ.v n) (SZ.v l))
  (s0: Ghost.erased (Seq.seq t))
  (pi: R.ref SZ.t)
  (b: bool)
  (i: SZ.t)
  (s: Ghost.erased (Seq.seq t))
: STGhost unit opened
    (array_swap_outer_invariant_body0 pts_to pi i s)
    (fun _ -> array_swap_outer_invariant pts_to n l bz s0 pi b)
    (array_swap_outer_invariant_prop (SZ.v n) (SZ.v l) bz s0 s (SZ.v i) b)
    (fun _ -> True)
= let w = {
    i = i;
    s = s;
  }
  in
  rewrite (array_swap_outer_invariant_body0 pts_to pi i s) (array_swap_outer_invariant_body0 pts_to pi w.i w.s);
  rewrite (array_swap_outer_invariant0 pts_to n l bz s0 pi b) (array_swap_outer_invariant pts_to n l bz s0 pi b)

let elim_array_swap_outer_invariant
  (#opened: _)
  (#t: Type)
  (pts_to: array_pts_to_t t)
  (n: SZ.t)
  (l: SZ.t)
  (bz: Prf.bezout (SZ.v n) (SZ.v l))
  (s0: Ghost.erased (Seq.seq t))
  (pi: R.ref SZ.t)
  (b: bool)
: STGhost (array_swap_outer_invariant_t t) opened
    (array_swap_outer_invariant pts_to n l bz s0 pi b)
    (fun w -> array_swap_outer_invariant_body0 pts_to pi w.i w.s)
    True
    (fun w ->
      array_swap_outer_invariant_prop (SZ.v n) (SZ.v l) bz s0 w.s (SZ.v w.i) b /\
True //      (b == false ==> Ghost.reveal w.s `Seq.equal` (Seq.slice s0 (SZ.v l) (SZ.v n) `Seq.append` Seq.slice s0 0 (SZ.v l)))
    )
= let w = elim_exists () in
  let _ = gen_elim () in
//  Classical.move_requires (array_swap_outer_invariant_prop_end (SZ.v n) (SZ.v l) bz s0 w.s (SZ.v w.i)) b;
  noop ();
  w

[@@erasable]
noeq
type array_swap_inner_invariant_t (t: Type)
= {
    j: SZ.t;
    idx: SZ.t;
    s: Ghost.erased (Seq.seq t)
  }

[@@__reduce__]
let array_swap_inner_invariant_body0
  (#t: Type)
  (pts_to: array_pts_to_t t)
  (n: SZ.t)
  (l: SZ.t)
  (bz: Prf.bezout (SZ.v n) (SZ.v l))
  (s0: Ghost.erased (Seq.seq t))
  (pi: R.ref SZ.t)
  (i: SZ.t)
  (pj: R.ref SZ.t)
  (pidx: R.ref SZ.t)
  (b: bool)
  (j: SZ.t)
  (idx: SZ.t)
  (s: Ghost.erased (Seq.seq t))
: Tot vprop
=   R.pts_to pi full_perm i `star`
    R.pts_to pj full_perm j `star`
    R.pts_to pidx full_perm idx `star`
    pts_to s

[@@__reduce__]
let array_swap_inner_invariant0
  (#t: Type)
  (pts_to: array_pts_to_t t)
  (n: SZ.t)
  (l: SZ.t)
  (bz: Prf.bezout (SZ.v n) (SZ.v l))
  (s0: Ghost.erased (Seq.seq t))
  (pi: R.ref SZ.t)
  (i: SZ.t)
  (pj: R.ref SZ.t)
  (pidx: R.ref SZ.t)
  (b: bool)
: Tot vprop
= exists_ (fun w ->
    array_swap_inner_invariant_body0 pts_to n l bz s0 pi i pj pidx b w.j w.idx w.s `star`
    pure (array_swap_inner_invariant_prop (SZ.v n) (SZ.v l) bz s0 w.s (SZ.v i) (SZ.v w.j) (SZ.v w.idx) b)
  )

let array_swap_inner_invariant
  (#t: Type)
  (pts_to: array_pts_to_t t)
  (n: SZ.t)
  (l: SZ.t)
  (bz: Prf.bezout (SZ.v n) (SZ.v l))
  (s0: Ghost.erased (Seq.seq t))
  (pi: R.ref SZ.t)
  (i: SZ.t)
  (pj: R.ref SZ.t)
  (pidx: R.ref SZ.t)
  (b: bool)
: Tot vprop
= array_swap_inner_invariant0 pts_to n l bz s0 pi i pj pidx b

let intro_array_swap_inner_invariant
  (#opened: _)
  (#t: Type)
  (pts_to: array_pts_to_t t)
  (n: SZ.t)
  (l: SZ.t)
  (bz: Prf.bezout (SZ.v n) (SZ.v l))
  (s0: Ghost.erased (Seq.seq t))
  (pi: R.ref SZ.t)
  (i: SZ.t)
  (pj: R.ref SZ.t)
  (pidx: R.ref SZ.t)
  (b: bool)
  (j: SZ.t)
  (idx: SZ.t)
  (s: Ghost.erased (Seq.seq t))
: STGhost unit opened
    (array_swap_inner_invariant_body0 pts_to n l bz s0 pi i pj pidx b j idx s)
    (fun _ -> array_swap_inner_invariant pts_to n l bz s0 pi i pj pidx b)
    (array_swap_inner_invariant_prop (SZ.v n) (SZ.v l) bz s0 s (SZ.v i) (SZ.v j) (SZ.v idx) b)
    (fun _ -> True)
= let w = {
    j = j;
    idx = idx;
    s = s;
  }
  in
  rewrite
    (array_swap_inner_invariant_body0 pts_to n l bz s0 pi i pj pidx b j idx s)
    (array_swap_inner_invariant_body0 pts_to n l bz s0 pi i pj pidx b w.j w.idx w.s);
  rewrite
    (array_swap_inner_invariant0 pts_to n l bz s0 pi i pj pidx b)
    (array_swap_inner_invariant pts_to n l bz s0 pi i pj pidx b)

let elim_array_swap_inner_invariant
  (#opened: _)
  (#t: Type)
  (pts_to: array_pts_to_t t)
  (n: SZ.t)
  (l: SZ.t)
  (bz: Prf.bezout (SZ.v n) (SZ.v l))
  (s0: Ghost.erased (Seq.seq t))
  (pi: R.ref SZ.t)
  (i: SZ.t)
  (pj: R.ref SZ.t)
  (pidx: R.ref SZ.t)
  (b: bool)
: STGhost (array_swap_inner_invariant_t t) opened
    (array_swap_inner_invariant pts_to n l bz s0 pi i pj pidx b)
    (fun w -> array_swap_inner_invariant_body0 pts_to n l bz s0 pi i pj pidx b w.j w.idx w.s)
    True
    (fun w -> array_swap_inner_invariant_prop (SZ.v n) (SZ.v l) bz s0 w.s (SZ.v i) (SZ.v w.j) (SZ.v w.idx) b)
= let w = elim_exists () in
  elim_pure _;
  w

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

#push-options "--z3rlimit 64"

#restart-solver
inline_for_extraction
let array_swap_outer_body
  (#t: Type)
  (#pts_to: array_pts_to_t t)
  (index: array_index_t pts_to)
  (upd: array_upd_t pts_to)
  (s0: Ghost.erased (Seq.seq t))
  (n: SZ.t)
  (l: SZ.t)
  (bz: Prf.bezout (SZ.v n) (SZ.v l))
  (d: SZ.t)
  (q: SZ.t)
  (pi: R.ref SZ.t)
  (sq: squash (
    SZ.v d == bz.d /\
    SZ.v q == bz.q_n
  ))
  ()
: STT unit
    (array_swap_outer_invariant pts_to n l bz s0 pi true)
    (fun _ -> exists_ (array_swap_outer_invariant pts_to n l bz s0 pi))
=
  let _ = elim_array_swap_outer_invariant pts_to n l bz s0 pi true in
  let _ = gen_elim () in
  let i = R.read pi in
  let s = vpattern_replace pts_to in
  let save = index _ n i in
  R.with_local 0sz (fun pj ->
  R.with_local i (fun pidx ->
    noop ();
    intro_array_swap_inner_invariant pts_to n l bz s0 pi i pj pidx (0 < bz.q_n - 1) _ _ _;
    Steel.ST.Loops.while_loop
      (array_swap_inner_invariant pts_to n l bz s0 pi i pj pidx)
      (fun _ ->
        let gb = elim_exists () in
        let _ = elim_array_swap_inner_invariant pts_to n l bz s0 pi i pj pidx gb in
        let j = R.read pj in
        [@@inline_let]
        let b = j `SZ.lt` (q `SZ.sub` 1sz) in
        intro_array_swap_inner_invariant pts_to n l bz s0 pi i pj pidx b _ _ _;
        return b
      )
      (fun _ ->
        let _ = elim_array_swap_inner_invariant pts_to n l bz s0 pi i pj pidx true in
        let j = R.read pj in
        let idx = R.read pidx in
        let j' = j `SZ.add` 1sz in
        let idx' = impl_jump n l idx in
        let x = index _ n idx' in
        let _ = upd _ n idx x in
        R.write pj j';
        R.write pidx idx';
        intro_array_swap_inner_invariant pts_to n l bz s0 pi i pj pidx (SZ.v j' < bz.q_n - 1) _ _ _;
        noop ()
      );
    let _ = elim_array_swap_inner_invariant pts_to n l bz s0 pi i pj pidx false in
    let idx = R.read pidx in
    let _ = upd _ n idx save in
    [@@inline_let]
    let i' = i `SZ.add` 1sz in
    R.write pi i';
    intro_array_swap_outer_invariant pts_to n l bz s0 pi (i' `SZ.lt` d) _ _;
    noop ()
  ))

#restart-solver
inline_for_extraction
let array_swap_aux
  (#t: Type)
  (#pts_to: array_pts_to_t t)
  (index: array_index_t pts_to)
  (upd: array_upd_t pts_to)
  (s0: Ghost.erased (Seq.seq t))
  (n: SZ.t)
  (l: SZ.t)
: ST (Ghost.erased (Seq.seq t))
    (pts_to s0)
    (fun s -> pts_to s)
    (
      SZ.v n == Seq.length s0 /\
      SZ.v l > 0 /\
      SZ.v l < SZ.v n
    )
    (fun s -> Prf.array_swap_post s0 (SZ.v n) (SZ.v l) s)
= let bz = Prf.mk_bezout (SZ.v n) (SZ.v l) in
  let d = gcd n l in
  let q = n `SZ.div` d in
  let s = R.with_local #_ 0sz #_ #(Ghost.erased (Seq.seq t)) #(fun s -> pts_to s `star` pure (Prf.array_swap_post s0 (SZ.v n) (SZ.v l) s)) (fun pi ->
    intro_array_swap_outer_invariant pts_to n l bz s0 pi true _ _;
    Steel.ST.Loops.while_loop
      (array_swap_outer_invariant pts_to n l bz s0 pi)
      (fun _ ->
        let gb = elim_exists () in
        let _ = elim_array_swap_outer_invariant pts_to n l bz s0 pi gb in
        let i = R.read pi in
        [@@inline_let]
        let b = i `SZ.lt` d in
        intro_array_swap_outer_invariant pts_to n l bz s0 pi b _ _;
        return b
      )
      (array_swap_outer_body index upd s0 n l bz d q pi ());
    let _ = elim_array_swap_outer_invariant pts_to n l bz s0 pi false in
    return _
  )
  in
  elim_pure _;
  return s

#pop-options

inline_for_extraction
let array_swap_gen
  (#t: Type)
  (#pts_to: array_pts_to_t t)
  (index: array_index_t pts_to)
  (upd: array_upd_t pts_to)
  (s0: Ghost.erased (Seq.seq t))
  (n: SZ.t)
  (l: SZ.t)
: ST (Ghost.erased (Seq.seq t))
    (pts_to s0)
    (fun s -> pts_to s)
    (
      SZ.v n == Seq.length s0 /\
      SZ.v l <= SZ.v n
    )
    (fun s ->
      SZ.v n == Seq.length s0 /\
      SZ.v l <= SZ.v n /\
      s `Seq.equal` (Seq.slice s0 (SZ.v l) (SZ.v n) `Seq.append` Seq.slice s0 0 (SZ.v l))
    )
= if l = 0sz || l = n
  then begin
    noop ();
    return s0
  end
  else array_swap_aux index upd s0 n l
