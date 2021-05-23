(*
   Copyright 2021 Microsoft Research

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

module Steel.Array
open Steel.Effect.Atomic
open Steel.Reference

let seq_facts () : Lemma (
  (forall (t: Type) (s: Seq.seq t) .
    Seq.length s == 0 ==> s == Seq.empty) /\
  (forall (t: Type) (a: t) (s: Seq.seq t) .
    Seq.head (Seq.cons a s) == a /\ Seq.tail (Seq.cons a s) == s) /\
  (forall (t: Type) (s: Seq.seq t) .
    Seq.length s > 0 ==>
    s == Seq.cons (Seq.head s) (Seq.tail s))
) =
  let e
    (t: Type) (s: Seq.seq t)
  : Lemma
    (Seq.length s == 0 ==> s == Seq.empty)
  =
    if Seq.length s = 0 then assert (s `Seq.equal` Seq.empty)
  in
  let f
    (t: Type) (a: t) (s: Seq.seq t)
  : Lemma
    (Seq.head (Seq.cons a s) == a /\ Seq.tail (Seq.cons a s) == s)
  = Seq.head_cons a s;
    Seq.lemma_tl a s
  in
  let g
    (t: Type) (s: Seq.seq t)
  : Lemma
    (Seq.length s > 0 ==> s == Seq.cons (Seq.head s) (Seq.tail s))
  =
    if Seq.length s > 0
    then Seq.cons_head_tail s
  in
  Classical.forall_intro_2 e;
  Classical.forall_intro_3 f;
  Classical.forall_intro_2 g

let fits32 (x: nat) : Tot prop = FStar.UInt.fits x U32.n == true
let array1 (t: Type) : Tot Type = (x: Seq.seq (ref t) {fits32 (Seq.length x)})
let array2 (t: Type) : Tot Type = Ghost.erased (array1 t)
noeq
type array t = {
  base: array1 t;
  from: U32.t;
  to: (to: Ghost.erased U32.t { U32.v from <= U32.v to /\ U32.v to <= Seq.length base })
}
let len #t a = a.to `U32.sub` a.from

let vnil_rewrite
  (t: Type)
  (x: t_of emp)
: GTot (Seq.lseq t 0)
= Seq.empty

let vnil
  (t: Type)
: Pure vprop
  (requires True)
  (ensures (fun v -> t_of v == Seq.lseq t 0))
= vrewrite emp (vnil_rewrite t)

let vcons_rewrite
  (#t: Type)
  (p: perm)
  (n: Ghost.erased nat)
  (r: Ghost.erased (ref t))
  (v: vprop)
  (sq: squash (t_of v == Seq.lseq t n))
  (xy: t_of (vptrp r p `star` v))
: GTot (Seq.lseq t (n + 1))
= Seq.cons (fst xy) (snd xy)

let vcons
  (#t: Type)
  (p: perm)
  (n: Ghost.erased nat)
  (r: Ghost.erased (ref t))
  (v: vprop)
: Pure vprop
  (requires (t_of v == Seq.lseq t n))
  (ensures (fun v' -> t_of v' == Seq.lseq t (n + 1)))
= vrewrite (vptrp r p `star` v) (vcons_rewrite p n r v ())

let rec varray1
  (#t: Type0)
  (a: array2 t)
  (p: perm)
: Pure vprop
  (requires True)
  (ensures (fun v -> t_of v == Seq.lseq t (Seq.length a)))
  (decreases (Seq.length a))
= if Seq.length a = 0
  then vnil t
  else vcons p (Seq.length a - 1) (Seq.index a 0) (varray1 (Seq.slice a 1 (Seq.length a)) p)

[@@ __steel_reduce__]
unfold
let sel_varray1 (#a:Type) (#p:vprop) (r:array2 a)
  (q: perm)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (varray1 r q) /\ True)})
: GTot (Seq.lseq a (Seq.length r))
= let x : t_of (varray1 r q) = h (varray1 r q) in
  x

let sel_varray2
  (#a: Type0)
  (r: array2 a)
  (p: perm)
: Tot (selector (Seq.lseq a (Seq.length r)) (hp_of (varray1 r p)))
= fun h -> sel_of (varray1 r p) h

[@@ __steel_reduce__]
let varray2' (#a: Type0) (r: array2 a) (p: perm) : vprop' =
  {hp = hp_of (varray1 r p);
   t = Seq.lseq a (Seq.length r);
   sel = sel_varray2 r p}

[@@ __steel_reduce__]
let varray2 r p = VUnit (varray2' r p)

let varray9
  (#t: Type0)
  (a: array t)
  (p: perm)
: Tot vprop
= varray2 (Seq.slice a.base (U32.v a.from) (U32.v a.to)) p

let is_array #a r p = hp_of (varray9 r p)

let array_sel #a r p = fun h -> sel_of (varray9 r p) h

let intro_varray
  (#opened: _)
  (#t: Type)
  (p: perm)
  (q: array2 t)
  (r: array t)
: SteelGhost unit opened
    (varray2 q p)
    (fun _ -> varrayp r p)
    (fun _ -> Ghost.reveal q `Seq.equal` Seq.slice r.base (U32.v r.from) (U32.v r.to))
    (fun h _ h' ->
      (h (varray2 q p) <: Seq.seq t) == h' (varrayp r p)
    )
=
  change_slprop_rel
    (varray2 q p)
    (varrayp r p)
    (fun (x: t_of (varray2 q p)) (y: t_of (varrayp r p)) -> (x <: Seq.seq t) == y)
    (fun _ -> ())

let elim_varray
  (#opened: _)
  (#t: Type)
  (r: array t)
  (p: perm)
: SteelGhost (array2 t) opened
    (varrayp r p)
    (fun q -> varray2 q p)
    (fun _ -> True)
    (fun h q h' ->
      Ghost.reveal q == Seq.slice r.base (U32.v r.from) (U32.v r.to) /\
      (h (varrayp r p) <: Seq.seq t) == h' (varray2 q p)
    )
=
  let q : array2 t = (Seq.slice r.base (U32.v r.from) (U32.v r.to)) in
  change_slprop_rel
    (varrayp r p)
    (varray2 q p)
    (fun (y: t_of (varray r)) (x: t_of (varray2 q p)) -> (x <: Seq.seq t) == y)
    (fun _ -> ());
  q

let intro_varray2
  (#opened: _)
  (#t: Type)
  (q: array2 t)
  (p: perm)
: SteelGhost unit opened
    (varray1 q p)
    (fun _ -> varray2 q p)
    (fun _ -> True)
    (fun h _ h' ->
      (h' (varray2 q p) <: Seq.seq t) == sel_varray1 q p h
    )
=
  change_slprop_rel
    (varray1 q p)
    (varray2 q p)
    (fun (x: t_of (varray1 q p)) (y: t_of (varray2 q p)) -> (x <: Seq.seq t) == y)
    (fun _ -> ())

let elim_varray2
  (#opened: _)
  (#t: Type)
  (r: array2 t)
  (p: perm)
: SteelGhost unit opened
    (varray2 r p)
    (fun _ -> varray1 r p)
    (fun _ -> True)
    (fun h _ h' ->
      (h (varray2 r p) <: Seq.seq t) == sel_varray1 r p h'
    )
=
  change_slprop_rel
    (varray2 r p)
    (varray1 r p)
    (fun (y: t_of (varray2 r p)) (x: t_of (varray1 r p)) -> (x <: Seq.seq t) == y)
    (fun _ -> ())

let intro_vnil1
  (#opened: _)
  (t: Type)
  (p: perm)
: SteelGhost (array2 t) opened
    emp
    (fun r -> varray1 r p)
    (fun _ -> True)
    (fun _ r _ -> Seq.length r == 0)
=
  intro_vrewrite emp (vnil_rewrite t);
  let r : array2 t = Seq.empty in
  change_slprop
    (vrewrite emp (vnil_rewrite t))
    (varray1 r p)
    (Ghost.hide (Seq.empty #t <: t_of (vrewrite emp (vnil_rewrite t))))
    (Ghost.hide (Seq.empty #t <: t_of (varray1 r p)))
    (fun _ -> ());
  r

let intro_vnil
  (#opened: _)
  (t: Type)
  (p: perm)
: SteelGhost (array2 t) opened
    emp
    (fun r -> varray2 r p)
    (fun _ -> True)
    (fun _ r h' ->
      Ghost.reveal r == Seq.empty /\
      h' (varray2 r p) == Seq.empty
    )
=
  seq_facts ();
  let res = intro_vnil1 t p in
  intro_varray2 res _;
  res

let intro_vcons1
  (#opened: _)
  (#t: Type)
  (p: perm)
  (r: Ghost.erased (ref t))
  (a: array2 t)
: SteelGhost (array2 t) opened
    (vptrp r p `star` varray1 a p)
    (fun a' -> varray1 a' p)
    (fun _ -> fits32 (Seq.length a + 1))
    (fun h a' h' ->
      Ghost.reveal a' == Seq.cons (Ghost.reveal r) a /\
      (sel_varray1 a' p h' <: Seq.seq t) ==
        Seq.cons (h (vptrp r p)) (sel_varray1 a p h)
    )
=
  seq_facts ();
  reveal_star (vptrp r p) (varray1 a p); // FIXME: WHY WHY WHY?
  intro_vrewrite (vptrp r p `star` varray1 a p) (vcons_rewrite p (Seq.length a) r (varray1 a p) ());
  let a' : array2 t = Seq.cons (Ghost.reveal r) a in
  change_equal_slprop
    (vrewrite (vptrp r p `star` varray1 a p) (vcons_rewrite p (Seq.length a) r (varray1 a p) ()))
    (varray1 a' p);
  a'

let intro_vcons
  (#opened: _)
  (#t: Type)
  (p: perm)
  (r: Ghost.erased (ref t))
  (a: array2 t)
: SteelGhost (array2 t) opened
    (vptrp r p `star` varray2 a p)
    (fun a' -> varray2 a' p)
    (fun _ -> fits32 (Seq.length a + 1))
    (fun h a' h' ->
      Ghost.reveal a' == Seq.cons (Ghost.reveal r) a /\
      h' (varray2 a' p) ==
        Seq.cons (h (vptrp r p)) (h (varray2 a p))
    )
= elim_varray2 a p;
  let res = intro_vcons1 p r a in
  intro_varray2 res p;
  res

#set-options "--ide_id_info_off" 

#push-options "--z3rlimit 16"
#restart-solver

let elim_vcons1
  (#opened: _)
  (#t: Type)
  (a: array2 t)
  (p: perm)
: SteelGhost (Ghost.erased (ref t) & array2 t) opened
    (varray1 a p)
    (fun res -> vptrp (pfst res) p `star` varray1 (psnd res) p)
    (fun _ -> Seq.length a > 0)
    (fun h res h' ->
      Seq.length a > 0 /\
      begin let s = sel_varray1 a p h in
      h' (vptrp (pfst res) p) == Seq.head s /\
      Seq.tail s == sel_varray1 (psnd res) p h' /\
      Ghost.reveal a == Seq.cons (Ghost.reveal (pfst res)) (psnd res)
      end
    )
=
  seq_facts ();
  let a0 : Ghost.erased (Seq.seq (ref t)) = Ghost.hide (Ghost.reveal a) in // same here
  let r : Ghost.erased (ref t) = (Seq.head a0) in
  let q : array2 t = Seq.tail a0 in
  change_equal_slprop
    (varray1 a p)
    (vrewrite (vptrp (r) p `star` varray1 (q) p) (vcons_rewrite p (Seq.length (q)) (r) (varray1 (q) p) ()));
  elim_vrewrite (vptrp (r) p `star` varray1 (q) p) (vcons_rewrite p (Seq.length (q)) (r) (varray1 (q) p) ());
  reveal_star (vptrp (r) p) (varray1 (q) p);
  let res : (Ghost.erased (ref t) & array2 t) = (r, q) in
  change_equal_slprop
    (vptrp (r) p `star` varray1 (q) p)
    (vptrp (pfst res) p `star` varray1 (psnd res) p);
  reveal_star (vptrp (pfst res) p) (varray1 (psnd res) p);
  res

#pop-options

let elim_vcons
  (#opened: _)
  (#t: Type)
  (a: array2 t)
  (p: perm)
: SteelGhost (Ghost.erased (ref t) & array2 t) opened
    (varray2 a p)
    (fun res -> vptrp (pfst res) p `star` varray2 (psnd res) p)
    (fun _ -> Seq.length a > 0)
    (fun h res h' ->
      Seq.length a > 0 /\
      begin let s = h (varray2 a p) in
      s == Seq.cons (h' (vptrp (pfst res) p)) (h' (varray2 (psnd res) p)) /\
      Ghost.reveal a == Seq.cons (Ghost.reveal (pfst res)) (psnd res)
      end
    )
=
  elim_varray2 a p;
  let res = elim_vcons1 a p in
  intro_varray2 (psnd res) p;
  res

let elim_nil
  (#opened: _)
  (#t: Type)
  (a: array2 t)
  (p: perm)
: SteelGhost unit opened
    (varray2 a p)
    (fun _ -> emp)
    (fun _ -> Seq.length a == 0)
    (fun _ _ _ -> True)
=
  elim_varray2 a p; 
  change_equal_slprop
    (varray1 a p)
    (vrewrite emp (vnil_rewrite t));
  elim_vrewrite emp (vnil_rewrite t)

let seq_append_nil
  (#t: Type)
  (a2: Seq.seq t)
: Lemma
  (Seq.append Seq.empty a2 == a2)
  [SMTPat (Seq.append Seq.empty a2)]
= assert (Seq.append Seq.empty a2 `Seq.equal` a2)

#push-options "--z3rlimit 16"
#restart-solver

let seq_append_cons
  (#t: Type)
  (c: t)
  (a1 a2: Seq.seq t)
: Lemma
  (Seq.append (Seq.cons c a1) a2 == Seq.cons c (Seq.append a1 a2))
  [SMTPat (Seq.append (Seq.cons c a1) a2)]
=
  assert (Seq.append (Seq.cons c a1) a2 `Seq.equal` Seq.cons c (Seq.append a1 a2))

#pop-options

#push-options "--z3rlimit 64"
#restart-solver

let rec vappend
  (#opened: _)
  (#t: Type)
  (a1 a2: array2 t)
  (p: perm)
: SteelGhost (array2 t) opened
    (varray2 a1 p `star` varray2 a2 p)
    (fun r -> varray2 r p)
    (fun _ -> fits32 (Seq.length a1 + Seq.length a2))
    (fun h r h' ->
      h' (varray2 r p) == Seq.append (h (varray2 a1 p)) (h (varray2 a2 p)) /\
      Ghost.reveal r == Seq.append a1 a2
    )
    (decreases (Seq.length a1))
=
  seq_facts ();
  if Seq.length a1 = 0
  then begin
    elim_nil a1 p;
    a2
  end else begin
    let hd_tl = elim_vcons a1 p in
    reveal_star_3 (vptrp (pfst hd_tl) p) (varray2 (psnd hd_tl) p) (varray2 a2 p); // FIXME: WHY WHY WHY?
    let tl' = vappend (psnd hd_tl) a2 p in
    let res = intro_vcons p (pfst hd_tl) tl' in
    res
  end

#pop-options

let slice_cons_left
  (#t: Type)
  (a: t)
  (x: Seq.seq t)
  (i: nat)
: Lemma
  ((i > 0 /\ i <= Seq.length x + 1) ==> Seq.slice (Seq.cons a x) 0 i == Seq.cons a (Seq.slice x 0 (i - 1)))
= if i > 0 && i <= Seq.length x + 1 then assert (Seq.slice (Seq.cons a x) 0 i `Seq.equal` Seq.cons a (Seq.slice x 0 (i - 1)))

let slice_cons_right
  (#t: Type)
  (a: t)
  (x: Seq.seq t)
  (i: nat)
: Lemma
  ((i > 0 /\ i <= Seq.length x + 1) ==> Seq.slice (Seq.cons a x) i (Seq.length x + 1) == Seq.slice x (i - 1) (Seq.length x))
= if i > 0 && i <= Seq.length x + 1 then assert (Seq.slice (Seq.cons a x) i (Seq.length x + 1) `Seq.equal` Seq.slice x (i - 1) (Seq.length x))

#push-options "--z3rlimit 16"  // 256 --fuel 6 --ifuel 6"
#restart-solver

let rec vsplit0
  (#opened: _)
  (#t: Type)
  (p: perm)
  (a: array2 t)
  (i: U32.t)
: SteelGhost (array2 t & array2 t) opened
    (varray2 a p)
    (fun res -> varray2 (pfst res) p `star` varray2 (psnd res) p)
    (fun _ -> U32.v i <= Seq.length a)
    (fun h res h' ->
      let s = h (varray2 a p) in
      U32.v i <= Seq.length a /\
      pfst res `Seq.equal` Seq.slice a 0 (U32.v i) /\
      psnd res `Seq.equal` Seq.slice a (U32.v i) (Seq.length a) /\
      h' (varray2 (pfst res) p) == Seq.slice s 0 (U32.v i) /\
      h' (varray2 (psnd res) p) `Seq.equal` Seq.slice s (U32.v i) (Seq.length a)
    )
    (decreases (U32.v i))
=
  seq_facts ();
  let g0 = gget (varray2 a p) in
  if i = 0ul
  then begin
    let n = intro_vnil t p in
    reveal_star (varray2 n p) (varray2 a p);
    let res = (n, a) in
    change_equal_slprop
      (varray2 n p `star` varray2 a p)
      (varray2 (pfst res) p `star` varray2 (psnd res) p);
    reveal_star (varray2 (pfst res) p) (varray2 (psnd res) p);
    res
  end else begin
    let hd_tl : (Ghost.erased (ref t) & array2 t) = elim_vcons a p in
    reveal_star (vptrp (pfst hd_tl) p) (varray2 (psnd hd_tl) p);
    let j = i `U32.sub` 1ul in
    assert (U32.v j == U32.v i - 1);
    let g2_hd = gget (vptrp (pfst hd_tl) p) in
    let g2_tl = gget (varray2 (psnd hd_tl) p) in
    slice_cons_left (Ghost.reveal g2_hd) (Ghost.reveal g2_tl) (U32.v i);
    slice_cons_right (Ghost.reveal g2_hd) (Ghost.reveal g2_tl) (U32.v i);
    let sl_sr = vsplit0 p (psnd hd_tl) j in
    reveal_star_3 (vptrp (pfst hd_tl) p) (varray2 (pfst sl_sr) p) (varray2 (psnd sl_sr) p); // FIXME: WHY WHY WHY?
    let sl = intro_vcons p (pfst hd_tl) (pfst sl_sr) in
    reveal_star (varray2 sl p) (varray2 (psnd sl_sr) p);
    let res = (sl, psnd sl_sr) in
    change_equal_slprop
      (varray2 sl p `star` varray2 (psnd sl_sr) p)
      (varray2 (pfst res) p `star` varray2 (psnd res) p);
    reveal_star (varray2 (pfst res) p) (varray2 (psnd res) p);
    res
  end

#pop-options

val vsplit
  (#opened: _)
  (#t: Type)
  (p: perm)
  (a: array2 t)
  (i: U32.t)
: SteelGhost (array2 t & array2 t) opened
    (varray2 a p)
    (fun res -> varray2 (pfst res) p `star` varray2 (psnd res) p)
    (fun _ -> U32.v i <= Seq.length a)
    (fun h res h' ->
      let s = h (varray2 a p) in
      U32.v i <= Seq.length a /\
      pfst res `Seq.equal` Seq.slice a 0 (U32.v i) /\
      psnd res `Seq.equal` Seq.slice a (U32.v i) (Seq.length a) /\
      (a <: Seq.seq (ref t)) == Seq.append (pfst res) (psnd res) /\
      h' (varray2 (pfst res) p) == Seq.slice s 0 (U32.v i) /\
      h' (varray2 (psnd res) p) `Seq.equal` Seq.slice s (U32.v i) (Seq.length a) /\
      s == Seq.append (h' (varray2 (pfst res) p)) (h' (varray2 (psnd res) p))
    )

let vsplit
  #_ #t p a i
=
  let g = gget (varray2 a p) in
  Seq.lemma_split a (U32.v i);
  Seq.lemma_split #t (Ghost.reveal g) (U32.v i);
  vsplit0 p a i

[@@erasable]
noeq
type ith_t
  (t: Type)
= {
  ith_lhs: array2 t;
  ith_item: Ghost.erased (ref t);
  ith_rhs: array2 t;
}

#push-options "--z3rlimit 16"

let unpack_ith
  (#opened: _)
  (#t: Type)
  (p: perm)
  (a: array2 t)
  (i: U32.t)
: SteelGhost (ith_t t) opened
    (varray2 a p)
    (fun res -> varray2 res.ith_lhs p `star` vptrp res.ith_item p `star` varray2 res.ith_rhs p)
    (fun _ -> U32.v i < Seq.length a)
    (fun h res h' ->
      U32.v i < Seq.length a /\
      Ghost.reveal a == Seq.append res.ith_lhs (Seq.cons (Ghost.reveal res.ith_item) res.ith_rhs) /\
      can_be_split (varray2 res.ith_lhs p `star` vptrp res.ith_item p `star` varray2 res.ith_rhs p) (varray2 res.ith_lhs p) /\
      can_be_split (varray2 res.ith_lhs p `star` vptrp res.ith_item p `star` varray2 res.ith_rhs p) (vptrp res.ith_item p) /\
      can_be_split (varray2 res.ith_lhs p `star` vptrp res.ith_item p `star` varray2 res.ith_rhs p) (varray2 res.ith_lhs p) /\
      h (varray2 a p) == Seq.append (h' (varray2 res.ith_lhs p)) (Seq.cons (h' (vptrp res.ith_item p)) (h' (varray2 res.ith_rhs p))) /\
      Seq.length res.ith_lhs == U32.v i
    )
=
  let m = get #(varray2 a p) () in
  let rsplit = vsplit p a i in
  reveal_star (varray2 (pfst rsplit) p) (varray2 (psnd rsplit) p);
  let rcons = elim_vcons (psnd rsplit) p in
  reveal_star_3 (varray2 (pfst rsplit) p) (vptrp (pfst rcons) p) (varray2 (psnd rcons) p);
  let res = { ith_lhs = pfst rsplit; ith_item = pfst rcons; ith_rhs = psnd rcons } in
  change_equal_slprop
    (varray2 (pfst rsplit) p `star` vptrp (pfst rcons) p `star` varray2 (psnd rcons) p)
    (varray2 res.ith_lhs p `star` vptrp res.ith_item p `star` varray2 res.ith_rhs p);
  reveal_star_3 (varray2 res.ith_lhs p) (vptrp res.ith_item p) (varray2 res.ith_rhs p);
  res

#pop-options

let pack_ith
  (#opened: _)
  (#t: Type)
  (p: perm)
  (res: ith_t t)
  (a: array2 t)
: SteelGhost unit opened
    (varray2 res.ith_lhs p `star` vptrp res.ith_item p `star` varray2 res.ith_rhs p)
    (fun _ -> varray2 a p)
    (fun _ ->
      Ghost.reveal a == Seq.append res.ith_lhs (Seq.cons (Ghost.reveal res.ith_item) res.ith_rhs)
    )
    (fun h _ h' ->
      let i = Seq.length res.ith_lhs in
      can_be_split (varray2 res.ith_lhs p `star` vptrp res.ith_item p `star` varray2 res.ith_rhs p) (varray2 res.ith_lhs p) /\
      can_be_split (varray2 res.ith_lhs p `star` vptrp res.ith_item p `star` varray2 res.ith_rhs p) (vptrp res.ith_item p) /\
      h' (varray2 a p) == Seq.append (h (varray2 res.ith_lhs p)) (Seq.cons (h (vptrp res.ith_item p)) (h (varray2 res.ith_rhs p)))
    )
=
  reveal_star_3 (varray2 res.ith_lhs p) (vptrp res.ith_item p) (varray2 res.ith_rhs p);
  let rhs = intro_vcons p res.ith_item res.ith_rhs in
  reveal_star (varray2 res.ith_lhs p) (varray2 rhs p);
  let a' = vappend res.ith_lhs rhs p in
  change_equal_slprop (varray2 a' p) (varray2 a p)

let seq_index_append_cons
  (#t: Type)
  (i: nat)
  (a: Seq.seq t) (x: t) (b: Seq.seq t)
: Lemma
  (requires (Seq.length a == i))
  (ensures (Seq.index (Seq.append a (Seq.cons x b)) i == x))
= ()

let seq_upd_append_cons
  (#t: Type)
  (i: nat)
  (y: t)
  (a: Seq.seq t) (x: t) (b: Seq.seq t)
: Lemma
  (Seq.length a == i ==> Seq.upd (Seq.append a (Seq.cons x b)) i y == Seq.append a (Seq.cons y b))
=
  assert (Seq.length a == i ==> Seq.upd (Seq.append a (Seq.cons x b)) i y `Seq.equal` Seq.append a (Seq.cons y b))

let decr32 (a:U32.t) (sq: squash (a <> 0ul)) : Pure U32.t
  (requires True)
  (ensures (fun c -> U32.v a - 1 == U32.v c))
= U32.sub a 1ul

let rec valloc
  (#t: Type)
  (i: U32.t)
  (x: t)
: Steel (array1 t)
    emp
    (fun res -> varray2 res full_perm)
    (fun _ -> True)
    (fun _ res h' ->
      Seq.length res == U32.v i /\
      h' (varray2 res full_perm) == Seq.create (U32.v i) x
    )
    (decreases (U32.v i))
=
  if i = 0ul
  then
    let res = intro_vnil t full_perm in
    assert (Seq.create 0 x `Seq.equal` Seq.empty);
    let res2 : array1 t = Seq.empty in
    change_equal_slprop
      (varray2 res full_perm)
      (varray2 res2 full_perm);
    return res2
  else begin
    let sq : squash (i <> 0ul) = () in
    let hd = Steel.Reference.alloc x in
    let j = decr32 i sq in
    assert (Seq.cons x (Seq.create (U32.v j) x) `Seq.equal` Seq.create (U32.v i) x);
    let tl = valloc j x in
    change_equal_slprop
      (vptr hd)
      (vptr (Ghost.reveal (Ghost.hide hd)));
    let res = intro_vcons full_perm (Ghost.hide hd) tl in
    let res2 = Seq.cons hd tl in
    change_equal_slprop
      (varray2 res full_perm)
      (varray2 res2 full_perm);
    return res2
  end

let adjacent #_ a b = a.base == b.base /\ Ghost.reveal a.to == b.from

let tmerge
  (#t: Type)
  (r1 r2: array t)
: Pure (array t)
  (requires (adjacent r1 r2))
  (ensures (fun r -> length r == length r1 + length r2))
= {
  base = r1.base;
  from = r1.from;
  to = r2.to;
}

let merge #t r1 r2 = tmerge r1 r2

let merge_assoc r1 r2 r3 = ()

let tsplit
  (#t: Type)
  (r: array t)
  (i: U32.t)
: Pure (array t & array t)
  (requires (U32.v i <= length r))
  (ensures (fun (rl, rr) ->
    merge_into rl rr r /\
    length rl == U32.v i
  ))
=
  let mid = r.from `U32.add` i in
  let r1 = {
    base = r.base;
    from = r.from;
    to = mid;
  } in
  let r2 = {
    base = r.base;
    from = mid;
    to = r.to
  } in
  (r1, r2)

let merge_zero_left #t r1 r2 = ()

let merge_zero_right #t r1 r2 = ()

let gsplit #t r i = tsplit r i

let gsplit_unique #t r rl rr = ()

val gsplit0 (#opened: _) (#t:Type) (p: perm) (a:array t) (i:U32.t)
  : SteelGhost (Ghost.erased (array t & array t)) opened
          (varrayp a p)
          (fun res -> varrayp (pfst res) p `star` varrayp (psnd res) p)
          (fun _ -> U32.v i <= length a)
          (fun h res h' ->
            let s = h (varrayp a p) in
            let sl = h' (varrayp (pfst res) p) in
            let sr = h' (varrayp (psnd res) p) in
            U32.v i <= length a /\
            Ghost.reveal res == gsplit a i /\
            sl == Seq.slice s 0 (U32.v i) /\
            sr == Seq.slice s (U32.v i) (length a) /\
            s == sl `Seq.append` sr
          )

#push-options "--z3rlimit 32"
#restart-solver
let gsplit0 #t p a i =
  let a2 = elim_varray a p in
  let res2 = vsplit p a2 i in
  let res = tsplit a i in
  intro_varray p (pfst res2) (pfst res);
  intro_varray p (psnd res2) (psnd res);
  let gres = Ghost.hide res in
  change_equal_slprop
    (varrayp (pfst res) p)
    (varrayp (pfst gres) p);
  change_equal_slprop
    (varrayp (psnd res) p)
    (varrayp (psnd gres) p);
  gres
#pop-options

let splitp #t a p i =
  let gres = gsplit0 p a i in
  let res = tsplit a i in
  change_equal_slprop
    (varrayp (pfst gres) p)
    (varrayp (pfst res) p);
  change_equal_slprop
    (varrayp (psnd gres) p)
    (varrayp (psnd res) p);
  return res

val gjoin (#opened: _) (#t:Type) (al ar:array t)
  (p: perm)
  : SteelGhost (Ghost.erased (array t)) opened
          (varrayp al p `star` varrayp ar p)
          (fun a -> varrayp a p)
          (fun _ -> adjacent al ar)
          (fun h a h' ->
            let s = h' (varrayp a p) in
            s == (h (varrayp al p) `Seq.append` h (varrayp ar p)) /\
            merge_into al ar a
          )

#push-options "--z3rlimit 32"
#restart-solver
let gjoin #t al ar p =
  let al2 = elim_varray al p in
  let ar2 = elim_varray ar p in
  let a2 = vappend al2 ar2 p in
  let a = tmerge al ar in
  intro_varray p a2 a;
  let res = Ghost.hide a in
  change_equal_slprop
    (varrayp a p)
    (varrayp (Ghost.reveal res) p);
  res
#pop-options

let joinp #t al ar p =
  let ga : Ghost.erased (array t) = gjoin al ar p in
  let a = tmerge al ar in
  change_equal_slprop
    (varrayp (Ghost.reveal ga) p)
    (varrayp a p);
  return a

let freeable #t a = a.from == 0ul /\ U32.v a.to == Seq.length a.base

let alloc2 (#t:Type) (x:t) (n:U32.t)
  : Steel (array t)
             emp
             (fun r -> varray r)
             (requires fun _ -> True)
             (ensures fun _ r h1 ->
               Seq.length r.base == U32.v n /\
               r.from == 0ul /\
               Ghost.reveal r.to == n /\
               asel r h1 == Seq.create (U32.v n) x /\
               freeable r
             )
=
  let base = valloc n x in
  let res = {
    base = base;
    from = 0ul;
    to = n;
  } in
  intro_varray full_perm (Ghost.hide base) res;
  return res

let alloc x n = alloc2 x n

let indexp #t r q i =
  let r2 = elim_varray r q in
  let p = unpack_ith q r2 i in
  let gl = gget (varray2 p.ith_lhs q) in
  let gg = gget (vptrp p.ith_item q) in
  let gr = gget (varray2 p.ith_rhs q) in
  seq_index_append_cons (U32.v i) (Ghost.reveal gl) (Ghost.reveal gg) (Ghost.reveal gr);
  (* r2 and p are ghost,
     so the proper way is to index into base *)
  seq_index_append_cons (U32.v i) p.ith_lhs p.ith_item p.ith_rhs;
  let j : nat = U32.v r.from + U32.v i in
  let pi = Seq.index r.base j in
  change_equal_slprop (vptrp p.ith_item q) (vptrp pi q);
  let res = readp pi q in
  change_equal_slprop (vptrp pi q) (vptrp p.ith_item q);
  pack_ith q p r2;
  intro_varray q r2 r;
  return res

let upd #t r i x =
  let r2 = elim_varray r _ in
  let p = unpack_ith _ r2 i in
  let gl = gget (varray2 p.ith_lhs _) in
  let gg = gget (vptr p.ith_item) in
  let gr = gget (varray2 p.ith_rhs _) in
  seq_upd_append_cons (U32.v i) x (Ghost.reveal gl) (Ghost.reveal gg) (Ghost.reveal gr);
  (* r2 and p are ghost,
     so the proper way is to index into base *)
  seq_index_append_cons (U32.v i) p.ith_lhs p.ith_item p.ith_rhs;
  let j : nat = U32.v r.from + U32.v i in
  let pi = Seq.index r.base j in
  change_equal_slprop (vptr p.ith_item) (vptr pi);
  write pi x;
  change_equal_slprop (vptr pi) (vptr p.ith_item);
  pack_ith _ p r2;
  intro_varray _ r2 r

(* TODO: properly deallocate instead of just dropping the vprop *)
let free #t r =
  reveal_emp ();
  change_slprop_rel
    (varray r)
    (emp)
    (fun _ _ -> True)
    (fun m -> intro_emp m)
