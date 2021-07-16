module Steel.Pointer.RefSeq

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

let hp_varray2 r p = hp_of (varray1 r p)

let sel_varray2
  (#a: Type0)
  (r: array2 a)
  (p: perm)
: Tot (selector (Seq.lseq a (Seq.length r)) (hp_of (varray1 r p)))
= fun h -> sel_of (varray1 r p) h

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
    (fun _ -> True)
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
    (fun _ -> True)
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
: SteelGhost (Ghost.erased (ref t) `gpair` array2 t) opened
    (varray1 a p)
    (fun res -> vptrp (GPair?.fst res) p `star` varray1 (GPair?.snd res) p)
    (fun _ -> Seq.length a > 0)
    (fun h res h' ->
      Seq.length a > 0 /\
      begin let s = sel_varray1 a p h in
      h' (vptrp (GPair?.fst res) p) == Seq.head s /\
      Seq.tail s == sel_varray1 (GPair?.snd res) p h' /\
      Ghost.reveal a == Seq.cons (Ghost.reveal (GPair?.fst res)) (GPair?.snd res)
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
  let res : (Ghost.erased (ref t) `gpair` array2 t) = GPair r q in
  change_equal_slprop
    (vptrp (r) p `star` varray1 (q) p)
    (vptrp (GPair?.fst res) p `star` varray1 (GPair?.snd res) p);
  reveal_star (vptrp (GPair?.fst res) p) (varray1 (GPair?.snd res) p);
  res

#pop-options

let elim_vcons
  (#opened: _)
  (#t: Type)
  (a: array2 t)
  (p: perm)
: SteelGhost (Ghost.erased (ref t) `gpair` array2 t) opened
    (varray2 a p)
    (fun res -> vptrp (GPair?.fst res) p `star` varray2 (GPair?.snd res) p)
    (fun _ -> Seq.length a > 0)
    (fun h res h' ->
      Seq.length a > 0 /\
      begin let s = h (varray2 a p) in
      s == Seq.cons (h' (vptrp (GPair?.fst res) p)) (h' (varray2 (GPair?.snd res) p)) /\
      Ghost.reveal a == Seq.cons (Ghost.reveal (GPair?.fst res)) (GPair?.snd res)
      end
    )
=
  elim_varray2 a p;
  let res = elim_vcons1 a p in
  intro_varray2 (GPair?.snd res) p;
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
    (fun _ -> True)
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
    reveal_star_3 (vptrp (GPair?.fst hd_tl) p) (varray2 (GPair?.snd hd_tl) p) (varray2 a2 p); // FIXME: WHY WHY WHY?
    let tl' = vappend (GPair?.snd hd_tl) a2 p in
    let res = intro_vcons p (GPair?.fst hd_tl) tl' in
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

#push-options "--z3rlimit 64"  // 256 --fuel 6 --ifuel 6"
#restart-solver

let rec vsplit0
  (#opened: _)
  (#t: Type)
  (p: perm)
  (a: array2 t)
  (i: nat)
: SteelGhost (array2 t `gpair` array2 t) opened
    (varray2 a p)
    (fun res -> varray2 (GPair?.fst res) p `star` varray2 (GPair?.snd res) p)
    (fun _ -> i <= Seq.length a)
    (fun h res h' ->
      let s = h (varray2 a p) in
      i <= Seq.length a /\
      GPair?.fst res `Seq.equal` Seq.slice a 0 (i) /\
      GPair?.snd res `Seq.equal` Seq.slice a (i) (Seq.length a) /\
      h' (varray2 (GPair?.fst res) p) == Seq.slice s 0 (i) /\
      h' (varray2 (GPair?.snd res) p) `Seq.equal` Seq.slice s (i) (Seq.length a)
    )
    (decreases (i))
=
  seq_facts ();
  let g0 = gget (varray2 a p) in
  if i = 0
  then begin
    let n = intro_vnil t p in
    reveal_star (varray2 n p) (varray2 a p);
    let res = GPair n a in
    change_equal_slprop
      (varray2 n p `star` varray2 a p)
      (varray2 (GPair?.fst res) p `star` varray2 (GPair?.snd res) p);
    reveal_star (varray2 (GPair?.fst res) p) (varray2 (GPair?.snd res) p);
    res
  end else begin
    let hd_tl : (Ghost.erased (ref t) `gpair` array2 t) = elim_vcons a p in
    reveal_star (vptrp (GPair?.fst hd_tl) p) (varray2 (GPair?.snd hd_tl) p);
    let j = i - 1 in
    let g2_hd = gget (vptrp (GPair?.fst hd_tl) p) in
    let g2_tl = gget (varray2 (GPair?.snd hd_tl) p) in
    slice_cons_left (Ghost.reveal g2_hd) (Ghost.reveal g2_tl) i;
    slice_cons_right (Ghost.reveal g2_hd) (Ghost.reveal g2_tl) (i);
    let sl_sr = vsplit0 p (GPair?.snd hd_tl) j in
    reveal_star_3 (vptrp (GPair?.fst hd_tl) p) (varray2 (GPair?.fst sl_sr) p) (varray2 (GPair?.snd sl_sr) p); // FIXME: WHY WHY WHY?
    let sl = intro_vcons p (GPair?.fst hd_tl) (GPair?.fst sl_sr) in
    reveal_star (varray2 sl p) (varray2 (GPair?.snd sl_sr) p);
    let res = GPair sl (GPair?.snd sl_sr) in
    change_equal_slprop
      (varray2 sl p `star` varray2 (GPair?.snd sl_sr) p)
      (varray2 (GPair?.fst res) p `star` varray2 (GPair?.snd res) p);
    reveal_star (varray2 (GPair?.fst res) p) (varray2 (GPair?.snd res) p);
    res
  end

#pop-options

let vsplit
  #_ #t p a i
=
  let g = gget (varray2 a p) in
  Seq.lemma_split a (i);
  Seq.lemma_split #t (Ghost.reveal g) (i);
  vsplit0 p a i

#push-options "--z3rlimit 16"

let unpack_ith
  (#opened: _)
  (#t: Type)
  (p: perm)
  (a: array2 t)
  (i: nat)
: SteelGhost (ith_t t) opened
    (varray2 a p)
    (fun res -> varray2 res.ith_lhs p `star` vptrp res.ith_item p `star` varray2 res.ith_rhs p)
    (fun _ -> i < Seq.length a)
    (fun h res h' ->
      i < Seq.length a /\
      Ghost.reveal a == Seq.append res.ith_lhs (Seq.cons (Ghost.reveal res.ith_item) res.ith_rhs) /\
      can_be_split (varray2 res.ith_lhs p `star` vptrp res.ith_item p `star` varray2 res.ith_rhs p) (varray2 res.ith_lhs p) /\
      can_be_split (varray2 res.ith_lhs p `star` vptrp res.ith_item p `star` varray2 res.ith_rhs p) (vptrp res.ith_item p) /\
      can_be_split (varray2 res.ith_lhs p `star` vptrp res.ith_item p `star` varray2 res.ith_rhs p) (varray2 res.ith_lhs p) /\
      h (varray2 a p) == Seq.append (h' (varray2 res.ith_lhs p)) (Seq.cons (h' (vptrp res.ith_item p)) (h' (varray2 res.ith_rhs p))) /\
      Seq.length res.ith_lhs == i
    )
=
  let m = get #(varray2 a p) () in
  let rsplit = vsplit p a i in
  reveal_star (varray2 (GPair?.fst rsplit) p) (varray2 (GPair?.snd rsplit) p);
  let rcons = elim_vcons (GPair?.snd rsplit) p in
  reveal_star_3 (varray2 (GPair?.fst rsplit) p) (vptrp (GPair?.fst rcons) p) (varray2 (GPair?.snd rcons) p);
  let res = { ith_lhs = GPair?.fst rsplit; ith_item = GPair?.fst rcons; ith_rhs = GPair?.snd rcons } in
  change_equal_slprop
    (varray2 (GPair?.fst rsplit) p `star` vptrp (GPair?.fst rcons) p `star` varray2 (GPair?.snd rcons) p)
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
  change_equal_slprop (vptrp res.ith_item p) (vptrp (Ghost.reveal res.ith_item) p);
  reveal_star_3 (varray2 res.ith_lhs p) (vptrp (Ghost.reveal res.ith_item) p) (varray2 res.ith_rhs p);
  let rhs = intro_vcons p res.ith_item res.ith_rhs in
  reveal_star (varray2 res.ith_lhs p) (varray2 rhs p);
  let a' = vappend res.ith_lhs rhs p in
  change_equal_slprop (varray2 a' p) (varray2 a p)

let rec valloc
  (#t: Type)
  (i: nat)
  (x: t)
: Steel (array1 t)
    emp
    (fun res -> varray2 res full_perm)
    (fun _ -> True)
    (fun _ res h' ->
      Seq.length res == i /\
      h' (varray2 res full_perm) == Seq.create (i) x
    )
    (decreases (i))
=
  if i = 0
  then
    let res = intro_vnil t full_perm in
    assert (Seq.create 0 x `Seq.equal` Seq.empty);
    let res2 : array1 t = Seq.empty in
    change_equal_slprop
      (varray2 res full_perm)
      (varray2 res2 full_perm);
    return res2
  else begin
    let sq : squash (i <> 0) = () in
    let hd = Steel.Reference.malloc x in
    let j = i - 1 in
    assert (Seq.cons x (Seq.create (j) x) `Seq.equal` Seq.create (i) x);
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

#push-options "--z3rlimit 16"
#restart-solver

let rec vshare
  (#opened: _)
  (#t: Type)
  (a: array2 t)
  (p: perm)
: SteelGhost perm opened
    (varray2 a p)
    (fun res -> varray2 a res `star` varray2 a res)
    (fun _ -> True)
    (fun h res h' ->
      h' (varray2 a res) `Seq.equal` h (varray2 a p) /\
      res == half_perm p
    )
    (decreases (Seq.length a))
=
  if Seq.length a = 0
  then begin
    elim_nil a p;
    let h = half_perm p in
    let a1 = intro_vnil t h in
    assert (a1 `Seq.equal` a);
    change_equal_slprop
      (varray2 a1 h)
      (varray2 a h);
    let a2 = intro_vnil t h in
    assert (a2 `Seq.equal` a);
    change_equal_slprop
      (varray2 a2 h)
      (varray2 a h);
    h
  end else begin
    let g : Ghost.erased (Seq.lseq t (Seq.length a)) = gget (varray2 a p) in
    let hd_tl = elim_vcons a p in
    let g_hd : Ghost.erased t = gget (vptrp (GPair?.fst hd_tl) p) in
    let g_tl : Ghost.erased (Seq.lseq t (Seq.length (GPair?.snd hd_tl))) = gget (varray2 (GPair?.snd hd_tl) p) in
    assert (Ghost.reveal g == Seq.cons (Ghost.reveal g_hd) g_tl);
    share (GPair?.fst hd_tl);
    let g_hd_1 : Ghost.erased t = gget (vptrp (GPair?.fst hd_tl) _) in
    assert (Ghost.reveal g_hd_1 == Ghost.reveal g_hd);
    let h = vshare (GPair?.snd hd_tl) p in
    let g_tl_1 : Ghost.erased (Seq.lseq t (Seq.length (GPair?.snd hd_tl))) = gget (varray2 (GPair?.snd hd_tl) h) in
    assert (Ghost.reveal g_tl_1 == Ghost.reveal g_tl);
    change_equal_slprop
      (vptrp (GPair?.fst hd_tl) _)
      (vptrp (GPair?.fst hd_tl) h);
    let a1 = intro_vcons h (GPair?.fst hd_tl) (GPair?.snd hd_tl) in
    change_equal_slprop
      (varray2 a1 h)
      (varray2 a h);
    change_equal_slprop
      (vptrp (GPair?.fst hd_tl) _)
      (vptrp (GPair?.fst hd_tl) h);
    let a2 = intro_vcons h (GPair?.fst hd_tl) (GPair?.snd hd_tl) in
    change_equal_slprop
      (varray2 a2 h)
      (varray2 a h);
    noop ();
    h
  end

let rec vgather
  (#opened: _)
  (#t: Type)
  (a: array2 t)
  (p1 p2: perm)
: SteelGhost perm opened
    (varray2 a p1 `star` varray2 a p2)
    (fun res -> varray2 a res)
    (fun _ -> True)
    (fun h res h' ->
      h' (varray2 a res) `Seq.equal` h (varray2 a p1) /\
      h' (varray2 a res) `Seq.equal` h (varray2 a p2) /\
      res == p1 `sum_perm` p2
    )
    (decreases (Seq.length a))
=
  if Seq.length a = 0
  then begin
    elim_nil a p1;
    elim_nil a p2;
    let p = p1 `sum_perm` p2 in
    let a' = intro_vnil t p in
    assert (a' `Seq.equal` a);
    change_equal_slprop
      (varray2 a' p)
      (varray2 a p);
    p
  end else begin
    let hd_tl_1 = elim_vcons a p1 in
    let g_hd_1 : Ghost.erased t = gget (vptrp (GPair?.fst hd_tl_1) p1) in
    let g_tl_1 : Ghost.erased (Seq.lseq t (Seq.length (GPair?.snd hd_tl_1))) = gget (varray2 (GPair?.snd hd_tl_1) p1) in
    let hd_tl_2 = elim_vcons a p2 in
    Seq.lemma_cons_inj #(ref t) (GPair?.fst hd_tl_1) (GPair?.fst hd_tl_2) (GPair?.snd hd_tl_1) (GPair?.snd hd_tl_2);
    change_equal_slprop
      (vptrp (GPair?.fst hd_tl_2) p2)
      (vptrp (GPair?.fst hd_tl_1) p2);
    let g_hd_2 : Ghost.erased t = gget (vptrp (GPair?.fst hd_tl_1) p2) in
    let p = gather_gen (GPair?.fst hd_tl_1) p1 p2 in
    let g_hd : Ghost.erased t = gget (vptrp (GPair?.fst hd_tl_1) p) in
    assert (Ghost.reveal g_hd == Ghost.reveal g_hd_1);
    assert (Ghost.reveal g_hd == Ghost.reveal g_hd_2);
    change_equal_slprop
      (varray2 (GPair?.snd hd_tl_2) p2)
      (varray2 (GPair?.snd hd_tl_1) p2);
    let g_tl_2 : Ghost.erased (Seq.lseq t (Seq.length (GPair?.snd hd_tl_1))) = gget (varray2 (GPair?.snd hd_tl_1) p2) in
    let p' = vgather (GPair?.snd hd_tl_1) p1 p2 in
    change_equal_slprop
      (varray2 (GPair?.snd hd_tl_1) p')
      (varray2 (GPair?.snd hd_tl_1) p);
    let g_tl : Ghost.erased (Seq.lseq t (Seq.length (GPair?.snd hd_tl_1))) = gget (varray2 (GPair?.snd hd_tl_1) p) in
    assert (Ghost.reveal g_tl == Ghost.reveal g_tl_1);
    assert (Ghost.reveal g_tl == Ghost.reveal g_tl_2);
    let a' = intro_vcons p (GPair?.fst hd_tl_1) (GPair?.snd hd_tl_1) in
    change_equal_slprop
      (varray2 a' p)
      (varray2 a p);
    p
  end

let rec vfree
  x
=
  if Seq.length x = 0
  then begin
    noop ();
    elim_nil x full_perm
  end else begin
    let hd_tl = elim_vcons x full_perm in
    let hd = Seq.head x in
    let tl = Seq.tail x in
    Seq.lemma_cons_inj (Ghost.reveal (GPair?.fst hd_tl)) hd (GPair?.snd hd_tl) tl;
    change_equal_slprop
      (vptrp (GPair?.fst hd_tl) full_perm)
      (vptrp hd full_perm);
    free hd;
    change_equal_slprop
      (varray2 (GPair?.snd hd_tl) full_perm)
      (varray2 tl full_perm);
    vfree tl
  end
