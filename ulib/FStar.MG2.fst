module FStar.MG2

(*** The modifies clause *)

(* NOTE: aloc cannot be a member of the class, because of OCaml
   extraction. So it must be a parameter of the class instead. *)

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

module GSet = FStar.GSet

let loc (#aloc: Type0) (c: cls aloc) = (s: GSet.set aloc { forall (greater lesser: aloc) . {:pattern (greater `GSet.mem` s); (greater `c.aloc_includes` lesser)} greater `GSet.mem` s /\ greater `c.aloc_includes` lesser ==> lesser `GSet.mem` s })

let loc_of_aloc #al (#c: cls al) (b: al) : GTot (loc c) =
  Classical.forall_intro_3 (fun x y -> Classical.move_requires (c.aloc_includes_trans x y));
  GSet.comprehend (fun x -> FStar.StrongExcludedMiddle.strong_excluded_middle (b `c.aloc_includes` x))

let loc_none #al (#c: cls al) : Tot (loc c) =
  GSet.empty

let loc_includes (#aloc: Type) (#c: cls aloc) (greater lesser: loc c) : GTot Type0 =
  forall (x_lesser: aloc) . {:pattern (x_lesser `GSet.mem` lesser)} x_lesser `GSet.mem` lesser ==> (exists (x_greater: aloc) . {:pattern (x_greater `GSet.mem` greater)} x_greater `GSet.mem` greater /\ x_greater `c.aloc_includes` x_lesser)

let loc_disjoint (#aloc: Type) (#c: cls aloc) (l1 l2: loc c) : GTot Type0 =
  forall (x1 x2: aloc) . {:pattern (GSet.mem x1 l1); (GSet.mem x2 l2)} (GSet.mem x1 l1 /\ GSet.mem x2 l2) ==> c.aloc_disjoint x1 x2

let loc_union (#aloc: Type) (#c: cls aloc) (l1 l2: loc c) : GTot (loc c) =
  l1 `GSet.union` l2

let loc_disjoint_sym (#aloc: Type) (#c: cls aloc) (l1 l2: loc c) : Lemma
  (loc_disjoint l1 l2 <==> loc_disjoint l2 l1)
  [SMTPat (loc_disjoint l1 l2)]
= Classical.forall_intro_2 c.aloc_disjoint_sym

let loc_disjoint_none_r
  (#aloc: Type) (#c: cls aloc)
  (s: loc c)
: Lemma
  (ensures (loc_disjoint s loc_none)) =
  ()

let loc_disjoint_union_r
  (#aloc: Type) (#c: cls aloc)
  (s s1 s2: loc c)
: Lemma
  (requires (loc_disjoint s s1 /\ loc_disjoint s s2))
  (ensures (loc_disjoint s (loc_union s1 s2))) =
  ()

let loc_disjoint_includes
  (#aloc: Type) (#c: cls aloc)
  (p1 p2 p1' p2' : loc c)
: Lemma
  (requires (loc_includes p1 p1' /\ loc_includes p2 p2' /\ loc_disjoint p1 p2))
  (ensures (loc_disjoint p1' p2')) =
  ()

let loc_disjoint_aloc_intro
  (#aloc: Type) (#c: cls aloc)
  (b1: aloc)
  (b2: aloc)
: Lemma
  (requires (c.aloc_disjoint b1 b2))
  (ensures (loc_disjoint (loc_of_aloc b1) (loc_of_aloc #_ #c b2))) =
  Classical.forall_intro_4 (fun x y z -> Classical.move_requires (c.aloc_disjoint_includes x y z))

let loc_disjoint_aloc_elim
  #aloc #c b1 b2
= Classical.forall_intro c.aloc_includes_refl;
  assert (b1 `GSet.mem` loc_of_aloc #_ #c b1);
  assert (b2 `GSet.mem` loc_of_aloc #_ #c b2)

let loc_includes_aloc_intro
  #aloc #c b1 b2
= Classical.forall_intro_3 (fun x y -> Classical.move_requires (c.aloc_includes_trans x y));
  Classical.forall_intro c.aloc_includes_refl;
  assert (b1 `GSet.mem` loc_of_aloc #_ #c b1)

let loc_includes_aloc_elim
  #aloc #c b1 b2
= Classical.forall_intro c.aloc_includes_refl;
  assert (b1 `GSet.mem` loc_of_aloc #_ #c b1);
  assert (b2 `GSet.mem` loc_of_aloc #_ #c b2)

let loc_includes_disjoint_elim
  #al (c: cls al)
  (l l1 l2: loc c)
: Lemma
  (requires ((l1 `loc_union` l2) `loc_includes` l /\ l1 `loc_disjoint` l /\ l1 `loc_disjoint` l2))
  (ensures (l2 `loc_includes` l))
= let f
    (x: al)
    (y: al)
  : Lemma
    (requires (GSet.mem x l /\ GSet.mem y (l1 `loc_union` l2) /\ y `c.aloc_includes` x))
    (ensures (GSet.mem y l2))
  = if GSet.mem y l2
    then ()
    else
      let g
        ()
      : Lemma
        (requires (GSet.mem y l1))
        (ensures False)
      = assert (l `loc_disjoint` l1);
        c.aloc_disjoint_not_includes y x
      in
      Classical.move_requires g ()
  in
  Classical.forall_intro_2 (fun x -> Classical.move_requires (f x))

let loc_union_idem
  (#aloc: Type) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_union s s == s) =
  assert (loc_union s s `GSet.equal` s)

let loc_union_comm
  (#aloc: Type) (#c: cls aloc)
  (s1 s2: loc c)
: Lemma
  (loc_union s1 s2 == loc_union s2 s1) =
  assert (loc_union s1 s2 `GSet.equal` loc_union s2 s1)

let loc_union_assoc
  (#aloc: Type) (#c: cls aloc)
  (s1 s2 s3: loc c)
: Lemma
  (loc_union s1 (loc_union s2 s3) == loc_union (loc_union s1 s2) s3) =
  assert (loc_union s1 (loc_union s2 s3) `GSet.equal` loc_union (loc_union s1 s2) s3)

let loc_union_loc_none_l
  (#aloc: Type) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_union loc_none s == s) =
  assert (loc_union loc_none s `GSet.equal` s)

let loc_union_loc_none_r
  (#aloc: Type) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_union s loc_none == s) =
  assert (loc_union s loc_none `GSet.equal` s)

let preserved #al (#c: cls al) (l: loc c) (h1 h2: HS.mem) : GTot Type0 =
  forall (x: al) . {:pattern (x `GSet.mem` l)} x `GSet.mem` l ==> c.aloc_preserved x h1 h2

let preserved_elim
  #al #c l h1 h2 x
= Classical.forall_intro c.aloc_includes_refl;
  assert (x `GSet.mem` loc_of_aloc #_ #c x)

let preserved_intro
  #al #c l h1 h2 f
= Classical.forall_intro (Classical.move_requires f)

let modifies #al (#c: cls al) (l: loc c) (h1 h2: HS.mem) : GTot Type0 =
  forall (l' : loc c) . {:pattern (l' `loc_disjoint` l)} l' `loc_disjoint` l ==> preserved l' h1 h2


let loc_used_in #al (c: cls al) (h: HS.mem) : Tot (loc c) =
  admit()


let loc_unused_in #al (c: cls al) (h: HS.mem) : Tot (loc c) =
  Classical.forall_intro_3 c.aloc_unused_in_includes;
  GSet.comprehend (fun x -> FStar.StrongExcludedMiddle.strong_excluded_middle (x `c.aloc_unused_in` h))

let loc_includes_refl
  (#aloc: Type) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_includes s s) =
  Classical.forall_intro c.aloc_includes_refl

let loc_includes_trans
  (#aloc: Type) (#c: cls aloc)
  (s1 s2 s3: loc c)
: Lemma
  (requires (loc_includes s1 s2 /\ loc_includes s2 s3))
  (ensures (loc_includes s1 s3)) =
  Classical.forall_intro_3 (fun x y -> Classical.move_requires (c.aloc_includes_trans x y))

let loc_includes_union_r
  (#aloc: Type) (#c: cls aloc)
  (s s1 s2: loc c)
: Lemma
  (requires (loc_includes s s1 /\ loc_includes s s2))
  (ensures (loc_includes s (loc_union s1 s2))) =
  ()

let loc_includes_union_l
  (#aloc: Type) (#c: cls aloc)
  (s1 s2 s: loc c)
: Lemma
  (requires (loc_includes s1 s \/ loc_includes s2 s))
  (ensures (loc_includes (loc_union s1 s2) s)) =
  Classical.forall_intro c.aloc_includes_refl;
  assert (forall x . x `GSet.mem` s1 ==> x `GSet.mem` (loc_union s1 s2));
  assert (forall x . x `GSet.mem` s2 ==> x `GSet.mem` (loc_union s1 s2));
  Classical.move_requires (loc_includes_trans (loc_union s1 s2) s1) s;
  Classical.move_requires (loc_includes_trans (loc_union s1 s2) s2) s

let loc_includes_none
  (#aloc: Type) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_includes s loc_none) =
  ()

let loc_includes_none_elim
  (#aloc: Type) (#c: cls aloc)
  (s: loc c)
: Lemma
  (requires (loc_includes loc_none s))
  (ensures (s == loc_none)) =
  assert (s `GSet.equal` loc_none #_ #c)


let modifies_aloc_elim
  (#aloc: Type) (#c: cls aloc)
  (b: aloc)
  (p: loc c)
  (h h': HS.mem)
: Lemma
  (requires (
    loc_disjoint (loc_of_aloc b) p /\
    modifies p h h'
  ))
  (ensures (
    c.aloc_preserved b h h'
  )) =
  Classical.forall_intro c.aloc_includes_refl;
  assert (b `GSet.mem` (loc_of_aloc #_ #c b))

let modifies_refl
  (#aloc: Type) (#c: cls aloc)
  (s: loc c)
  (h: HS.mem)
: Lemma
  (modifies s h h) =
  Classical.forall_intro_2 c.aloc_preserved_refl


let modifies_loc_includes
  (#aloc: Type) (#c: cls aloc)
  (s1: loc c)
  (h h': HS.mem)
  (s2: loc c)
: Lemma
  (requires (modifies s2 h h' /\ loc_includes s1 s2))
  (ensures (modifies s1 h h')) =
  Classical.forall_intro (loc_includes_refl #_ #c);
  Classical.forall_intro_4 (fun x y z -> Classical.move_requires (loc_disjoint_includes #_ #c x y z))


let modifies_trans
  (#aloc: Type) (#c: cls aloc)
  (s12: loc c)
  (h1 h2: HS.mem)
  (s23: loc c)
  (h3: HS.mem)
: Lemma
  (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3))
  (ensures (modifies (loc_union s12 s23) h1 h3)) =
  loc_includes_refl s12;
  loc_includes_union_l s12 s23 s12;
  modifies_loc_includes (loc_union s12 s23) h1 h2 s12;
  loc_includes_refl s23;
  loc_includes_union_l s12 s23 s23;
  modifies_loc_includes (loc_union s12 s23) h2 h3 s23;
  Classical.forall_intro_4 (fun x y z -> Classical.move_requires (c.aloc_preserved_trans x y z))

let loc_unused_in_used_in_disjoint (#al: Type) (c: cls al) (h: HS.mem) : Lemma
  (loc_unused_in c h `loc_disjoint` loc_used_in c h) =
  admit()

let modifies_aloc_intro'
  (#al: Type) (#c: cls al) (l: loc c) (h h' : HS.mem)
  (alocs: (
    (x: al) ->
    Lemma
    (requires (loc_disjoint l (loc_of_aloc x)))
    (ensures (c.aloc_preserved x h h'))
  ))
: Lemma
  (modifies l h h')
=
  let f
    (l': loc c)
  : Lemma
    (requires (l' `loc_disjoint` l))
    (ensures (preserved l' h h'))
  = let g
      (x: al)
    : Lemma
      (requires (x `GSet.mem` l'))
      (ensures (c.aloc_preserved x h h'))
    = alocs x
    in
    Classical.forall_intro (Classical.move_requires g)
  in
  Classical.forall_intro (Classical.move_requires f)

let modifies_aloc_intro
  (#al: Type) (#c: cls al) (z: al) (h h' : HS.mem)
  (alocs: (
    (x: al) ->
    Lemma
    (requires (c.aloc_disjoint x z))
    (ensures (c.aloc_preserved x h h'))
  ))
: Lemma
  (modifies (loc_of_aloc #_ #c z) h h') =
  modifies_aloc_intro' #_ #c (loc_of_aloc z) h h' (fun x ->
    c.aloc_includes_refl z;
    assert (z `GSet.mem` loc_of_aloc #_ #c z);
    c.aloc_includes_refl x;
    assert (x `GSet.mem` loc_of_aloc #_ #c x);
    alocs x
  )

let modifies_loc_none_intro
  (#al: Type) (#c: cls al)  (h h' : HS.mem)
  (alocs: (
    (x: al) ->
    Lemma
    (ensures (c.aloc_preserved x h h'))
  ))
: Lemma
  (modifies (loc_none #al #c) h h')
= admit()

let modifies_only_used_in
  (#al: Type)
  (#c: cls al)
  (l: loc c)
  (h h' : HS.mem)
: Lemma
  (requires (modifies (loc_unused_in c h `loc_union` l) h h'))
  (ensures (modifies l h h')) =
  modifies_aloc_intro' l h h' (fun x ->
    admit();//c.aloc_used_in_or_unused_in x h;
    //Classical.forall_intro_2 (fun x y -> c.aloc_used_in_unused_in_disjoint x y h);
    Classical.forall_intro c.aloc_includes_refl;
    c.aloc_disjoint_not_includes x x;
    (*if StrongExcludedMiddle.strong_excluded_middle (x `c.aloc_used_in` h) then begin
      let f
        (x' y' : al)
      : Lemma
        (requires (x `c.aloc_includes` x' /\ y' `c.aloc_unused_in` h))
        (ensures (y' `c.aloc_disjoint` x'))
      = c.aloc_disjoint_sym x y' ;
        c.aloc_disjoint_includes y' x y' x'
      in
      Classical.forall_intro_2 (fun x -> Classical.move_requires (f x));
      assert (loc_unused_in c h `loc_disjoint` loc_of_aloc x);
      assert ((loc_unused_in c h `loc_union` l) `loc_disjoint` loc_of_aloc x);
      assert (x `GSet.mem` loc_of_aloc #_ #c x)
    end else begin
      c.aloc_unused_in_preserved x h h'
    end*)
    ()
  )

let aloc_unused_in_intro #al (c: cls al) (l: al) (h: HS.mem) : Lemma
  (requires (l `c.aloc_unused_in` h))
  (ensures (loc_unused_in c h `loc_includes` loc_of_aloc l))
  =
  let f
    (x: al)
  : Lemma
    (requires (l `c.aloc_includes` x))
    (ensures (x `GSet.mem` loc_unused_in c h))
  = c.aloc_unused_in_includes l x h
  in
  Classical.forall_intro (Classical.move_requires f);
  Classical.forall_intro c.aloc_includes_refl

let aloc_used_in_intro (#al: _) (c: cls al) (l: al) (h: HS.mem) : Lemma
  (requires (~ (l `c.aloc_unused_in` h)))
  (ensures (loc_used_in c h `loc_includes` loc_of_aloc l))
  = admit()
