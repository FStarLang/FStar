module FStar.MG2

(*** The modifies clause *)

(* NOTE: aloc cannot be a member of the class, because of OCaml
   extraction. So it must be a parameter of the class instead. *)

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

module GSet = FStar.GSet

noeq
type cls (aloc: Type) : Type = | Cls:
  (aloc_includes: (
    aloc ->
    aloc ->
    GTot Type0
  )) ->
  (aloc_includes_refl: (
    (x: aloc) ->
    Lemma
    (aloc_includes x x)
  )) ->
  (aloc_includes_trans: (
    (x1: aloc) ->
    (x2: aloc) ->
    (x3: aloc) ->
    Lemma
    (requires (aloc_includes x1 x2 /\ aloc_includes x2 x3))
    (ensures (aloc_includes x1 x3))
  )) ->
  (aloc_disjoint: (
    (x1: aloc) ->
    (x2: aloc) ->
    GTot Type0
  )) ->
  (aloc_disjoint_sym: (
    (x1: aloc) ->
    (x2: aloc) ->
    Lemma
    (aloc_disjoint x1 x2 <==> aloc_disjoint x2 x1)
  )) ->
  (aloc_disjoint_not_includes: (
    (x1: aloc) ->
    (x2: aloc) ->
    Lemma
    ((aloc_disjoint x1 x2 /\ aloc_includes x1 x2) ==> False)
  )) ->
  (aloc_disjoint_includes: (
    (larger1: aloc) ->
    (larger2: aloc) ->
    (smaller1: aloc) ->
    (smaller2: aloc) ->
    Lemma
    (requires (aloc_disjoint larger1 larger2 /\ larger1 `aloc_includes` smaller1 /\ larger2 `aloc_includes` smaller2))
    (ensures (aloc_disjoint smaller1 smaller2))
  )) ->
  (aloc_preserved: (
    aloc ->
    HS.mem ->
    HS.mem ->
    GTot Type0
  )) ->
  (aloc_preserved_refl: (
    (x: aloc) ->
    (h: HS.mem) ->
    Lemma
    (aloc_preserved x h h)
  )) ->
  (aloc_preserved_trans: (
    (x: aloc) ->
    (h1: HS.mem) ->
    (h2: HS.mem) ->
    (h3: HS.mem) ->
    Lemma
    (requires (aloc_preserved x h1 h2 /\ aloc_preserved x h2 h3))
    (ensures (aloc_preserved x h1 h3))
  )) ->
  (aloc_unused_in: (
    (x: aloc) ->
    (h: HS.mem) ->
    GTot Type0
  )) ->
  (aloc_unused_in_includes: (
    (greater: aloc) ->
    (lesser: aloc) ->
    (h: HS.mem) ->
    Lemma
    ((greater `aloc_includes` lesser /\ greater `aloc_unused_in` h) ==> lesser `aloc_unused_in` h)
  )) ->
  (aloc_unused_in_preserved: (
    (x: aloc) ->
    (h1: HS.mem) ->
    (h2: HS.mem) ->
    Lemma
    (requires (x `aloc_unused_in` h1))
    (ensures (aloc_preserved x h1 h2))
  )) ->
  cls aloc

[@must_erase_for_extraction]
val loc (#aloc: Type0) (c: cls aloc) : Tot Type0

val loc_of_aloc (#al: _) (#c: cls al) (b: al) : GTot (loc c)

val loc_none (#al: _) (#c: cls al) : Tot (loc c)

val loc_includes (#aloc: Type) (#c: cls aloc) (greater lesser: loc c) : GTot Type0

val loc_disjoint (#aloc: Type) (#c: cls aloc) (l1 l2: loc c) : GTot Type0

val loc_union (#aloc: Type) (#c: cls aloc) (l1 l2: loc c) : GTot (loc c)

val loc_disjoint_sym (#aloc: Type) (#c: cls aloc) (l1 l2: loc c) : Lemma
  (loc_disjoint l1 l2 <==> loc_disjoint l2 l1)
  [SMTPat (loc_disjoint l1 l2)]

val loc_disjoint_none_r
  (#aloc: Type) (#c: cls aloc)
  (s: loc c)
: Lemma
  (ensures (loc_disjoint s loc_none))

val loc_disjoint_union_r
  (#aloc: Type) (#c: cls aloc)
  (s s1 s2: loc c)
: Lemma
  (requires (loc_disjoint s s1 /\ loc_disjoint s s2))
  (ensures (loc_disjoint s (loc_union s1 s2)))

val loc_disjoint_includes
  (#aloc: Type) (#c: cls aloc)
  (p1 p2 p1' p2' : loc c)
: Lemma
  (requires (loc_includes p1 p1' /\ loc_includes p2 p2' /\ loc_disjoint p1 p2))
  (ensures (loc_disjoint p1' p2'))

val loc_disjoint_aloc_intro
  (#aloc: Type) (#c: cls aloc)
  (b1: aloc)
  (b2: aloc)
: Lemma
  (requires (c.aloc_disjoint b1 b2))
  (ensures (loc_disjoint (loc_of_aloc b1) (loc_of_aloc #_ #c b2)))

val loc_disjoint_aloc_elim
  (#aloc: Type) (#c: cls aloc)
  (b1: aloc)
  (b2: aloc)
: Lemma
  (requires (loc_disjoint (loc_of_aloc b1) (loc_of_aloc #_ #c b2)))
  (ensures (c.aloc_disjoint b1 b2))

val loc_includes_aloc_intro
  (#aloc: Type) (#c: cls aloc)
  (b1: aloc)
  (b2: aloc)
: Lemma
  (requires (c.aloc_includes b1 b2))
  (ensures (loc_includes (loc_of_aloc b1) (loc_of_aloc #_ #c b2)))

val loc_includes_aloc_elim
  (#aloc: Type) (#c: cls aloc)
  (b1: aloc)
  (b2: aloc)
: Lemma
  (requires (loc_includes (loc_of_aloc b1) (loc_of_aloc #_ #c b2)))
  (ensures (c.aloc_includes b1 b2))

val loc_includes_disjoint_elim
  (#al: _) (c: cls al)
  (l l1 l2: loc c)
: Lemma
  (requires ((l1 `loc_union` l2) `loc_includes` l /\ l1 `loc_disjoint` l /\ l1 `loc_disjoint` l2))
  (ensures (l2 `loc_includes` l))

val loc_union_idem
  (#aloc: Type) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_union s s == s)

val loc_union_comm
  (#aloc: Type) (#c: cls aloc)
  (s1 s2: loc c)
: Lemma
  (loc_union s1 s2 == loc_union s2 s1)

val loc_union_assoc
  (#aloc: Type) (#c: cls aloc)
  (s1 s2 s3: loc c)
: Lemma
  (loc_union s1 (loc_union s2 s3) == loc_union (loc_union s1 s2) s3)

val loc_union_loc_none_l
  (#aloc: Type) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_union loc_none s == s)

val loc_union_loc_none_r
  (#aloc: Type) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_union s loc_none == s)

val preserved (#al: _) (#c: cls al) (l: loc c) (h1 h2: HS.mem) : GTot Type0

val preserved_elim (#al: _) (#c: cls al) (l: loc c) (h1 h2: HS.mem) (x: al) : Lemma
  (requires (preserved l h1 h2 /\ l `loc_includes` loc_of_aloc x))
  (ensures (c.aloc_preserved x h1 h2))

val preserved_intro (#al: _) (#c: cls al) (l: loc c) (h1 h2: HS.mem)
  (f: (
    (x: al) ->
    Lemma
    (requires (l `loc_includes` loc_of_aloc x))
    (ensures (c.aloc_preserved x h1 h2))
  ))
: Lemma
  (preserved l h1 h2)

val modifies (#al: _) (#c: cls al) (l: loc c) (h1 h2: HS.mem) : GTot Type0

val loc_used_in (#al: _) (c: cls al) (h: HS.mem) : Tot (loc c)

val loc_unused_in (#al: _) (c: cls al) (h: HS.mem) : Tot (loc c)

val loc_includes_refl
  (#aloc: Type) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_includes s s)

val loc_includes_trans
  (#aloc: Type) (#c: cls aloc)
  (s1 s2 s3: loc c)
: Lemma
  (requires (loc_includes s1 s2 /\ loc_includes s2 s3))
  (ensures (loc_includes s1 s3))

val loc_includes_union_r
  (#aloc: Type) (#c: cls aloc)
  (s s1 s2: loc c)
: Lemma
  (requires (loc_includes s s1 /\ loc_includes s s2))
  (ensures (loc_includes s (loc_union s1 s2)))

val loc_includes_union_l
  (#aloc: Type) (#c: cls aloc)
  (s1 s2 s: loc c)
: Lemma
  (requires (loc_includes s1 s \/ loc_includes s2 s))
  (ensures (loc_includes (loc_union s1 s2) s))

val loc_includes_none
  (#aloc: Type) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_includes s loc_none)

val loc_includes_none_elim
  (#aloc: Type) (#c: cls aloc)
  (s: loc c)
: Lemma
  (requires (loc_includes loc_none s))
  (ensures (s == loc_none))


val modifies_aloc_elim
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
  ))

val modifies_refl
  (#aloc: Type) (#c: cls aloc)
  (s: loc c)
  (h: HS.mem)
: Lemma
  (modifies s h h)


val modifies_loc_includes
  (#aloc: Type) (#c: cls aloc)
  (s1: loc c)
  (h h': HS.mem)
  (s2: loc c)
: Lemma
  (requires (modifies s2 h h' /\ loc_includes s1 s2))
  (ensures (modifies s1 h h'))


val modifies_trans
  (#aloc: Type) (#c: cls aloc)
  (s12: loc c)
  (h1 h2: HS.mem)
  (s23: loc c)
  (h3: HS.mem)
: Lemma
  (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3))
  (ensures (modifies (loc_union s12 s23) h1 h3))

val loc_unused_in_used_in_disjoint (#al: Type) (c: cls al) (h: HS.mem) : Lemma
  (loc_unused_in c h `loc_disjoint` loc_used_in c h)

val modifies_aloc_intro'
  (#al: Type) (#c: cls al) (l: loc c) (h h' : HS.mem)
  (alocs: (
    (x: al) ->
    Lemma
    (requires (loc_disjoint l (loc_of_aloc x)))
    (ensures (c.aloc_preserved x h h'))
  ))
: Lemma
  (modifies l h h')

val modifies_aloc_intro
  (#al: Type) (#c: cls al) (z: al) (h h' : HS.mem)
  (alocs: (
    (x: al) ->
    Lemma
    (requires (c.aloc_disjoint x z))
    (ensures (c.aloc_preserved x h h'))
  ))
: Lemma
  (modifies (loc_of_aloc #_ #c z) h h')

val modifies_loc_none_intro
  (#al: Type) (#c: cls al)  (h h' : HS.mem)
  (alocs: (
    (x: al) ->
    Lemma
    (ensures (c.aloc_preserved x h h'))
  ))
: Lemma
  (modifies (loc_none #al #c) h h')


val modifies_only_used_in
  (#al: Type)
  (#c: cls al)
  (l: loc c)
  (h h' : HS.mem)
: Lemma
  (requires (modifies (loc_unused_in c h `loc_union` l) h h'))
  (ensures (modifies l h h'))

val aloc_unused_in_intro (#al: _) (c: cls al) (l: al) (h: HS.mem) : Lemma
  (requires (l `c.aloc_unused_in` h))
  (ensures (loc_unused_in c h `loc_includes` loc_of_aloc l))

val aloc_used_in_intro (#al: _) (c: cls al) (l: al) (h: HS.mem) : Lemma
  (requires (~ (l `c.aloc_unused_in` h)))
  (ensures (loc_used_in c h `loc_includes` loc_of_aloc l))
