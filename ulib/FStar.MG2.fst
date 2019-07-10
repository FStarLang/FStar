module FStar.MG2

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

(*** The modifies clause *)

(* NOTE: aloc cannot be a member of the class, because of OCaml
   extraction. So it must be a parameter of the class instead. *)

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
  cls aloc

module GSet = FStar.GSet

type loc (#aloc: Type) (c: cls aloc) = (s: GSet.set aloc { forall (greater lesser: aloc) . {:pattern (greater `GSet.mem` s); (greater `c.aloc_includes` lesser)} greater `GSet.mem` s /\ greater `c.aloc_includes` lesser ==> lesser `GSet.mem` s })

let loc_includes (#aloc: Type) (#c: cls aloc) (greater lesser: loc c) : GTot Type0 =
  forall (x_lesser: aloc) . {:pattern (x_lesser `GSet.mem` lesser)} x_lesser `GSet.mem` lesser ==> (exists (x_greater: aloc) . {:pattern (x_greater `GSet.mem` greater)} x_greater `GSet.mem` greater /\ x_greater `c.aloc_includes` x_lesser)

let loc_disjoint (#aloc: Type) (#c: cls aloc) (l1 l2: loc c) : GTot Type0 =
  forall (x1 x2: aloc) . {:pattern (GSet.mem x1 l1); (GSet.mem x2 l2)} (GSet.mem x1 l1 /\ GSet.mem x2 l2) ==> c.aloc_disjoint x1 x2

let loc_disjoint_sym (#aloc: Type) (#c: cls aloc) (l1 l2: loc c) : Lemma
  (loc_disjoint l1 l2 <==> loc_disjoint l2 l1)
  [SMTPat (loc_disjoint l1 l2)]
= Classical.forall_intro_2 c.aloc_disjoint_sym

let loc_union (#aloc: Type) (#c: cls aloc) (l1 l2: loc c) : GTot (loc c) =
  l1 `GSet.union` l2

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
