module FStar.Classical

val give_witness (#a:Type) (_:a) :Lemma (ensures a)

val give_witness_from_squash (#a:Type) (_:squash a) :Lemma (ensures a)

val get_equality (#t:Type) (a b:t) :Pure (a == b) (requires (a == b)) (ensures (fun _ -> True))

val get_forall (#a:Type) (p:a -> GTot Type0) :Pure (forall (x:a). p x) (requires (forall (x:a). p x)) (ensures (fun _ -> True))

val impl_to_arrow (#a:Type0) (#b:Type0) (_:(a ==> b)) (_:squash a) :GTot (squash b)

val arrow_to_impl (#a:Type0) (#b:Type0) (_:(squash a -> GTot (squash b))) :GTot (a ==> b)

val forall_intro_gtot (#a:Type) (#p:(a -> GTot Type)) ($_:(x:a -> GTot (p x))) :Tot (squash (forall (x:a). p x))

val lemma_forall_intro_gtot (#a:Type) (#p:(a -> GTot Type)) ($_:(x:a -> GTot (p x))) :Lemma (forall (x:a). p x)

val gtot_to_lemma (#a:Type) (#p:(a -> GTot Type)) ($_:(x:a -> GTot (p x))) (x:a) :Lemma (p x)

val lemma_to_squash_gtot (#a:Type) (#p:(a -> GTot Type)) ($_:(x:a -> Lemma (p x))) (x:a) :GTot (squash (p x))

val forall_intro_squash_gtot (#a:Type) (#p:(a -> GTot Type)) ($_:(x:a -> GTot (squash (p x))))
  :Tot (squash (forall (x:a). p x))

//This one seems more generally useful than the one above
val forall_intro_squash_gtot_join (#a:Type) (#p:(a -> GTot Type)) ($_:(x:a -> GTot (squash (p x))))
  :Tot (forall (x:a). p x)

val forall_intro (#a:Type) (#p:(a -> GTot Type)) ($_:(x:a -> Lemma (p x))) :Lemma (forall (x:a). p x)

val forall_intro_with_pat (#a:Type) (#c: (x:a -> Type)) (#p:(x:a -> GTot Type0))
  ($pat: (x:a -> Tot (c x)))
  ($_: (x:a -> Lemma (p x)))
  :Lemma (forall (x:a).{:pattern (pat x)} p x)

val forall_intro_sub (#a:Type) (#p:(a -> GTot Type)) (_:(x:a -> Lemma (p x))) :Lemma (forall (x:a). p x)

val forall_intro_2 (#a:Type) (#b:(a -> Type)) (#p:(x:a -> b x -> GTot Type0)) ($_: (x:a -> y:b x -> Lemma (p x y)))
  :Lemma (forall (x:a) (y:b x). p x y)

val forall_intro_2_with_pat (#a:Type) (#b:(a -> Type)) (#c: (x:a -> y:b x -> Type)) (#p:(x:a -> b x -> GTot Type0))
  ($pat: (x:a -> y:b x -> Tot (c x y)))
  ($_: (x:a -> y:b x -> Lemma (p x y)))
  :Lemma (forall (x:a) (y:b x).{:pattern (pat x y)} p x y)

val forall_intro_3 (#a:Type) (#b:(a -> Type)) (#c:(x:a -> y:b x -> Type)) (#p:(x:a -> y:b x -> z:c x y -> Type0))
  ($_: (x:a -> y:b x -> z:c x y -> Lemma (p x y z)))
  : Lemma (forall (x:a) (y:b x) (z:c x y). p x y z)

val forall_intro_3_with_pat (#a:Type) (#b:(a -> Type)) (#c: (x:a -> y:b x -> Type)) (#d: (x:a -> y:b x -> z:c x y -> Type))
  (#p:(x:a -> y:b x -> z:c x y -> GTot Type0))
  ($pat: (x:a -> y:b x -> z:c x y -> Tot (d x y z)))
  ($_: (x:a -> y:b x -> z:c x y -> Lemma (p x y z)))
  :Lemma (forall (x:a) (y:b x) (z:c x y).{:pattern (pat x y z)} p x y z)

val forall_intro_4
  (#a:Type) (#b:(a -> Type)) (#c:(x:a -> y:b x -> Type)) (#d:(x:a -> y:b x -> z:c x y -> Type))
  (#p:(x:a -> y:b x -> z:c x y -> w:d x y z -> Type0))
  ($_: (x:a -> y:b x -> z:c x y -> w:d x y z -> Lemma (p x y z w)))
  : Lemma (forall (x:a) (y:b x) (z:c x y) (w:d x y z). p x y z w)

val exists_intro (#a:Type) (p:(a -> Type)) (witness:a)
  :Lemma (requires (p witness)) (ensures (exists (x:a). p x))

val forall_to_exists (#a:Type) (#p:(a -> Type)) (#r:Type) ($_:(x:a -> Lemma (p x ==> r)))
  :Lemma ((exists (x:a). p x) ==> r)

val forall_to_exists_2 (#a:Type) (#p:(a -> Type)) (#b:Type) (#q:(b -> Type)) (#r:Type)
  ($f:(x:a -> y:b -> Lemma ((p x /\ q y) ==> r)))
  :Lemma (((exists (x:a). p x) /\ (exists (y:b). q y)) ==> r)

val impl_intro_gtot (#p:Type0) (#q:Type0) ($_:p -> GTot q) :GTot (p ==> q)

val impl_intro (#p:Type0) (#q:Type0) ($_: p -> Lemma q) :Lemma (p ==> q)

val exists_elim (goal:Type) (#a:Type) (#p:(a -> Type)) (_:squash (exists (x:a). p x))
  (_:(x:a{p x} -> GTot (squash goal))) :Lemma goal

val move_requires (#a:Type) (#p:a -> Type) (#q:a -> Type)
  ($_:(x:a -> Lemma (requires (p x)) (ensures (q x)))) (x:a)
  :Lemma (p x ==> q x)

val forall_impl_intro (#a:Type) (#p:(a -> GTot Type)) (#q:(a -> GTot Type))
  ($_:(x:a -> (squash(p x)) -> Lemma (q x)))
  :Lemma (forall x. p x ==> q x)

val impl_intro_gen (#p:Type0) (#q:squash p -> Tot Type0) (_:squash p -> Lemma (q ()))
  :Lemma (p ==> q ())

val ghost_lemma (#a:Type) (#p:(a -> GTot Type0)) (#q:(a -> unit -> GTot Type0))
  ($_:(x:a -> Ghost unit (p x) (q x)))
  :Lemma (forall (x:a). p x ==> q x ())

val or_elim (#l #r:Type0) (#goal:(squash (l \/ r) -> Tot Type0))
  (hl:squash l -> Lemma (goal ()))
  (hr:squash r -> Lemma (goal ()))
  : Lemma ((l \/ r) ==> goal ())

val excluded_middle (p:Type) :Lemma (requires (True)) (ensures (p \/ ~p))
