module Steel.ST.Stick
open Steel.ST.Util

(* This is not the "magic wand", so I renamed it "stick." This may be close to Iris's "view shifts." *)

val stick
  (hyp concl: vprop)
: Tot vprop

val stick_elim
  (#opened: _)
  (hyp concl: vprop)
: STGhostT unit opened
    ((hyp `stick` concl) `star` hyp)
    (fun _ -> concl)

val stick_intro
  (#opened: _)
  (hyp concl: vprop)
  (v: vprop)
  (f_elim: (
    (opened: inames) ->
    STGhostT unit opened
    (v `star` hyp)
    (fun _ -> concl)
  ))
: STGhostT unit opened
    v
    (fun _ -> hyp `stick` concl)

let stick_uncurry
  (#opened: _)
  (h1 h2 c: vprop)
: STGhostT unit opened
    (h1 `stick` (h2 `stick` c))
    (fun _ -> (h1 `star` h2) `stick` c)
= stick_intro (h1 `star` h2) c (h1 `stick` (h2 `stick` c)) (fun _ ->
    stick_elim h1 (h2 `stick` c);
    stick_elim h2 c
  )

let stick_curry
  (#opened: _)
  (h1 h2 c: vprop)
: STGhostT unit opened
    ((h1 `star` h2) `stick` c)
    (fun _ -> (h1 `stick` (h2 `stick` c)))
= stick_intro h1 (h2 `stick` c) ((h1 `star` h2) `stick` c) (fun _ ->
    stick_intro h2 c (((h1 `star` h2) `stick` c) `star` h1) (fun _ ->
    stick_elim (h1 `star` h2) c
  ))

let stick_join
  (#opened: _)
  (h1 c1 h2 c2: vprop)
: STGhostT unit opened
    ((h1 `stick` c1) `star` (h2 `stick` c2))
    (fun _ -> (h1 `star` h2) `stick` (c1 `star` c2))
= stick_intro (h1 `star` h2) (c1 `star` c2) ((h1 `stick` c1) `star` (h2 `stick` c2)) (fun _ ->
    stick_elim h1 c1;
    stick_elim h2 c2
  )

let stick_trans
  (#opened: _)
  (v1 v2 v3: vprop)
: STGhostT unit opened
    ((v1 `stick` v2) `star` (v2 `stick` v3))
    (fun _ -> v1 `stick` v3)
= stick_intro v1 v3 ((v1 `stick` v2) `star` (v2 `stick` v3)) (fun _ ->
    stick_elim v1 v2;
    stick_elim v2 v3
  )

let adjoint_stick_elim
  (#opened: _)
  (p q r: vprop)
  (f: (
    (opened: _) ->
    STGhostT unit opened
    p (fun _ -> q `stick` r)
  ))
: STGhostT unit opened
    (p `star` q)
    (fun _ -> r)
= f _;
  stick_elim q r

let adjoint_stick_intro
  (#opened: _)
  (p q r: vprop)
  (f: (
    (opened: _) ->
    STGhostT unit opened
    (p `star` q) (fun _ -> r)
  ))
: STGhostT unit opened
    p
    (fun _ -> q `stick` r)
= stick_intro q r p (fun _ ->
    f _
  )

(* The magic wand is a stick (but not the converse) *)

let wand_is_stick
  (#opened: _)
  (wand: (vprop -> vprop -> vprop))
  (s1 s2: vprop)
  (interp_wand:
    (h: mem) ->
    Lemma
    (interp (hp_of (s1 `wand` s2)) h <==> (forall (h1:mem) . (disjoint h h1 /\ interp (hp_of s1) h1) ==> interp (hp_of s2) (h `join` h1)))
  )
: STGhostT unit opened
  (s1 `wand` s2)
  (fun _ -> s1 `stick` s2)
= stick_intro s1 s2 (s1 `wand` s2) (fun _ ->
    weaken (s1 `star` (s1 `wand` s2)) s2 (fun m ->
    interp_star (hp_of s1) (hp_of (s1 `wand` s2)) m;
    let m1 = FStar.IndefiniteDescription.indefinite_description_ghost mem (fun m1 -> exists m2 . disjoint m1 m2 /\ interp (hp_of s1) m1 /\ interp (hp_of (s1 `wand` s2)) m2 /\ join m1 m2 == m) in
    let m2 = FStar.IndefiniteDescription.indefinite_description_ghost mem (fun m2 ->
    disjoint m1 m2 /\ interp (hp_of s1) m1 /\ interp (hp_of (s1 `wand` s2)) m2 /\ join m1 m2 == m) in
    interp_wand m2;
    assert (interp (hp_of s2) (m2 `join` m1));
    join_commutative m2 m1
  ))
