module PulseCore.HeapSig
open FStar.Ghost
open FStar.PCM
module H2 = PulseCore.Heap2
module ST = PulseCore.HoareStateMonad
module CM = FStar.Algebra.CommMonoid

let star_commutative #h p q =
  introduce forall c. h.interp (h.star p q) c <==> h.interp (h.star q p) c with (
    h.star_equiv p q c;
    h.star_equiv q p c;
    Classical.forall_intro_2 h.sep.disjoint_sym;
    Classical.forall_intro_2 h.sep.join_commutative
  );
  h.slprop_extensionality (h.star p q) (h.star q p)

let star_associative' (#h: heap_sig) (p q r: h.slprop) (m: h.mem { h.interp (h.star p (h.star q r)) m }) :
    squash (h.interp (h.star (h.star p q) r) m) =
  h.star_equiv p (h.star q r) m;
  let m1 = IndefiniteDescription.indefinite_description_ghost _ fun m1 -> exists m23.
    h.sep.disjoint m1 m23 /\ m == h.sep.join m1 m23 /\ h.interp p m1 /\ h.interp (h.star q r) m23 in
  let m23 = IndefiniteDescription.indefinite_description_ghost _ fun m23 ->
    h.sep.disjoint m1 m23 /\ m == h.sep.join m1 m23 /\ h.interp p m1 /\ h.interp (h.star q r) m23 in
  h.star_equiv q r m23;
  let m2 = IndefiniteDescription.indefinite_description_ghost _ fun m2 -> exists m3.
    h.sep.disjoint m2 m3 /\ m23 == h.sep.join m2 m3 /\ h.interp q m2 /\ h.interp r m3 in
  let m3 = IndefiniteDescription.indefinite_description_ghost _ fun m3 ->
    h.sep.disjoint m2 m3 /\ m23 == h.sep.join m2 m3 /\ h.interp q m2 /\ h.interp r m3 in
  h.sep.join_associative m1 m2 m3;
  let m12 = h.sep.join m1 m2 in
  h.star_equiv p q m12;
  h.star_equiv (h.star p q) r m

let star_associative #h p q r =
  introduce forall m. h.interp (h.star p (h.star q r)) m <==> h.interp (h.star (h.star p q) r) m with (
    introduce h.interp (h.star p (h.star q r)) m ==> h.interp (h.star (h.star p q) r) m with _. (
      star_associative' p q r m
    );
    introduce h.interp (h.star (h.star p q) r) m ==> h.interp (h.star p (h.star q r)) m with _. (
      star_commutative (h.star p q) r;
      star_commutative p q;
      star_commutative p (h.star q r);
      star_commutative q r;
      star_associative' r q p m
    )
  );
  h.slprop_extensionality (h.star p (h.star q r)) (h.star (h.star p q) r)

let emp_trivial (h:heap_sig u#a)
: Lemma (forall m. h.interp h.emp m)
= h.pure_true_emp ();
  FStar.Classical.forall_intro (h.pure_interp True)

let exists_ #h #a p = h.as_slprop (fun m -> exists (x:a). h.interp (p x) m)

let interp_exists (#h:heap_sig u#h) (#a:Type u#a) (p: a -> GTot h.slprop)
: Lemma (forall m. h.interp (exists_ p) m <==> (exists x. h.interp (p x) m))
= h.interp_as (fun m -> exists (x:a). h.interp (p x) m)

let exists_extensionality (#h:heap_sig u#h) (#a:Type u#a) (p q:a -> GTot h.slprop)
: Lemma
    (requires forall x. p x == q x)
    (ensures exists_ p == exists_ q)
= interp_exists #h #a p;
  interp_exists #h #a q;
  h.slprop_extensionality (exists_ p) (exists_ q)

let erase_cm (#a:Type) (c:CM.cm a)
: CM.cm (erased a)
= CM.CM (hide c.unit)
        (fun x y -> hide (c.mult (reveal x) (reveal y)))
        (fun x -> c.identity (reveal x))
        (fun x y z -> c.associativity (reveal x) (reveal y) (reveal z))
        (fun x y -> c.commutativity (reveal x) (reveal y))

let cm_slprop (hs:heap_sig u#h) 
: c:CM.cm (hs.slprop) { c.unit == hs.emp /\ c.mult == hs.star }
= CM.CM hs.emp
        hs.star
        (fun x -> hs.emp_unit x; star_commutative x hs.emp)
        star_associative star_commutative

let cm_e_slprop (hs:heap_sig u#h) = erase_cm (cm_slprop hs)

let ac_lemmas (h:heap_sig u#a)
: Lemma (
    (forall p q r. (p `h.star` q) `h.star` r == p `h.star` (q `h.star` r)) /\
    (forall p q. p `h.star` q == q `h.star` p) /\
    (forall p. p `h.star` h.emp == p)
)
= FStar.Classical.forall_intro_3 (star_associative #h);
  FStar.Classical.forall_intro_2 (star_commutative #h);
  FStar.Classical.forall_intro h.emp_unit

let frame
      (#h:heap_sig u#h)
      (#opened_invariants:inames h)
      (#maybe_ghost:bool)
      (#a:Type u#a)
      (#pre:h.slprop)
      (#post:a -> GTot h.slprop)
      (frame:h.slprop)
      ($f:_action_except h a maybe_ghost opened_invariants pre post)
: _action_except h a maybe_ghost opened_invariants (pre `h.star` frame) (fun x -> post x `h.star` frame)
= fun frame' m -> ac_lemmas h; f (frame `h.star` frame') m

let witness_exists_lemma (#h:heap_sig u#h) (#a:Type u#a)
             (p:a -> GTot h.slprop) (frame:h.slprop) (m:h.mem { interpret (exists_ p `h.star` frame) m })
: x:erased a { interpret (p x `h.star` frame) m }
= h.star_equiv (exists_ p) frame m;
  eliminate exists c0 c1.
    h.sep.disjoint c0 c1 /\
    m == h.sep.join c0 c1 /\
    h.interp (exists_ p) c0 /\
    h.interp frame c1
  returns (exists (x:a). interpret (p x `h.star` frame) m)
  with _ . (
    interp_exists p;
    eliminate exists x.
        h.interp (p x) c0
    returns _
    with _ . (
        h.star_equiv (p x) frame m
    )
  );
  FStar.IndefiniteDescription.indefinite_description_tot a (fun x -> interpret (p x `h.star` frame) m)

let witness_exists 
      (#h:heap_sig u#h)
      (#ex:inames h)
      (#a:Type u#a)
      (p:a -> GTot h.slprop)
: ghost_action_except h (erased a) ex
           (exists_ p)
           (fun x -> p x)
= fun frame m ->
    ac_lemmas h;
    let x = witness_exists_lemma p (frame `h.star` h.mem_invariant ex m) m in
    h.is_ghost_action_preorder ();
    x, m

let intro_exists_lemma
      (#h:heap_sig u#h) (#a:Type u#a)
      (p:a -> GTot h.slprop)
      (x:erased a)
      (frame:h.slprop)
      (m:h.mem { interpret (p x `h.star` frame) m })
: Lemma (interpret (exists_ p `h.star` frame) m)
= h.star_equiv (p x) frame m;
  interp_exists p;
  h.star_equiv (exists_ p) frame m

let intro_exists
      (#h:heap_sig u#h)
      (#opened_invariants:_)
      (#a:Type u#a)
      (p:a -> GTot h.slprop)
      (x:erased a)
: ghost_action_except h unit opened_invariants
      (p x)
      (fun _ -> exists_ p)
= fun frame m ->
    ac_lemmas h;
    intro_exists_lemma p x (frame `h.star` h.mem_invariant opened_invariants m) m;
    h.is_ghost_action_preorder ();
    (), m


module U = FStar.Universe
let lift_h_exists
      (#h:heap_sig u#h)
      (#opened_invariants:_)
      (#a:Type u#a)
      (p:a -> GTot h.slprop)
: ghost_action_except h unit opened_invariants
    (exists_ p)
    (fun _a -> exists_ #_ #(U.raise_t a) (lift_dom_ghost p))
= fun frame m ->
    ac_lemmas h;
    let x = witness_exists_lemma p (frame `h.star` h.mem_invariant opened_invariants m) m in
    intro_exists_lemma (lift_dom_ghost p) (U.raise_val (reveal x)) (frame `h.star` h.mem_invariant opened_invariants m) m;
    h.is_ghost_action_preorder ();
    (), m


let elim_pure_lemma (#h:heap_sig u#h) (p:prop) (frame:h.slprop) 
    (m:h.mem { interpret (h.pure p `h.star` frame) m })
: Lemma (p /\ interpret (h.emp `h.star` frame) m)
= h.star_equiv (h.pure p) frame m;
  FStar.Classical.forall_intro (h.pure_interp p);
  h.star_equiv h.emp frame m;
  emp_trivial h

let elim_pure
      (#h:heap_sig u#h)
      (#opened_invariants:_)
      (p:prop)
: ghost_action_except h (squash p) opened_invariants (h.pure p) (fun _ -> h.emp)
= fun frame m ->
    ac_lemmas h;
    elim_pure_lemma p (frame `h.star` h.mem_invariant opened_invariants m) m;
    h.is_ghost_action_preorder ();
    (), m

let intro_pure_lemma (#h:heap_sig u#h) (p:prop) (frame:h.slprop) (pf:squash p)
    (m:h.mem { interpret (h.emp `h.star` frame) m })
: Lemma (interpret (h.pure p `h.star` frame) m)
= h.star_equiv h.emp frame m;
  FStar.Classical.forall_intro (h.pure_interp p);
  h.star_equiv (h.pure p) frame m

let intro_pure
      (#h:heap_sig u#h)
      (#opened_invariants:_)
      (p:prop)
      (pf:squash p)
: ghost_action_except h unit opened_invariants h.emp (fun _ -> h.pure p)
= fun frame m ->
    ac_lemmas h;
    intro_pure_lemma p (frame `h.star` h.mem_invariant opened_invariants m) pf m;
    h.is_ghost_action_preorder ();
    (), m

let drop_lemma (#h:heap_sig u#h) (p:h.slprop) (frame:h.slprop)
    (m:h.mem { interpret (p `h.star` frame) m })
: Lemma (interpret (h.emp `h.star` frame) m)
= emp_trivial h;
  h.star_equiv p frame m;
  h.star_equiv h.emp frame m

let drop 
      (#h:heap_sig u#h)
      (#opened_invariants:_)
      (p:h.slprop)
: ghost_action_except h unit opened_invariants p (fun _ -> h.emp)
= fun frame m ->
    ac_lemmas h;
    drop_lemma p (frame `h.star` h.mem_invariant opened_invariants m) m;
    h.is_ghost_action_preorder ();
    (), m

let lift_ghost
      (#h:heap_sig u#h)
      (#opened_invariants:inames h)
      (#a:Type u#a)
      (#p:h.slprop)
      (#q:a -> GTot h.slprop)
      (ni_a:non_info a)
      (f:erased (ghost_action_except h a opened_invariants p q))
: ghost_action_except h a opened_invariants p q
= fun frame m0 ->
    let xm1 : erased (a * full_mem h) = 
        let ff = reveal f in
        let x, m1 = ff frame m0 in
        hide (x, m1)
    in
    let x : erased a = fst (reveal xm1) in
    let pre_m1 : erased h.mem = snd (reveal xm1) in
    let m1 = h.update_ghost m0 pre_m1 in
    let x = ni_a x in
    x, m1

let destruct_star_l (#h:heap_sig u#h) (p q:h.slprop) (m:h.mem)
: Lemma (h.interp (p `h.star` q) m ==> h.interp p m)
= introduce h.interp (p `h.star` q) m ==> h.interp p m
  with _ . (
    h.star_equiv p q m;
    eliminate exists c0 c1.
        h.sep.disjoint c0 c1 /\
        m == h.sep.join c0 c1 /\
        h.interp p c0 /\
        h.interp q c1
    returns h.interp p m
    with _ . (
        h.star_equiv p h.emp m;
        emp_trivial h;
        assert (h.interp h.emp c1);
        assert (h.interp (p `h.star` h.emp) m);
        ac_lemmas h
    )
 )

let destruct_star (#h:heap_sig u#h) (p q:h.slprop) (m:h.mem)
: Lemma (h.interp (p `h.star` q) m ==> h.interp p m /\ h.interp q m)
= ac_lemmas h;
  destruct_star_l p q m;
  destruct_star_l q p m


let intro_pure_frame (#h:heap_sig u#h) (p:h.slprop) (q:prop) (_:squash q) (m:h.mem)
: Lemma
  (requires h.interp p m)
  (ensures h.interp (p `h.star` h.pure q) m)
= h.star_equiv p (h.pure q) m;
  h.sep.join_empty m;
  assert (h.sep.disjoint m h.sep.empty);
  h.pure_interp q h.sep.empty