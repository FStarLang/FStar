module PulseCore.HeapSig
open FStar.Ghost
open FStar.PCM
module H2 = PulseCore.Heap2
module ST = PulseCore.HoareStateMonad
module CM = FStar.Algebra.CommMonoid
module Set = FStar.GhostSet
let non_info (t:Type u#a) : Type u#a = x:erased t -> (y:t { y == reveal x })

let core_ref: Type u#0 = H2.core_ref
let core_ref_null = H2.core_ref_null
let is_null : core_ref -> GTot bool = H2.core_ref_is_null
let ref (a:Type u#a) (p:pcm a) = core_ref

let core_ghost_ref : Type u#0 = H2.core_ghost_ref
let ghost_ref (a:Type u#a) (p:pcm a) = core_ghost_ref
let add (#a:Type) (f:Set.decide_eq a) (x:a) (y:Set.set a) = Set.union (Set.singleton f x) y

noeq
type separable (mem:Type u#a) = {
  empty : mem;
  disjoint : mem -> mem -> prop;
  join : (
    m0:mem ->
    m1:mem { disjoint m0 m1 } ->
    mem
  );
  disjoint_sym : (
    m0:mem ->
    m1:mem ->
    Lemma (disjoint m0 m1 <==> disjoint m1 m0)
  );
  join_commutative : (
    m0:mem ->
    m1:mem { disjoint m0 m1 } ->
    Lemma (disjoint_sym m0 m1; join m0 m1 == join m1 m0)
  );
  disjoint_join : (
    m0:mem ->
    m1:mem ->
    m2:mem ->
    Lemma (
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2) ==>
        disjoint m0 m1 /\
        disjoint m0 m2 /\
        disjoint (join m0 m1) m2 /\
        disjoint (join m0 m2) m1)
  );
  join_associative : (
    m0:mem ->
    m1:mem ->
    m2:mem { disjoint m1 m2 /\ disjoint m0 (join m1 m2) } ->
    Lemma (disjoint m0 m1 /\
           disjoint (join m0 m1) m2 /\
           join m0 (join m1 m2) == join (join m0 m1) m2)
  );
  join_empty : (
    m0:mem ->
    Lemma (disjoint m0 empty /\ join m0 empty == m0)
  );
}

let is_affine_mem_prop (#m:Type u#a) (sep:separable m) (p:m -> prop)
: prop
= forall (m0 m1:m). p m0 /\ sep.disjoint m0 m1 ==> p (sep.join m0 m1)

let affine_mem_prop (#m:Type u#a) (sep:separable m)
: Type u#(max 1 a)
= p:(m -> prop){ is_affine_mem_prop sep p }

noeq
type heap_sig : Type u#(a + 2) = {
    mem : Type u#(a + 1);
    sep : separable mem;
    full_mem_pred : mem -> prop;
    
    is_ghost_action : mem -> mem -> prop;
    is_ghost_action_preorder : (
      unit ->
      Lemma (FStar.Preorder.preorder_rel is_ghost_action)
    );
    update_ghost : (
      m0:mem ->
      m1:erased mem { is_ghost_action m0 m1 } ->
      m:mem { m == reveal m1 }
    );
    slprop : Type u#(a + 1);
    interp: slprop -> affine_mem_prop sep;
    as_slprop: affine_mem_prop sep -> slprop;
    interp_as : (
      p:affine_mem_prop sep ->
      Lemma (forall c. interp (as_slprop p) c == p c)
    );
    slprop_extensionality: (
      p:slprop ->
      q:slprop ->
      Lemma ((forall c. interp p c <==> interp q c) ==> p == q)
    );
    non_info_slprop: non_info slprop;

    emp : slprop;
    pure : prop -> slprop;
    star : slprop -> slprop -> slprop;
    intro_emp: (
      c:mem ->
      Lemma (interp emp c)
    );
    pure_interp: (
      p:prop ->
      c:mem ->
      Lemma (interp (pure p) c == p)
    );
    pure_true_emp: (
      unit ->
      Lemma (pure True == emp)
    );
    emp_unit : (
      p:slprop ->
      Lemma (p == (p `star` emp))
    );
    star_equiv: (
      p:slprop ->
      q:slprop ->
      m:mem ->
      Lemma (
        interp (p `star` q) m <==> 
        (exists m0 m1. 
          sep.disjoint m0 m1 /\
          m == sep.join m0 m1 /\
          interp p m0 /\
          interp q m1))
    );
}

val star_commutative (#h: heap_sig) (p q: h.slprop) : Lemma (p `h.star` q == q `h.star` p)
val star_associative (#h: heap_sig) (p q r: h.slprop) : Lemma (p `h.star` (q `h.star` r) == (p `h.star` q) `h.star` r)

val emp_trivial (h:heap_sig u#a)
: Lemma (forall m. h.interp h.emp m)

let interpret (#h:heap_sig u#h) (p:h.slprop) : h.mem -> prop = fun m -> h.interp p m
let full_mem (hs:heap_sig u#h) = m:hs.mem{ hs.full_mem_pred m }
let maybe_ghost_action (chs:heap_sig u#m) (maybe_ghost:bool) (m0 m1:chs.mem)
    = maybe_ghost ==> chs.is_ghost_action m0 m1

let step_t 
  (chs:heap_sig u#m)
  (a:Type u#a)
  (maybe_ghost:bool)
  (expects:chs.slprop)
  (provides: a -> GTot chs.slprop)
  (frame:chs.slprop)
= ST.st #(full_mem chs) a
    (requires fun m0 ->
        interpret (expects `chs.star` frame) m0)
    (ensures fun m0 x m1 ->
        maybe_ghost_action chs maybe_ghost m0 m1 /\
        interpret (expects `chs.star` frame) m0 /\  //TODO: fix the effect so as not to repeat this
        interpret (provides x `chs.star` frame) m1)

(** An action is just a thunked computation in [MstTot] that takes a frame as argument *)
let _action_except 
    (chs:heap_sig u#m)
    (a:Type u#a)
    (maybe_ghost:bool)
    (expects:chs.slprop)
    (provides: a -> GTot chs.slprop)
 : Type u#(max a (m + 1)) 
 = frame:chs.slprop -> step_t chs a maybe_ghost expects provides frame

#push-options "--print_universes --print_implicits"
let action_except
    (chs:heap_sig u#m)
    (a:Type u#a)
    (expects:chs.slprop)
    (provides:a -> GTot chs.slprop)
= _action_except chs a false expects provides

let ghost_action_except
      (chs:heap_sig u#m)
      (a:Type u#a)
      (expects:chs.slprop)
      (provides: a -> GTot chs.slprop)
= _action_except chs a true expects provides

val exists_
    (#chs:heap_sig u#m)
    (#a:Type u#a)
    (p: a -> GTot chs.slprop)
: chs.slprop


val interp_exists (#h:heap_sig u#h) (#a:Type u#a) (p: a -> GTot h.slprop)
: Lemma (forall m. h.interp (exists_ p) m <==> (exists x. h.interp (p x) m))

val exists_extensionality
    (#chs:heap_sig u#m)
    (#a:Type u#a)
    (p: a -> GTot chs.slprop)
    (q: a -> GTot chs.slprop)
: Lemma 
  (requires (forall x. p x == q x))
  (ensures exists_ p == exists_ q)

val cm_slprop (hs:heap_sig u#h)   : c:CM.cm (hs.slprop) { c.unit == hs.emp /\ c.mult == hs.star }
val cm_e_slprop (hs:heap_sig u#h) 
: c:CM.cm (erased hs.slprop) {
  c.unit == hide hs.emp /\
  (forall x y. c.mult x y == hide (hs.star (reveal x) (reveal y)))
}

val ac_lemmas (h:heap_sig u#a)
: Lemma (
    (forall p q r. (p `h.star` q) `h.star` r == p `h.star` (q `h.star` r)) /\
    (forall p q. p `h.star` q == q `h.star` p) /\
    (forall p. p `h.star` h.emp == p)
)

(* Some heap generic actions *)

val frame
      (#h:heap_sig u#h)
      (#maybe_ghost:bool)
      (#a:Type u#a)
      (#pre:h.slprop)
      (#post:a -> GTot h.slprop)
      (frame:h.slprop)
      ($f:_action_except h a maybe_ghost pre post)
: _action_except h a maybe_ghost (pre `h.star` frame) (fun x -> post x `h.star` frame)

module U = FStar.Universe
let lift_dom_ghost #a #b (q:a -> GTot b) : U.raise_t a -> GTot b =
  fun v -> q (U.downgrade_val v)

val lift_h_exists
      (#h:heap_sig u#h)
      (#a:Type u#a)
      (p:a -> GTot h.slprop)
: ghost_action_except h unit
    (exists_ p)
    (fun _a -> exists_ #_ #(U.raise_t a) (lift_dom_ghost p))

val elim_pure
      (#h:heap_sig u#h)
      (p:prop)
: ghost_action_except h (squash p) (h.pure p) (fun _ -> h.emp)

val intro_pure
      (#h:heap_sig u#h)
      (p:prop)
      (_:squash p)
: ghost_action_except h unit h.emp (fun _ -> h.pure p)
  
val drop 
      (#h:heap_sig u#h)
      (p:h.slprop)
: ghost_action_except h unit p (fun _ -> h.emp)

val lift_ghost
      (#h:heap_sig u#h)
      (#a:Type u#a)
      (#p:h.slprop)
      (#q:a -> GTot h.slprop)
      (ni_a:non_info a)
      (f:erased (ghost_action_except h a p q))
: ghost_action_except h a p q

val destruct_star (#h:heap_sig u#h) (p q:h.slprop) (m:h.mem)
: Lemma (h.interp (p `h.star` q) m ==> h.interp p m /\ h.interp q m)

val intro_pure_frame (#h:heap_sig u#h) (p:h.slprop) (q:prop) (_:squash q) (m:h.mem)
: Lemma
  (requires h.interp p m)
  (ensures h.interp (p `h.star` h.pure q) m)
