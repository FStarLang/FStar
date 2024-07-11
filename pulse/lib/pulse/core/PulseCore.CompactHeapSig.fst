module PulseCore.CompactHeapSig
open FStar.Ghost
open FStar.PCM
open PulseCore.HeapSig
module H2 = PulseCore.Heap2
module ST = PulseCore.HoareStateMonad
module CM = FStar.Algebra.CommMonoid
open FStar.Tactics.Typeclasses

//wrapping pcm as a class just for type inference
class pcm_class (h:Type u#a) = { p:pcm h }
let empty {| s:pcm_class 'h |} = s.p.p.one
let disjoint {| s:pcm_class 'h |} = s.p.p.composable
let join {| s:pcm_class 'h |} = s.p.p.op
let disjoint_empty {| s : pcm_class 'h |} (h:'h)
: Lemma (disjoint h empty /\
         join h (empty #'h) == h /\
         join (empty #'h) h == h)
= s.p.is_unit h;
  s.p.comm h (empty #'h)

let is_affine {| pcm_class 'h |} (p:'h -> prop) : prop
= forall h0 h1. p h0 /\ disjoint h0 h1 ==> p (join h0 h1)
let affine_p h {| pcm_class h |} = p:(h -> prop) { is_affine p }

class cm (a:Type u#a) = { [@@@no_method] f: CM.cm a }
let ( ** ) {| p : cm 'a |} = p.f.mult
let emp {| p : cm 'a |} = p.f.unit

(* The paper doesn't have a class of pred, define it directly as affine_p heap;
   But, to support extensionality, we define it as a class with an abstract type
   slprop in a bijection with affine_p heap, with emp and ** *)
class pred (heap:Type u#a) {| pcm_class heap |} : Type u#(a + 1) = {
  slprop : Type u#a;
  interp: slprop -> affine_p heap;
  as_slprop: affine_p heap -> slprop;
  [@@@no_method]
  interp_as : (
      p:affine_p heap ->
      Lemma (forall c. interp (as_slprop p) c == p c)
  );
  slprop_extensionality: (
      p:slprop ->
      q:slprop ->
      Lemma ((forall c. interp p c <==> interp q c) ==> p == q)
  );
  [@@@no_method]
  cm : cm slprop;
  star_interp: (
      p:slprop ->
      q:slprop ->
      m:heap ->
      Lemma (
        interp (p ** q) m <==> 
        (exists m0 m1. 
          disjoint m0 m1 /\
          m == join m0 m1 /\
          interp p m0 /\
          interp q m1))
    );
  emp_interp : interp emp empty;
}

instance cm_pred #h {| pcm_class h |} {| p:pred h |} : cm p.slprop = p.cm

let emp_any (#heap:Type u#a) {| pcm_class heap |} {| p: pred heap |}  (h:heap)
: Lemma (interp emp h)
= let emp = emp #p.slprop in
  FStar.Squash.return_squash p.emp_interp;
  let hp = interp emp in
  disjoint_empty h;
  assert (disjoint (empty #heap) h);
  assert (hp h);
  p.interp_as hp

class memory (mem:Type u#a) : Type u#(a + 1) = {
  [@@@no_method]
  heap: Type u#a;
  heap_of: mem -> heap;
  [@@@no_method]
  pcm_class : pcm_class heap;
  [@@@no_method]
  pred : pred heap;
}

instance memory_sep (#mem:Type u#a) {| m:memory mem |} : pcm_class m.heap = m.pcm_class
instance memory_pred (#mem:Type u#a) {| m:memory mem |} : pred m.heap = m.pred
instance memory_cm (#mem:Type u#a) {| m:memory mem |} : cm (slprop #m.heap) = m.pred.cm
open FStar.Set

class invariants (mem:Type u#a)  {| m:memory mem |} = {
    iname:eqtype;
    iref:Type0;
    iname_of: (i:iref -> GTot iname);
    inv : iref -> slprop #m.heap -> slprop #m.heap;
    iname_ok: iname -> mem -> prop;
    [@@@no_method]
    dup_inv_equiv : (
      i:iref ->
      p:slprop ->
      Lemma (inv i p == (inv i p ** inv i p))
    );
    mem_invariant : set iname -> mem -> slprop #m.heap;
    [@@@no_method]
    inv_iname_ok : (
      i:iref ->
      p:slprop ->
      m:mem ->
      Lemma 
        (requires interp (inv i p) (heap_of m))
        (ensures iname_ok (iname_of i) m)
    );
    [@@@no_method]
    mem_invariant_equiv : (
      e:set iname ->
      m:mem ->
      i:iref ->
      p:slprop ->
      Lemma 
        (requires
          interp (inv i p) (heap_of m) /\
          not (iname_of i `Set.mem` e))
        (ensures
          mem_invariant e m ==
          mem_invariant (Set.add (iname_of i) e) m ** p)
    );
}

class storable (mem:Type u#(a + 1)) {| m: memory mem |} = {
  sprop : Type u#a;
  up: sprop -> slprop #m.heap;
  down: slprop #m.heap -> sprop;
  up_down: (
      p:sprop ->
      Lemma (down (up p) == p)
    );
  non_info_sprop: non_info sprop;
}

class erasability (mem:Type u#a) {| m:memory mem |} {| i:invariants mem |} = {
  is_ghost_action : mem -> mem -> prop;
  is_ghost_action_preorder : FStar.Preorder.preorder_rel is_ghost_action;
  update_ghost : (
      m0:mem ->
      m1:erased mem { is_ghost_action m0 m1 } ->
      m:mem { m == reveal m1 }
  );
  non_info_slprop : non_info (slprop #m.heap);
  non_info_iref : non_info i.iref;
}


noeq
type slsig : Type u#(a + 2) = {
  mem : Type u#(a + 1);
  memory : memory mem;
  invariants : invariants mem;
  storable : storable mem;
  erasablility : erasability mem;
}
let full_mem (s:slsig) = m:s.mem { s.memory.pcm_class.p.refine (heap_of m) }

let separable_of_pcm (a:Type u#a) (p:pcm a)
: separable a
= let core = a in
  let empty = p.p.one in
  let disjoint = p.p.composable in
  let join = p.p.op in
  let disjoint_sym :
    m0:core ->
    m1:core ->
    Lemma (disjoint m0 m1 <==> disjoint m1 m0)
    = fun m0 m1 -> ()
  in
  let join_commutative (m0:core) (m1:core { disjoint m0 m1 })
  : Lemma (disjoint_sym m0 m1; join m0 m1 == join m1 m0)
  = p.comm m0 m1
  in
  let disjoint_join (m0:core) (m1:core) (m2:core)
  : Lemma (
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2) ==>
        disjoint m0 m1 /\
        disjoint m0 m2 /\
        disjoint (join m0 m1) m2 /\
        disjoint (join m0 m2) m1)
  = introduce 
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2) ==>
        disjoint m0 m1 /\
        disjoint m0 m2 /\
        disjoint (join m0 m1) m2 /\
        disjoint (join m0 m2) m1
    with _ . (
      p.assoc m0 m1 m2;
      p.assoc m2 m0 m1;
      join_commutative m2 m0
    )
  in
  let join_associative (m0:core) (m1:core) (m2:core { disjoint m1 m2 /\ disjoint m0 (join m1 m2) } )
  : Lemma (disjoint m0 m1 /\
           disjoint (join m0 m1) m2 /\
           join m0 (join m1 m2) == join (join m0 m1) m2)
  = p.assoc m0 m1 m2
  in
  let join_empty (m0:core)
  : Lemma (disjoint m0 empty /\ join m0 empty == m0)
  = p.is_unit m0
  in
  { core; core_of=(fun m -> m); empty; disjoint; join; disjoint_sym; join_commutative; disjoint_join; join_associative; join_empty }

let pcm_of_separable (a:Type u#a) (p:separable a)
: pcm p.core
= FStar.Classical.forall_intro_2 p.disjoint_sym;
  let pp : pcm' p.core = { composable=p.disjoint; op=p.join; one=p.empty } in
  let assoc_r : FStar.PCM.lem_assoc_r pp =
    fun x y z ->
      assert (pp.composable x y);
      assert (pp.composable (pp.op x y) z);
      p.disjoint_sym (pp.op x y) z;
      p.disjoint_join z x y;
      assert (pp.composable z x);
      assert (pp.composable z y);
      assert (pp.composable (pp.op z x) y);
      assert (pp.composable (pp.op z y) x);
      p.join_commutative z y;
      assert (pp.composable (pp.op y z) x);
      p.disjoint_sym (pp.op y z) x;
      assert (pp.composable y z);
      assert (pp.composable x (pp.op y z));
      p.join_associative x y z
  in
  { p=pp;
    comm=p.join_commutative;
    assoc = (fun m0 m1 m2 -> p.join_associative m0 m1 m2);
    assoc_r;
    is_unit = (fun m -> p.join_empty m);
    refine = (fun m -> True);
  }
