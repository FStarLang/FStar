module PulseCore.BaseHeapSig
module H = PulseCore.Heap
module H2 = PulseCore.Heap2
open PulseCore.Tags
open PulseCore.HeapSig

noeq
type mem : Type u#(a + 1) = {
    heap: H2.heap u#a;
    ctr: nat;
    ghost_ctr: erased nat;
}

let empty_mem 
: mem u#a
= { heap = H2.empty_heap; ctr = 0; ghost_ctr = 0 }

let disjoint_mem (m0 m1: mem)
: prop
= H2.disjoint m0.heap m1.heap

let max (i j:nat) : nat = if i >= j then i else j
let join_mem (m0:mem) (m1:mem { disjoint_mem m0 m1 })
: mem
= { heap = H2.join m0.heap m1.heap;
    ctr = max m0.ctr m1.ctr;
    ghost_ctr = hide <| max m0.ghost_ctr m1.ghost_ctr }

let sep : separable (mem u#a) = {
    empty = empty_mem;
    disjoint = disjoint_mem;
    join = join_mem;
    disjoint_sym = (fun m1 m2 -> H2.disjoint_sym m1.heap m2.heap);
    join_commutative = (fun h0 h1 -> H2.join_commutative h0.heap h1.heap); 
    disjoint_join = (fun m1 m2 m3 -> H2.disjoint_join m1.heap m2.heap m3.heap);
    join_associative = (fun h0 h1 h2 -> H2.join_associative h0.heap h1.heap h2.heap);
    join_empty = (fun m -> H2.join_empty m.heap);
}

let full_mem_pred m = H2.full_heap_pred m.heap

let is_ghost_action m0 m1 : prop =
  m0.ctr == m1.ctr /\
  H2.concrete m0.heap == H2.concrete m1.heap

open FStar.FunctionalExtensionality
let slprop = p:(mem ^-> prop) { is_affine_mem_prop sep p }
let interp (p:slprop) : affine_mem_prop sep = p
  // H2.interp_depends_only_on p;
  // fun h -> H2.interp p h.heap
let as_slprop (p:affine_mem_prop sep) : slprop = on _ p
// = assert (forall m0 m1. H2.disjoint m0 m1 == sep.disjoint m0 m1);
//   H2.as_slprop p

let lift (p:H2.slprop) : slprop =
  H2.interp_depends_only_on p;
  as_slprop fun h -> H2.interp p h.heap

[@@erasable]
noeq
type uunit : Type u#a = | UU
let bprop : Type u#a = uunit
let up (b:bprop) : slprop = lift H2.emp
let down (p:slprop) : bprop = UU
let up_down (p:bprop) : Lemma (down (up p) == p) = ()

let emp : slprop = lift H2.emp
let pure (p:prop) : slprop = as_slprop fun _ -> p

let star' (p1:slprop) (p2:slprop) (m: mem) : prop = 
  exists m0 m1. 
    sep.disjoint m0 m1 /\
    m == sep.join m0 m1 /\
    interp p1 m0 /\
    interp p2 m1
let star'_affine p1 p2 : squash (is_affine_mem_prop sep (star' p1 p2)) =
  introduce forall m m3. star' p1 p2 m /\ sep.disjoint m m3 ==> star' p1 p2 (sep.join m m3) with
  introduce _ ==> _ with _. (
    let m0 = IndefiniteDescription.indefinite_description_ghost _ fun m0 -> exists m1. 
      sep.disjoint m0 m1 /\ m == sep.join m0 m1 /\ interp p1 m0 /\ interp p2 m1 in
    let m1 = IndefiniteDescription.indefinite_description_ghost _ fun m1 ->
      sep.disjoint m0 m1 /\ m == sep.join m0 m1 /\ interp p1 m0 /\ interp p2 m1 in
    sep.join_commutative m0 m1;
    sep.join_associative m3 m1 m0;
    sep.join_commutative m3 (sep.join m0 m1);
    sep.join_commutative (sep.join m3 m1) m0;
    sep.join_commutative m3 m1;
    assert star' p1 p2 (sep.join m0 (sep.join m1 m3))
  )
let star (p1:slprop) (p2:slprop) : slprop =
  star'_affine p1 p2;
  as_slprop (star' p1 p2)
let star_equiv (p q:slprop) (m:mem)
: Lemma (
    interp (p `star` q) m <==> 
        (exists m0 m1. 
          sep.disjoint m0 m1 /\
          m == sep.join m0 m1 /\
          interp p m0 /\
          interp q m1)
  )
= ()

let slprop_extensionality (p q:slprop)
: Lemma ((forall c. interp p c <==> interp q c) ==> p == q)
        [SMTPat (p == q)]
= introduce (forall c. interp p c <==> interp q c) ==> p == q with _. (
    introduce forall c. p c == q c with PropositionalExtensionality.apply (p c) (q c);
    extensionality _ _ p q
  )

let lift_star (p q: H2.slprop) : squash (lift (p `H2.star` q) == lift p `star` lift q) =  
  introduce forall c. interp (lift (p `H2.star` q)) c <==> interp (lift p `star` lift q) c with (
    introduce H2.interp (p `H2.star` q) c.heap ==> interp (lift p `star` lift q) c with _. (
      H2.elim_star p q c.heap;
      let h1 = IndefiniteDescription.indefinite_description_ghost _ fun h1 -> exists h2.
        H2.disjoint h1 h2 /\ c.heap == H2.join h1 h2 /\ H2.interp p h1 /\ H2.interp q h2 in
      let h2 = IndefiniteDescription.indefinite_description_ghost _ fun h2 ->
        H2.disjoint h1 h2 /\ c.heap == H2.join h1 h2 /\ H2.interp p h1 /\ H2.interp q h2 in
      let c1: mem = { c with heap = h1 } in
      let c2: mem = { c with heap = h2 } in
      assert sep.disjoint c1 c2
    );
    introduce interp (lift p `star` lift q) c ==> H2.interp (p `H2.star` q) c.heap with _. (
      let c1 = IndefiniteDescription.indefinite_description_ghost _ fun c1 -> exists c2.
        disjoint_mem c1 c2 /\ c == join_mem c1 c2 /\ interp (lift p) c1 /\ interp (lift q) c2 in
      let c2 = IndefiniteDescription.indefinite_description_ghost _ fun c2 ->
        disjoint_mem c1 c2 /\ c == join_mem c1 c2 /\ interp (lift p) c1 /\ interp (lift q) c2 in
      H2.intro_star p q c1.heap c2.heap
    )
  );
  slprop_extensionality (lift (p `H2.star` q)) (lift p `star` lift q)

let interp_as (p:affine_mem_prop sep)
: Lemma (forall c. interp (as_slprop p) c == p c)
= introduce forall c. interp (as_slprop p) c == p c
  with FStar.PropositionalExtensionality.apply (interp (as_slprop p) c) (p c)

let free_above (m:mem u#a) =
  H2.free_above_addr CONCRETE m.heap m.ctr /\
  H2.free_above_addr GHOST m.heap m.ghost_ctr
  // (forall i. i >= m.ghost_ctr ==> None? (H2.select_ghost i m.heap)) /\
  // (forall i. i >= m.ctr ==> None? (H2.select i m.heap))

let mem_invariant (is:GhostSet.set unit) (m:mem u#a)
: slprop u#a
= pure (free_above m)

let dup_pure (p:prop)
: Lemma (pure p == pure p `star` pure p)
= FStar.Classical.forall_intro sep.join_empty ;
  slprop_extensionality (pure p) (pure p `star` pure p)

let iname_of (i:unit) = i
let inv (i:unit) (p:slprop) = pure False
let inv_extract (i:unit) (p:slprop u#a) (m:mem u#a)
: Lemma 
  (requires interp (inv i p) m)
  (ensures p == emp)
= ()

let deq_iref : GhostSet.decide_eq unit = fun x y -> true
let mem_invariant_equiv (e:GhostSet.set unit) (m:mem u#a) (i:unit) (p:slprop u#a)
: Lemma 
  (requires
    interp (inv i p) m /\
    ~ (i `GhostSet.mem` e))
  (ensures
    mem_invariant e m ==
    mem_invariant (HeapSig.add deq_iref i e) m `star` p)
= ()

let dup_inv_equiv (i:unit) (p:slprop)
: Lemma (inv i p == inv i p `star` inv i p)
= dup_pure False
    
let emp_unit (p:slprop) : Lemma (p == (p `star` emp)) =
  introduce forall (h: _ { interp p h }). interp (p `star` emp) h with (
    let h2 = sep.empty in
    sep.join_empty h;
    H2.intro_emp h2.heap
  );
  slprop_extensionality p (p `star` emp)

let star_congruence (p q:slprop)
: Lemma
  (requires up (down p) == p /\ up (down q) == q)
  (ensures up (down (p `star` q)) == p `star` q)
= emp_unit p; emp_unit q

let update_ghost (m0:mem u#a) (m1:erased (mem u#a) { is_ghost_action m0 m1 })
: m:mem u#a { m == reveal m1 }
= { heap = H2.upd_ghost_heap m0.heap m1.heap; ctr = m0.ctr; ghost_ctr = m1.ghost_ctr }

let pure_true_emp () : Lemma (pure True == emp) =
  introduce forall h. interp (pure True) h <==> interp emp h with H2.intro_emp h.heap;
  slprop_extensionality (pure True) emp
let intro_emp (h:mem) : Lemma (interp emp h) = H2.intro_emp h.heap
let empty_mem_invariant (e:GhostSet.set unit)
: Lemma (mem_invariant e empty_mem == emp)
= FStar.Classical.forall_intro H2.free_above_empty;
  assert (free_above empty_mem);
  calc (==) {
    pure (free_above empty_mem);
  (==) { FStar.PropositionalExtensionality.apply (free_above empty_mem) True }
    pure True;
  (==) { pure_true_emp () }
    emp;
  }
let base_heap : heap_sig u#a =
  {
    mem;
    sep;
    full_mem_pred;
    is_ghost_action;
    is_ghost_action_preorder= (fun _ -> ());
    update_ghost;
    slprop;
    interp;
    as_slprop;
    interp_as;
    slprop_extensionality;
    non_info_slprop = (fun x -> reveal x);
    bprop;
    up;
    down;
    up_down;
    emp;
    pure;
    star;
    intro_emp;
    pure_interp=(fun p c -> ());
    pure_true_emp;
    emp_unit;
    star_equiv;
    star_congruence;
    iref = unit;
    deq_iref;
    non_info_iref = (fun x -> reveal x);
    inv;
    iname_ok = (fun _ _ -> True);
    dup_inv_equiv;
    mem_invariant;
    inv_iname_ok = (fun _ _ _ -> ());
    mem_invariant_equiv;
    iref_injective = (fun _ -> false);
    iref_injectivity = (fun _ _ _ _ _ -> ());
    empty_mem_invariant
}
let join_empty_inverse m0 m1 = H2.join_empty_inverse m0.heap m1.heap
let core_ghost_ref_is_null (r:core_ghost_ref) = H2.core_ghost_ref_is_null r
let core_ghost_ref_as_addr (r:core_ghost_ref)
: GTot nat
= H2.core_ghost_ref_as_addr r
let addr_as_core_ghost_ref (a:nat)
: GTot core_ghost_ref
= H2.addr_as_core_ghost_ref a
let core_ghost_ref_as_addr_injective r1 = H2.core_ghost_ref_as_addr_injective r1
let addr_as_core_ghost_ref_injective a = H2.addr_as_core_ghost_ref_injective a
let select_ghost i m = H2.select_ghost i m.heap
let ghost_ctr m = m.ghost_ctr
let empty_mem_props () = 
  FStar.Classical.forall_intro H2.free_above_empty;
  FStar.Classical.forall_intro_3 H2.reveal_free_above_addr
let mem_invariant_interp (ex:inames base_heap) (h0:base_heap.mem) (h1:base_heap.mem)
: Lemma (base_heap.interp (base_heap.mem_invariant ex h0) h1 ==>
         free_above_ghost_ctr h0)
= base_heap.pure_interp (free_above h0) h1;
  H2.reveal_free_above_addr GHOST h0.heap h0.ghost_ctr
let inames_ok_trivial (ex:inames base_heap) (h:base_heap.mem)
: Lemma (inames_ok ex h)
= ()
let bump_ghost_ctr (m0:base_heap.mem) (x:erased nat)
= let ctr = hide (max m0.ghost_ctr x) in
  let m1 = {m0 with ghost_ctr = ctr} in
  introduce forall ex c0 c1. 
    base_heap.interp (base_heap.mem_invariant ex m0) c0 ==>
    base_heap.interp (base_heap.mem_invariant ex m1) c1
  with introduce _ ==> _
  with _ . (
      base_heap.pure_interp (free_above m0) c0;
      base_heap.pure_interp (free_above m1) c1;
      H2.weaken_free_above GHOST m0.heap m0.ghost_ctr m1.ghost_ctr
  );
  let m' = { m1 with heap = H2.empty_heap } in
  H2.join_empty m0.heap;
  assert m1 == base_heap.sep.join m0 m'; 
  m1

let pts_to #a #p r c = lift (H2.pts_to #a #p r c)
let ghost_pts_to meta #a #p r x = lift (H2.ghost_pts_to meta #a #p r x)
let interp_ghost_pts_to i #meta #a #pcm v h0 = H2.interp_ghost_pts_to i #meta #a #pcm v h0.heap
let ghost_pts_to_compatible_equiv #meta #a #pcm x v0 v1 =
  lift_star (H2.ghost_pts_to meta #a #pcm x v0) (H2.ghost_pts_to meta #a #pcm x v1);
  H2.ghost_pts_to_compatible_equiv #meta #a #pcm x v0 v1;
  H2.slprop_extensionality (H2.ghost_pts_to meta #a #pcm x v0 `H2.star` H2.ghost_pts_to meta #a #pcm x v1)
    (H2.ghost_pts_to meta #a #pcm x (op pcm v0 v1))

(* Lifting H2 actions *)
let mg_of_mut (m:Tags.mutability) =
  match m with
  | Tags.MUTABLE -> false
  | _ -> true

let lower' (frame: slprop) (m: base_heap.mem) (h: H2.heap) : prop =
  interp frame { m with heap = h }
let lower (frame: slprop) (m: base_heap.mem) : p:H2.slprop { forall h. H2.interp p h <==> lower' frame m h } =
  introduce forall (h0 h1: H2.heap). lower' frame m h0 /\ H2.disjoint h0 h1 ==> lower' frame m (H2.join h0 h1) with
    introduce _ ==> _ with _ . (
      let m0 = { m with heap = h0 } in
      let m1 = { m with heap = h1 } in
      assert sep.disjoint m0 m1
    );
  H2.as_slprop (lower' frame m)

let elim_init (e:_) (fp: H2.slprop) (frame:slprop u#a) (m:base_heap.mem)
: Lemma 
  (requires interpret (lift fp `star` frame `star` mem_invariant e m) m)
  (ensures H2.interp fp m.heap /\ H2.interp (fp `H2.star` lower frame m) m.heap /\ free_above m)
= ac_lemmas base_heap;
  HeapSig.destruct_star #base_heap (lift fp `star` frame) (mem_invariant e m) m;
  HeapSig.destruct_star #base_heap (lift fp) frame m;
  assert H2.interp fp m.heap;
  assert free_above m;
  let m1 = IndefiniteDescription.indefinite_description_ghost _ fun m1 -> exists m2.
    disjoint_mem m1 m2 /\ m == join_mem m1 m2 /\ interp (lift fp) m1 /\ interp frame m2 in
  let m2 = IndefiniteDescription.indefinite_description_ghost _ fun m2 ->
    disjoint_mem m1 m2 /\ m == join_mem m1 m2 /\ interp (lift fp) m1 /\ interp frame m2 in
  assert interp frame m2;
  let m3 = { m with heap = H2.empty_heap } in
  let m4 = { m with heap = m2.heap } in
  H2.join_empty m2.heap;
  assert H2.disjoint m2.heap m3.heap;
  assert disjoint_mem m2 m3;
  assert join_mem m2 m3 == m4;
  assert interp frame m4;
  assert H2.interp (lower frame m) m4.heap;
  assert disjoint_mem m1 m4;
  assert join_mem m1 m4 == m;
  H2.intro_star fp (lower frame m) m1.heap m4.heap

let intro_fin (e:_) (post: H2.slprop) (frame:slprop) (m:base_heap.mem)
    (m0: base_heap.mem { m0.ctr <= m.ctr /\ m0.ghost_ctr <= m.ghost_ctr })
: Lemma
  (requires H2.interp (post `H2.star` lower frame m0) m.heap /\ free_above m)
  (ensures base_heap.interp (lift post `star` frame `star` mem_invariant e m) m)
= H2.elim_star post (lower frame m0) m.heap;
  let h1 = IndefiniteDescription.indefinite_description_ghost _ fun h1 -> exists h2.
    H2.disjoint h1 h2 /\ m.heap == H2.join h1 h2 /\ H2.interp post h1 /\ H2.interp (lower frame m0) h2 in
  let h2 = IndefiniteDescription.indefinite_description_ghost _ fun h2 ->
    H2.disjoint h1 h2 /\ m.heap == H2.join h1 h2 /\ H2.interp post h1 /\ H2.interp (lower frame m0) h2 in
  let m1 = { m with heap = h1 } in
  let m2 = { m with heap = h2 } in
  assert interp (lift post) m1;
  let m3 = { m0 with heap = h2 } in
  assert interp frame m3;
  let m4 = { m with heap = H2.empty_heap } in
  H2.join_empty h2;
  assert sep.disjoint m3 m4;
  assert join_mem m3 m4 == m2;
  assert interp frame m2;
  assert disjoint_mem m1 m2;
  assert join_mem m1 m2 == m;
  assert interp (lift post `star` frame) m;
  ac_lemmas base_heap;
  HeapSig.intro_pure_frame #base_heap (lift post `star` frame) (free_above m) () m
              
let lift_heap_action
      (#fp:H2.slprop u#a)
      (#a:Type u#b)
      (#fp':a -> H2.slprop u#a)
      (#mut:_)
      (e:inames base_heap)
      ($f:H2.action #mut #None fp a fp')
      (#fp_post: a -> slprop u#a { forall x. lift (fp' x) == fp_post x })
: act:_action_except base_heap a (mg_of_mut mut) e (lift fp) fp_post
  {
     mut == IMMUTABLE ==> preserves_inames act  
  }
= let act : _action_except base_heap a (mg_of_mut mut) e (lift fp) fp_post =
    fun frame m0 ->
      elim_init e fp frame m0;
      let h0 = m0.heap in
      assert H2.interp fp h0;
      let (| x, h1 |) = f h0 in
      assert H2.interp (fp' x) h1;
      let m1 = {m0 with heap=h1} in
      assert (H2.interp (fp' x `H2.star` lower frame m0) m1.heap);
      assert (H2.action_related_heaps #mut #None h0 h1);
      assert (H2.does_not_allocate CONCRETE h0 h1);
      assert (H2.does_not_allocate GHOST h0 h1);
      assert (free_above m1);
      intro_fin e (fp' x) frame m1 m0;
      assert (maybe_ghost_action base_heap (mg_of_mut mut) m0 m1);
      assert (inames_ok e m1);
      (x, m1)
  in
  match mut with
  | IMMUTABLE ->
    introduce forall (m0:full_mem base_heap) frame. 
      interpret (lift fp `base_heap.star` frame `base_heap.star` base_heap.mem_invariant e m0) m0 /\
      inames_ok e m0
      ==> ( 
      let x, m1 = act frame m0 in
      heaps_preserve_inames m0 m1
    )
    with introduce _ ==> _ 
    with _. ( 
      let x, m1 = act frame m0 in
      elim_init e fp frame m0;
      H2.action_framing f (lower frame m0) m0.heap;
      assert (H2.action_related_heaps #IMMUTABLE #None m0.heap m1.heap);
      assert (m0 == m1);
      assert (heaps_preserve_inames m0 m1)
    );
    act
  | _ -> act

let with_fresh_ghost_counter (#t:Type u#t) (#post:t -> H2.slprop u#a) (e:inames base_heap)
  (f: (addr:erased nat ->
        H2.action #ONLY_GHOST #(Some GHOST)
          #(fun h -> h `H2.free_above_addr GHOST` addr)
          #(fun h -> h `H2.free_above_addr GHOST` (addr + 1))      
          H2.emp 
          t
          post))
: ghost_action_except base_heap t e emp (fun x -> lift (post x))
= fun frame m0 ->
    elim_init e H2.emp frame m0;
    let h0 = m0.heap in
    let (|r, h1|) = f m0.ghost_ctr h0 in
    let m1 = {m0 with heap=h1; ghost_ctr=m0.ghost_ctr + 1} in
    intro_fin e (post r) frame m1 m0;
    r, m1

let ghost_extend_alt
    (meta:erased bool)
    (#ex:inames base_heap)
    (#a:Type u#a)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: ghost_action_except base_heap (ghost_ref a pcm) ex    
        base_heap.emp 
        (fun r -> ghost_pts_to meta r x)
= with_fresh_ghost_counter ex (H2.ghost_extend #meta #a #pcm x)

let ghost_extend_spec_alt
      (#meta:bool)
      (#ex:inames base_heap)
      #a #pcm (x:a { pcm.refine x })
      (frame:base_heap.slprop)
      (h:full_mem base_heap { 
        inames_ok ex h /\
        interpret (base_heap.emp `base_heap.star`
                   frame `base_heap.star`
                   base_heap.mem_invariant ex h) h })      
: Lemma (
      let (r, h1) = ghost_extend_alt meta #ex #a #pcm x frame h in
      single_ghost_allocation meta #a #pcm x r h h1)
= let act = ghost_extend_alt meta #ex #a #pcm x in
  let _, m1 = act frame h in
  elim_init ex H2.emp frame h;
  H2.ghost_extend_spec #meta #a #pcm x h.ghost_ctr h.heap;
  HeapSig.destruct_star
    (base_heap.emp `base_heap.star` frame)
    (base_heap.mem_invariant ex h) h;
  assert (interpret (base_heap.mem_invariant ex h) h);
  mem_invariant_interp ex h h;
  assert (free_above_ghost_ctr h)
  

let ghost_extend meta #ex #a #pcm x =
  let act = ghost_extend_alt meta #ex #a #pcm x in
  introduce reveal meta == false ==> preserves_inames act
  with _ . (
    introduce forall (m0:full_mem base_heap) frame. 
      interpret (base_heap.emp `base_heap.star` frame `base_heap.star` base_heap.mem_invariant ex m0) m0 /\
      inames_ok ex m0
      ==> ( 
      let r, m1 = act frame m0 in
      heaps_preserve_inames m0 m1
    )
    with introduce _ ==> _
    with _. (
      ghost_extend_spec_alt #meta #ex #a #pcm x frame m0;
      elim_init ex H2.emp frame m0;
      assert (free_above m0);
      H2.reveal_free_above_addr GHOST m0.heap m0.ghost_ctr
    )
  );
  act

let ghost_extend_spec
      (#meta:bool)
      (#ex:inames base_heap)
      #a #pcm (x:a { pcm.refine x })
      (frame:base_heap.slprop)
      (h:full_mem base_heap { 
        inames_ok ex h /\
        interpret (base_heap.emp `base_heap.star`
                   frame `base_heap.star`
                   base_heap.mem_invariant ex h) h })      
= ghost_extend_spec_alt #meta #ex #a #pcm x frame h

let ghost_read #ex #meta #a #p r x f = lift_heap_action ex (H2.ghost_read #meta #a #p r x f)
let ghost_write #ex #meta #a #p r x y f = 
    let act 
      : ghost_action_except base_heap unit ex
          (ghost_pts_to meta r x)
          (fun _ -> ghost_pts_to meta r y)
      = lift_heap_action ex (H2.ghost_write #meta #a #p r x y f)
    in
    introduce reveal meta == false ==> preserves_inames act
    with _ . (
      introduce forall (m0:full_mem base_heap) frame. 
        interpret ((ghost_pts_to meta r x) `base_heap.star` frame `base_heap.star` base_heap.mem_invariant ex m0) m0 /\
        inames_ok ex m0
          ==> ( 
          let x, m1 = act frame m0 in
          heaps_preserve_inames m0 m1
        )
      with introduce _ ==> _ 
      with _. ( 
        let _, m1 = act frame m0 in
        elim_init ex (H2.ghost_pts_to meta #a #p r x) frame m0;
        H2.ghost_write_modifies #meta #a #p r x y f m0.heap;
        match (H2.select_ghost (H2.core_ghost_ref_as_addr r) m0.heap) with
        | None -> ()
        | Some (H.Ref meta' _ _ _) -> 
          assert (reveal meta == false);
          assert (H2.interp (H2.ghost_pts_to meta #a #p r x) m0.heap);
          interp_ghost_pts_to r #meta #a #p x m0;
          assert (reveal meta' == false)
      )
    );
    act
let ghost_share #ex #meta #a #p r x y =
  lift_star (H2.ghost_pts_to meta #a #p r x) (H2.ghost_pts_to meta #a #p r y);
  lift_heap_action ex (H2.ghost_share #meta #a #p r x y)
let ghost_gather #ex #meta #a #p r x y =
  lift_star (H2.ghost_pts_to meta #a #p r x) (H2.ghost_pts_to meta #a #p r y);
  lift_heap_action ex (H2.ghost_gather #meta #a #p r x y)
    #(fun _ -> ghost_pts_to meta r (op p x y))

let with_fresh_counter (#t:Type u#t) (#post:t -> H2.slprop u#a) (e:inames base_heap)
  (f: (addr:nat ->
        H2.action #MUTABLE #(Some CONCRETE)
          #(fun h -> h `H2.free_above_addr CONCRETE` addr)
          #(fun h -> h `H2.free_above_addr CONCRETE` (addr + 1))      
          H2.emp 
          t
          post))
: action_except base_heap t e emp (fun x -> lift (post x))
= fun frame m0 ->
    elim_init e H2.emp frame m0;
    let h0 = m0.heap in
    let (|r, h1|) = f m0.ctr h0 in
    let m1 = {m0 with heap=h1; ctr=m0.ctr + 1} in
    intro_fin e (post r) frame m1 m0;
    r, m1

let extend_alt #ex #a #pcm (x:a {pcm.refine x})
  : action_except base_heap (ref a pcm) ex    
        base_heap.emp 
        (fun r -> pts_to r x)
  = with_fresh_counter ex (H2.extend #a #pcm x)
let extend #ex #a #pcm (x:a {pcm.refine x})
: act:action_except base_heap (ref a pcm) ex    
          base_heap.emp 
          (fun r -> pts_to r x) {
            preserves_inames act
          }
= let act = extend_alt #ex #a #pcm x in 
  FStar.Classical.forall_intro_2 H2.select_ghost_interp;
  introduce forall (m0:full_mem base_heap) frame. 
      interpret (base_heap.emp `base_heap.star` frame `base_heap.star` base_heap.mem_invariant ex m0) m0 /\
      inames_ok ex m0
      ==> ( 
      let r, m1 = act frame m0 in
      heaps_preserve_inames m0 m1
  )
  with introduce _ ==> _ 
  with _. ( 
    let r, m1 = act frame m0 in
    elim_init ex H2.emp frame m0;
    H2.extend_modifies #a #pcm x m0.ctr m0.heap
  );
  act


let read #ex #a #p r x f = lift_heap_action ex (H2.select_refine #a #p r x f) #(fun v -> pts_to r (f v))
let write #ex #a #p r x y f = 
  let act
    : action_except base_heap unit ex
        (pts_to r x)
        (fun _ -> pts_to r y)
    = lift_heap_action ex (H2.upd_gen_action #a #p r x y f)
  in
  FStar.Classical.forall_intro_2 H2.select_ghost_interp;
  introduce forall (m0:full_mem base_heap) frame. 
  interpret ((pts_to r x) `base_heap.star` frame `base_heap.star` base_heap.mem_invariant ex m0) m0 /\
  inames_ok ex m0
    ==> ( 
    let x, m1 = act frame m0 in
    heaps_preserve_inames m0 m1
  )
  with introduce _ ==> _ 
  with _. ( 
    let _, m1 = act frame m0 in
    elim_init ex (H2.pts_to #a #p r x) frame m0;
    H2.upd_gen_modifies #a #p r x y f m0.heap;
    assert (H2.ghost m0.heap == H2.ghost m1.heap);
    ()
  );
  act
let share #ex #a #p r x y =
  lift_star (H2.pts_to #a #p r x) (H2.pts_to #a #p r y);
  lift_heap_action ex (H2.split_action #a #p r x y)
let gather #ex #a #p r x y =
  lift_star (H2.pts_to #a #p r x) (H2.pts_to #a #p r y);
  lift_heap_action ex (H2.gather_action #a #p r x y)
    #(fun _ -> pts_to r (op p x y))
let pts_to_not_null_action #ex #a #p r x = lift_heap_action ex (H2.pts_to_not_null_action #a #p r x)

let interp_exists_sem (#a:Type) (p: a -> base_heap.slprop) (m:_)
: Lemma (interp (exists_ p) m <==> (exists x. interp (p x) m))
= assert (interp (exists_ p) m == base_heap.interp (exists_ p) m);
  interp_exists p

let exists_congruence (#a:Type) (witness:a) (p: a -> base_heap.slprop)
: Lemma 
  (requires forall x. is_boxable (p x))
  (ensures is_boxable (exists_ p))
= introduce forall m. interp (exists_ p) m ==> interp (up (down (exists_ p))) m
  with introduce _ ==> _
  with _ . (
    interp_exists_sem p m
  );
  introduce forall m. interp (up (down (exists_ p))) m ==> interp (exists_ p) m
  with introduce _ ==> _
  with _ . ( 
    interp_exists_sem p m 
  );
  slprop_extensionality (exists_ p) (up (down (exists_ p)))