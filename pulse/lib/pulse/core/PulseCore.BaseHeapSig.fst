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

let lens_core : lens (mem u#a) (H2.heap u#a) = {
    get = (fun s -> s.heap);
    put = (fun v s -> {s with heap = v});
    get_put = (fun m -> ());
    put_get = (fun c m -> ());
    put_put = (fun c1 c2 m -> ())
}

let sep : separable (mem u#a) = {
    core = H2.heap u#a;
    lens_core = lens_core;
    empty = H2.empty_heap;
    disjoint = H2.disjoint;
    join = H2.join;
    disjoint_sym = H2.disjoint_sym;
    join_commutative = (fun h0 h1 -> H2.join_commutative h0 h1); 
    disjoint_join = H2.disjoint_join;
    join_associative = (fun h0 h1 h2 -> H2.join_associative h0 h1 h2);
    join_empty = H2.join_empty;
    join_empty_inverse = H2.join_empty_inverse
}

let full_mem_pred m = H2.full_heap_pred m.heap

let is_ghost_action m0 m1 : prop =
  m0.ctr == m1.ctr /\
  H2.concrete m0.heap == H2.concrete m1.heap

let slprop = H2.slprop
let interp (p:H2.slprop) : affine_mem_prop sep =
  H2.interp_depends_only_on p;
  fun h -> H2.interp p h
let as_slprop (p:affine_mem_prop sep)
: H2.slprop
= assert (forall m0 m1. H2.disjoint m0 m1 == sep.disjoint m0 m1);
  H2.as_slprop p

[@@erasable]
noeq
type uunit : Type u#a = | UU
let bprop : Type u#a = uunit
let up (b:bprop) = H2.emp
let down (p:slprop) : bprop = UU
let up_down (p:bprop) : Lemma (down (up p) == p) = ()

let emp : slprop = H2.emp
let pure (p:prop) : slprop = H2.pure p
let star (p1:slprop) (p2:slprop) : slprop = H2.star p1 p2
let star_equiv (p q:H2.slprop) (m:H2.heap)
: Lemma (
    interp (p `H2.star` q) m <==> 
        (exists m0 m1. 
          sep.disjoint m0 m1 /\
          m == sep.join m0 m1 /\
          interp p m0 /\
          interp q m1)
  )
= introduce  
    interp (p `H2.star` q) m ==> 
        (exists m0 m1. {:pattern (H2.disjoint m0 m1)} 
          sep.disjoint m0 m1 /\
          m == sep.join m0 m1 /\
          interp p m0 /\
          interp q m1)
  with _ . (
    H2.elim_star p q m
  );
  introduce
        (exists m0 m1. 
          H2.disjoint m0 m1 /\
          m == H2.join m0 m1 /\
          H2.interp p m0 /\
          H2.interp q m1) ==>
    H2.interp (p `H2.star` q) m
  with _ . (
      eliminate exists m0 m1. 
          H2.disjoint m0 m1 /\
          m == H2.join m0 m1 /\
          H2.interp p m0 /\
          H2.interp q m1
      returns _ 
      with _ . (
          H2.intro_star p q m0 m1
      )
  )

let slprop_extensionality (p q:H2.slprop)
: Lemma ((forall c. interp p c <==> interp q c) ==> p == q)
        [SMTPat (H2.equiv p q)]
= introduce (forall c. interp p c <==> interp q c) ==> p == q
  with _ . (
    assert (forall p c. interp p c == H2.interp p c);
    H2.slprop_extensionality p q
  )

let interp_as (p:affine_mem_prop sep)
: Lemma (forall c. interp (as_slprop p) c == p c)
= introduce forall c. interp (as_slprop p) c == p c
  with (
    assert (forall m0 m1. H2.disjoint m0 m1 == sep.disjoint m0 m1);
    assert (interp (as_slprop p) c <==> H2.interp (H2.as_slprop p) c);
    assert (H2.interp (H2.as_slprop p) c <==> p c);
    FStar.PropositionalExtensionality.apply (interp (as_slprop p) c) (p c)
  )

let free_above (m:mem u#a) =
  H2.free_above_addr CONCRETE m.heap m.ctr /\
  H2.free_above_addr GHOST m.heap m.ghost_ctr
  // (forall i. i >= m.ghost_ctr ==> None? (H2.select_ghost i m.heap)) /\
  // (forall i. i >= m.ctr ==> None? (H2.select i m.heap))

let mem_invariant (is:eset unit) (m:mem u#a)
: slprop u#a
= pure (free_above m)

let dup_pure (p:prop)
: Lemma (pure p == pure p `H2.star` pure p)
= FStar.Classical.forall_intro (star_equiv (pure p) (pure p));
  FStar.Classical.forall_intro (H2.pure_interp p);
  FStar.Classical.forall_intro sep.join_empty ;
  slprop_extensionality (pure p) (pure p `star` pure p)

let iname_of (i:unit) = i
let inv (i:unit) (p:slprop) = pure (p == H2.emp)
let inv_extract (i:unit) (p:slprop)
: Lemma (inv i p == p `star` inv i p)
= introduce forall m. interp (inv i p) m ==> interp (p `star` inv i p) m
  with introduce _ ==> _
  with _ . ( 
    H2.pure_interp (p == H2.emp) m;
    H2.emp_unit (inv i p);
    H2.star_commutative p (inv i p)
  );
  introduce forall m. interp (p `star` inv i p) m ==> interp (inv i p) m
  with introduce _ ==> _
  with _ . (
    H2.affine_star p (inv i p) m
  );
  assert (H2.equiv (inv i p) (p `star` inv i p))
  
let mem_invariant_equiv (e:eset unit) (m:mem u#a) (i:unit) (p:slprop u#a)
: Lemma 
  (requires
    not (iname_of i `Set.mem` e))
  (ensures
    mem_invariant e m `star` inv i p ==
    mem_invariant (Set.add (iname_of i) e) m `star` p `star` inv i p)
= calc (==) {
    mem_invariant e m `star` inv i p;
  (==) { inv_extract i p }
   mem_invariant (Set.add (iname_of i) e) m `star` (p `star` inv i p);
  (==) { H2.star_associative (mem_invariant (Set.add (iname_of i) e) m) p (inv i p) }
   mem_invariant (Set.add (iname_of i) e) m `star` p `star` inv i p;
  }

let dup_inv_equiv (i:unit) (p:slprop)
: Lemma (inv i p == inv i p `H2.star` inv i p)
= dup_pure (p == H2.emp)

let star_congruence (p q:slprop)
: Lemma
  (requires up (down p) == p /\ up (down q) == q)
  (ensures up (down (p `star` q)) == p `star` q)
= H2.emp_unit p; H2.emp_unit q

let update_ghost (m0:mem u#a) (m1:erased (mem u#a) { is_ghost_action m0 m1 })
: m:mem u#a { m == reveal m1 }
= { heap = H2.upd_ghost_heap m0.heap m1.heap; ctr = m0.ctr; ghost_ctr = m1.ghost_ctr }

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
    non_info_bprop = (fun x -> reveal x);
    up;
    down;
    up_down;
    emp=H2.emp;
    pure=H2.pure;
    star=H2.star;
    intro_emp=H2.intro_emp;
    pure_interp=(fun p c -> H2.pure_interp p c; FStar.PropositionalExtensionality.apply (interp (pure p) c) p);
    pure_true_emp = (fun () -> 
      FStar.Classical.forall_intro (H2.pure_interp True);
      FStar.Classical.forall_intro H2.intro_emp;
      assert (H2.equiv (H2.pure True) H2.emp));
    emp_unit=(fun p -> H2.emp_unit p);
    star_commutative=H2.star_commutative;
    star_associative=H2.star_associative;
    star_equiv;
    star_congruence;
    pts_to=H2.pts_to;
    ghost_pts_to=H2.ghost_pts_to;
    iname = unit;
    iref = unit;
    non_info_iref = (fun x -> reveal x);
    iname_of = (fun x -> ());
    inv;
    iname_ok = (fun _ _ -> True);
    dup_inv_equiv;
    mem_invariant;
    inv_iname_ok = (fun _ _ _ -> ());
    mem_invariant_equiv;
}

let core_ghost_ref_as_addr (r:core_ghost_ref)
: GTot nat
= H2.core_ghost_ref_as_addr r

let select_ghost i m = H2.select_ghost i m
let ghost_ctr m = m.ghost_ctr
let mem_invariant_interp (ex:inames base_heap) (h0:base_heap.mem) (h1:base_heap.sep.core)
: Lemma (base_heap.interp (base_heap.mem_invariant ex h0) h1 ==>
         free_above_ghost_ctr h0)
= base_heap.pure_interp (free_above h0) h1;
  H2.reveal_free_above_addr GHOST h0.heap h0.ghost_ctr
let inames_ok_trivial (ex:inames base_heap) (h:base_heap.mem)
: Lemma (inames_ok ex h)
= ()
let interp_ghost_pts_to i #meta #a #pcm v h0 = H2.interp_ghost_pts_to i #meta #a #pcm v h0.heap
let ghost_pts_to_compatible_equiv = H2.ghost_pts_to_compatible_equiv

(* Lifting H2 actions *)
let mg_of_mut (m:Tags.mutability) =
  match m with
  | Tags.MUTABLE -> false
  | _ -> true


let elim_init (e:_) (fp frame:H2.slprop u#a) (m:base_heap.mem)
: Lemma 
  (requires interpret (fp `star` frame `star` mem_invariant e m) m)
  (ensures interpret fp m /\ interpret (fp `star` frame) m /\ free_above m)
= ac_lemmas base_heap;
  destruct_star #base_heap (fp `star` frame) (mem_invariant e m) m.heap;
  destruct_star #base_heap fp frame m.heap;
  FStar.Classical.forall_intro (base_heap.pure_interp (free_above m))

let intro_fin (e:_) (post frame:H2.slprop u#a) (m:base_heap.mem)
: Lemma
  (requires base_heap.interp (post `star` frame) m.heap /\ free_above m)
  (ensures base_heap.interp (post `star` frame `star` mem_invariant e m) m.heap)
= ac_lemmas base_heap;
  intro_pure #base_heap (post `star` frame) (free_above m) () m.heap
              
let lift_heap_action
      (#fp:H2.slprop u#a)
      (#a:Type u#b)
      (#fp':a -> H2.slprop u#a)
      (#mut:_)
      (e:inames base_heap)
      ($f:H2.action #mut #None fp a fp')
: act:_action_except base_heap a (mg_of_mut mut) e fp fp'
  {
     mut == IMMUTABLE ==> preserves_inames act  
  }
= let act : _action_except base_heap a (mg_of_mut mut) e fp fp' =
    fun frame m0 ->
      elim_init e fp frame m0;
      let h0 = m0.heap in
      let (| x, h1 |) = f h0 in
      assert (base_heap.interp (fp' x `star` frame) h1);
      let m1 = {m0 with heap=h1} in
      assert (H2.action_related_heaps #mut #None h0 h1);
      assert (H2.does_not_allocate CONCRETE h0 h1);
      assert (H2.does_not_allocate GHOST h0 h1);
      assert (free_above m1);
      intro_fin e (fp' x) frame m1;
      assert (maybe_ghost_action base_heap (mg_of_mut mut) m0 m1);
      assert (inames_ok e m1);
      (x, m1)
  in
  match mut with
  | IMMUTABLE ->
    introduce forall (m0:full_mem base_heap) frame. 
      interpret (fp `base_heap.star` frame `base_heap.star` base_heap.mem_invariant e m0) m0 /\
      inames_ok e m0
      ==> ( 
      let x, m1 = act frame m0 in
      heaps_preserve_inames m0 m1
    )
    with introduce _ ==> _ 
    with _. ( 
      let x, m1 = act frame m0 in
      elim_init e fp frame m0;
      H2.action_framing f frame m0.heap;
      assert (H2.action_related_heaps #IMMUTABLE #None m0.heap m1.heap);
      assert (m0 == m1);
      assert (heaps_preserve_inames m0 m1)
    );
    act
  | _ -> act

let with_fresh_ghost_counter (#t:Type u#t) (#post:t -> slprop u#a) (e:inames base_heap)
  (f: (addr:erased nat ->
        H2.action #ONLY_GHOST #(Some GHOST)
          #(fun h -> h `H2.free_above_addr GHOST` addr)
          #(fun h -> h `H2.free_above_addr GHOST` (addr + 1))      
          H2.emp 
          t
          post))
: ghost_action_except base_heap t e emp post
= fun frame m0 ->
    elim_init e emp frame m0;
    let h0 = m0.heap in
    let (|r, h1|) = f m0.ghost_ctr h0 in
    let m1 = {m0 with heap=h1; ghost_ctr=m0.ghost_ctr + 1} in
    intro_fin e (post r) frame m1;
    r, m1

let ghost_extend_alt
    (meta:erased bool)
    (#ex:inames base_heap)
    (#a:Type u#a)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: ghost_action_except base_heap (ghost_ref a pcm) ex    
        base_heap.emp 
        (fun r -> base_heap.ghost_pts_to meta r x)
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
      (forall (a:nat).
         a <> ghost_ctr h ==>
         select_ghost a (core_of h) == select_ghost a (core_of h1)) /\
      ghost_ctr h1 == ghost_ctr h + 1 /\
      select_ghost (ghost_ctr h) (core_of h1) == Some (H.Ref meta a pcm x) /\
      ghost_ctr h == core_ghost_ref_as_addr r
  )
= let act = ghost_extend_alt meta #ex #a #pcm x in
  let _, m1 = act frame h in
  elim_init ex emp frame h;
  H2.ghost_extend_spec #meta #a #pcm x h.ghost_ctr h.heap

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
      elim_init ex emp frame m0;
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
          (base_heap.ghost_pts_to meta r x)
          (fun _ -> base_heap.ghost_pts_to meta r y)
      = lift_heap_action ex (H2.ghost_write #meta #a #p r x y f)
    in
    introduce reveal meta == false ==> preserves_inames act
    with _ . (
      introduce forall (m0:full_mem base_heap) frame. 
        interpret ((base_heap.ghost_pts_to meta r x) `base_heap.star` frame `base_heap.star` base_heap.mem_invariant ex m0) m0 /\
        inames_ok ex m0
          ==> ( 
          let x, m1 = act frame m0 in
          heaps_preserve_inames m0 m1
        )
      with introduce _ ==> _ 
      with _. ( 
        let _, m1 = act frame m0 in
        elim_init ex (base_heap.ghost_pts_to meta r x) frame m0;
        H2.ghost_write_modifies #meta #a #p r x y f m0.heap;
        match (H2.select_ghost (H2.core_ghost_ref_as_addr r) m0.heap) with
        | None -> ()
        | Some (H.Ref meta' _ _ _) -> 
          assert (reveal meta == false);
          assert (base_heap.interp (base_heap.ghost_pts_to meta r x) m0.heap);
          interp_ghost_pts_to r #meta #a #p x m0;
          assert (reveal meta' == false)
      )
    );
    act
let ghost_share #ex #meta #a #p r x y = lift_heap_action ex (H2.ghost_share #meta #a #p r x y)
let ghost_gather #ex #meta #a #p r x y = lift_heap_action ex (H2.ghost_gather #meta #a #p r x y)

let with_fresh_counter (#t:Type u#t) (#post:t -> slprop u#a) (e:inames base_heap)
  (f: (addr:nat ->
        H2.action #MUTABLE #(Some CONCRETE)
          #(fun h -> h `H2.free_above_addr CONCRETE` addr)
          #(fun h -> h `H2.free_above_addr CONCRETE` (addr + 1))      
          H2.emp 
          t
          post))
: action_except base_heap t e emp post
= fun frame m0 ->
    elim_init e emp frame m0;
    let h0 = m0.heap in
    let (|r, h1|) = f m0.ctr h0 in
    let m1 = {m0 with heap=h1; ctr=m0.ctr + 1} in
    intro_fin e (post r) frame m1;
    r, m1

let extend_alt #ex #a #pcm (x:a {pcm.refine x})
  : action_except base_heap (ref a pcm) ex    
        base_heap.emp 
        (fun r -> base_heap.pts_to r x)
  = with_fresh_counter ex (H2.extend #a #pcm x)
let extend #ex #a #pcm (x:a {pcm.refine x})
: act:action_except base_heap (ref a pcm) ex    
          base_heap.emp 
          (fun r -> base_heap.pts_to r x) {
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
    elim_init ex base_heap.emp frame m0;
    H2.extend_modifies #a #pcm x m0.ctr m0.heap
  );
  act


let read #ex #a #p r x f = lift_heap_action ex (H2.select_refine #a #p r x f)
let write #ex #a #p r x y f = 
  let act
    : action_except base_heap unit ex
        (base_heap.pts_to r x)
        (fun _ -> base_heap.pts_to r y)
    = lift_heap_action ex (H2.upd_gen_action #a #p r x y f)
  in
  FStar.Classical.forall_intro_2 H2.select_ghost_interp;
  introduce forall (m0:full_mem base_heap) frame. 
  interpret ((base_heap.pts_to r x) `base_heap.star` frame `base_heap.star` base_heap.mem_invariant ex m0) m0 /\
  inames_ok ex m0
    ==> ( 
    let x, m1 = act frame m0 in
    heaps_preserve_inames m0 m1
  )
  with introduce _ ==> _ 
  with _. ( 
    let _, m1 = act frame m0 in
    elim_init ex (base_heap.pts_to r x) frame m0;
    H2.upd_gen_modifies #a #p r x y f m0.heap;
    assert (H2.ghost m0.heap == H2.ghost m1.heap);
    ()
  );
  act
let share #ex #a #p r x y = lift_heap_action ex (H2.split_action #a #p r x y)
let gather #ex #a #p r x y = lift_heap_action ex (H2.gather_action #a #p r x y)
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