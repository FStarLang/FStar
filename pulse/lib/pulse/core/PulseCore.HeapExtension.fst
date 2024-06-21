module PulseCore.HeapExtension
open PulseCore.HeapSig
open FStar.Ghost
open FStar.PCM
open FStar.FunctionalExtensionality
module H = PulseCore.Heap
module H2 = PulseCore.BaseHeapSig
module F = FStar.FunctionalExtensionality
module PA = PulseCore.PCM.Agreement

let base_heap_mem : Type u#(a + 1) = (H2.base_heap u#a).mem
let base_heap_core : Type u#(a + 1) = (H2.base_heap u#a).sep.core
let base_slprop : Type u#(a + 1) = (H2.base_heap u#a).slprop

noeq
type core (h:heap_sig u#a) : Type u#(a + 2) = {
    small_core : h.sep.core;
    big_core : base_heap_core u#(a + 1);
}

noeq
type ext_mem (h:heap_sig u#a) : Type u#(a + 2) = {
    small : h.mem;
    big : base_heap_mem u#(a + 1);
    ctr : nat;
//    ghost_ctr: erased nat;
}

(* A lens between mem and core *)
let get_core (#h:heap_sig u#h) (m:ext_mem h) : core h = {
    small_core = core_of m.small;
    big_core = core_of m.big;
}

let put_core (#h:heap_sig u#h) (c:core h) (m:ext_mem h) : ext_mem h = {
    small = h.sep.lens_core.put c.small_core m.small;
    big = H2.base_heap.sep.lens_core.put c.big_core m.big;
    ctr = m.ctr;
    // ghost_ctr = m.ghost_ctr;
}

let get_put (#h:heap_sig u#h) (m:ext_mem h)
: Lemma (put_core (get_core m) m == m)
= h.sep.lens_core.get_put m.small;
  H2.base_heap.sep.lens_core.get_put m.big

let put_get (#h:heap_sig u#h) (c:core h) (m:ext_mem h)
: Lemma (get_core (put_core c m) == c)
= h.sep.lens_core.put_get c.small_core m.small;
  H2.base_heap.sep.lens_core.put_get c.big_core m.big

let put_put (#h:heap_sig u#h) (c1 c2:core h) (m:ext_mem h)
: Lemma (put_core c2 (put_core c1 m) == put_core c2 m)
= h.sep.lens_core.put_put c1.small_core c2.small_core m.small;
  H2.base_heap.sep.lens_core.put_put c1.big_core c2.big_core m.big

let lens_core (h:heap_sig u#a) : lens (ext_mem h) (core h) = {
    get = get_core #h;
    put = put_core #h;
    get_put = get_put #h;
    put_get = put_get #h;
    put_put = put_put #h;
}

let empty (#h:heap_sig u#a) : core h = {
    small_core = h.sep.empty;
    big_core = H2.base_heap.sep.empty;
}

let disjoint (#h:heap_sig u#a) (m1 m2:core h)
: prop
= h.sep.disjoint m1.small_core m2.small_core /\
  H2.base_heap.sep.disjoint m1.big_core m2.big_core

let join (#h:heap_sig u#a) (m1:core h) (m2:core h { disjoint m1 m2 })
: core h
= {
    small_core = h.sep.join m1.small_core m2.small_core;
    big_core = H2.base_heap.sep.join m1.big_core m2.big_core;
  }

let disjoint_sym (#h:heap_sig u#a) (m1 m2:core h)
: Lemma (disjoint m1 m2 <==> disjoint m2 m1)
        [SMTPat (disjoint m1 m2)]
= h.sep.disjoint_sym m1.small_core m2.small_core;
  H2.base_heap.sep.disjoint_sym m1.big_core m2.big_core

let join_commutative (#h:heap_sig u#a) (m1:core h) (m2:core h { disjoint m1 m2 })
: Lemma (join m1 m2 == join m2 m1)
        [SMTPat (join m1 m2)]
= h.sep.join_commutative m1.small_core m2.small_core;
  H2.base_heap.sep.join_commutative m1.big_core m2.big_core

let disjoint_join (#h:heap_sig u#a) (m0 m1 m2:core h)
: Lemma (
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2) ==>
        disjoint m0 m1 /\
        disjoint m0 m2 /\
        disjoint (join m0 m1) m2 /\
        disjoint (join m0 m2) m1)
= h.sep.disjoint_join m0.small_core m1.small_core m2.small_core;
  H2.base_heap.sep.disjoint_join m0.big_core m1.big_core m2.big_core

let join_associative (#h:heap_sig u#a) 
        (m0:core h)
        (m1:core h)
        (m2:core h { disjoint m1 m2 /\ disjoint m0 (join m1 m2) })
: Lemma (disjoint m0 m1 /\
         disjoint (join m0 m1) m2 /\
         join m0 (join m1 m2) == join (join m0 m1) m2)
= h.sep.join_associative m0.small_core m1.small_core m2.small_core;
  H2.base_heap.sep.join_associative m0.big_core m1.big_core m2.big_core

let join_associative2 (#h:heap_sig u#a) (m0 m1 m2:core h)
  : Lemma
    (requires
      disjoint m0 m1 /\
      disjoint (join m0 m1) m2)
    (ensures
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2) /\
      join m0 (join m1 m2) == join (join m0 m1) m2)
    [SMTPat (join (join m0 m1) m2)]
  = disjoint_join m2 m0 m1;
    join_commutative m2 m1;
    join_associative m0 m1 m2

let join_empty (#h:heap_sig u#a) (m:core h)
: Lemma (disjoint m (empty #h) /\ join m (empty #h) == m)
        [SMTPatOr [
          [SMTPat (disjoint m (empty#h))];
          [SMTPat (join m (empty #h))]]]
= h.sep.join_empty m.small_core;
  H2.base_heap.sep.join_empty m.big_core

let ext_sep (h:heap_sig u#a)
: separable (ext_mem h)
= {
    core = core h;
    lens_core = lens_core h;
    empty = empty #h;
    disjoint = disjoint #h;
    join = join #h;
    disjoint_sym = disjoint_sym #h;
    join_commutative = join_commutative #h;
    disjoint_join = disjoint_join #h;
    join_associative = join_associative #h;
    join_empty = join_empty #h;
    join_empty_inverse = (fun m0 m1 ->
      h.sep.join_empty_inverse m0.small_core m1.small_core;
      H2.base_heap.sep.join_empty_inverse m0.big_core m1.big_core
    )
  }

let full_mem_pred (h:heap_sig u#a) (m:ext_mem h) : prop =
    h.full_mem_pred m.small /\
    H2.base_heap.full_mem_pred m.big

let is_ghost_action (h:heap_sig u#a) (m0 m1:ext_mem h) : prop =
    h.is_ghost_action m0.small m1.small /\
    H2.base_heap.is_ghost_action m0.big m1.big /\
    m0.ctr == m1.ctr

let ext_affine_mem_prop (#m:Type u#a) (sep:separable m)
: Type u#(max 1 a)
= p:(sep.core ^-> prop){ is_affine_mem_prop sep p }

let ext_slprop (h:heap_sig u#a) : Type u#(a + 2) = ext_affine_mem_prop (ext_sep h)
let is_restricted_any (#a #b:Type) (f:a ^-> b) : Lemma (F.is_restricted a f) = ()
let slprop_is_restricted (#h:heap_sig u#a) (p:ext_slprop h) 
: Lemma (is_restricted (ext_sep h).core p)
= is_restricted_any p
let interp (#h:heap_sig u#a) (p:ext_slprop h) : affine_mem_prop (ext_sep h) = p
let as_slprop (#h:heap_sig u#a) (p:affine_mem_prop (ext_sep h)) : ext_slprop h = F.on _ p
let equiv (#h:heap_sig u#a) (p1 p2:ext_slprop h) : prop = forall c. interp p1 c <==> interp p2 c
let slprop_extensionality (h:heap_sig u#a) (p1 p2:ext_slprop h)
: Lemma ((forall c. (interp p1 c <==> interp p2 c)) ==> p1 == p2)
        [SMTPat (equiv p1 p2)]
= introduce (forall (c:(ext_sep h).core). (interp p1 c <==> interp p2 c)) ==> p1 == p2
  with _ . (
    FStar.PredicateExtensionality.predicateExtensionality (ext_sep h).core p1 p2;
    slprop_is_restricted p1;
    slprop_is_restricted p2
  )

let non_info_slprop (h:heap_sig u#a) : non_info (ext_slprop h) = fun x -> reveal x
let bprop (h:heap_sig u#a)  : Type u#(a + 1) = h.slprop

let up_p (#h:heap_sig u#a) (p:h.slprop)
: core h -> prop 
= fun c -> h.interp p c.small_core
let up_p_affine (#h:heap_sig u#a) (p:h.slprop)
: Lemma (is_affine_mem_prop (ext_sep h) (up_p #h p))
= ()
let up (#h:heap_sig u#a) (b:h.slprop) : ext_slprop h = as_slprop #h (up_p b)

let down_p (#h:heap_sig u#a) (p:ext_slprop h)
: h.sep.core -> prop
= fun h -> p { small_core = h; big_core = H2.base_heap.sep.empty }

let down_p_affine (#h:heap_sig u#a) (p:ext_slprop h)
: Lemma (is_affine_mem_prop h.sep (down_p #h p))
= introduce 
    forall (h1 h2:h.sep.core).
      down_p p h1 /\ h.sep.disjoint h1 h2 ==> down_p p (h.sep.join h1 h2)
  with introduce _ ==> _
  with _ . (
    assert (down_p p h1);
    let h1_ = { small_core = h1; big_core = H2.base_heap.sep.empty } in
    assert (p h1_);
    let h2_ = { small_core = h2; big_core = H2.base_heap.sep.empty } in
    H2.base_heap.sep.join_empty H2.base_heap.sep.empty;
    assert (disjoint #h h1_ h2_);
    assert ((ext_sep h).disjoint h1_ h2_);
    assert (p (join #h h1_ h2_));
    ()
  )
let down (#h:heap_sig u#a) (p:ext_slprop h) 
: h.slprop
= down_p_affine #h p;
  h.as_slprop (down_p p)

let up_down (#h:heap_sig u#a) (p:h.slprop)
: Lemma (down (up p) == p)
        [SMTPat (down (up p))]
= down_p_affine (up p);
  up_p_affine p;
  introduce forall hh.
    h.interp (down (up p)) hh <==> h.interp p hh
  with  (
    calc (<==>) {
      h.interp (down (up p)) hh;
    (<==>) { h.interp_as (down_p (up p)) }
      down_p (up p) hh;
    (<==>) {}
      down_p (F.on _ (up_p p)) hh;
    (<==>) { h.interp_as (down_p (F.on _ (up_p p))) }
      h.interp p hh;
    };
    ()
  );
  h.slprop_extensionality (down (up p)) p

let non_info_bprop (h:heap_sig u#a) : non_info (bprop h) = h.non_info_slprop
let pure (#h:heap_sig u#a) (p:prop) : ext_slprop h = up (h.pure p)
let emp (#h:heap_sig u#a) : ext_slprop h = up h.emp
let star (#h:heap_sig u#a) (p1 p2:ext_slprop h) 
: ext_slprop h
= as_slprop (fun (c:(ext_sep h).core) ->
    exists (c1 c2 : core h).
      c1 `(ext_sep h).disjoint` c2 /\
      c == (ext_sep h).join c1 c2 /\
      p1 c1 /\
      p2 c2)
let pure_interp (#h:heap_sig u#a) (p:prop) (c:core h) 
: Lemma (interp (pure p) c == p)
= h.pure_interp p c.small_core
let pure_true_emp (#h:heap_sig u#a) (_:unit)
: Lemma (pure #h True == emp #h)
= h.pure_true_emp ()
let intro_emp (#h:heap_sig u#a) (c:core h)
: Lemma (interp (emp #h) c)
= h.intro_emp c.small_core
let emp_unit (#h:heap_sig u#a) (p:ext_slprop h)
: Lemma (p == p `star` emp)
= introduce forall c. 
    (interp p c <==> interp (p `star` emp) c)
  with (
    assert (c == (ext_sep h).join c (empty #h));
    h.intro_emp (empty #h).small_core    
  ); 
  slprop_extensionality h p (p `star` emp)
  
let star_commutative (#h:heap_sig u#a) (p1 p2:ext_slprop h)
: Lemma (p1 `star` p2 == p2 `star` p1)
= assert (equiv (p1 `star` p2) (p2 `star` p1))

#push-options "--z3rlimit_factor 4"
let star_associative (#h:heap_sig u#a) (p1 p2 p3:ext_slprop h)
: Lemma (p1 `star` (p2 `star` p3) == (p1 `star` p2) `star` p3)
= assert (equiv (p1 `star` (p2 `star` p3)) ((p1 `star` p2) `star` p3))
#pop-options


let lift (h:heap_sig u#a) (p:base_slprop u#(a + 1))
: ext_slprop h
= as_slprop (fun c -> H2.base_heap.interp p c.big_core)

let pts_to (h:heap_sig u#a) (#a:Type u#(a + 1)) (#p:pcm a) (r:ref a p) (x:a)
: ext_slprop h
= lift h (H2.base_heap.pts_to #a #p r x)

let ghost_pts_to (h:heap_sig u#a) (meta:bool) (#a:Type u#(a + 1)) (#p:pcm a) (r:ghost_ref a p) (x:a)
: ext_slprop h
= lift h (H2.base_heap.ghost_pts_to meta #a #p r x)

let ext_iname (h:heap_sig u#a) : eqtype = either h.iname nat
let ext_iref (h:heap_sig u#a) : Type0 = erased (either h.iref (ghost_ref _ (PA.pcm_agreement #h.slprop)))
let non_info_iref (h:heap_sig u#a) : non_info (ext_iref h) = fun x -> reveal x
let iname_of (h:heap_sig u#a) (r:ext_iref h) : GTot (ext_iname h) =
  match r with
  | Inl i -> Inl (h.iname_of i)
  | Inr r -> Inr (H2.core_ghost_ref_as_addr r)
let is_boxable_ext (#h:heap_sig u#a) (p:ext_slprop h) = up (down p) == p
let inv_core (#h:heap_sig u#a) (i:ghost_ref _ (PA.pcm_agreement #h.slprop)) (p:ext_slprop h)
: ext_slprop h
= lift h (H2.base_heap.ghost_pts_to true #_ #(PA.pcm_agreement #h.slprop) i (Some (down p)))
let inv (#h:heap_sig u#a) (i:ext_iref h) (p:ext_slprop h)
: ext_slprop h
= match i with
  | Inl i -> up (h.inv i (down p)) `star` pure (is_boxable_ext p)
  | Inr r -> inv_core r p `star` pure (is_boxable_ext p)

let iname_ok (h:heap_sig u#a) (i:ext_iname h) (m:ext_mem h) : prop =
  match i with
  | Inl i -> h.iname_ok i m.small
  | Inr i -> Some? (H2.select_ghost i (core_of m.big))

let down_inames (#h:heap_sig u#h) (e:eset (ext_iname h))
: inames h
= let e = Ghost.reveal e in
  FStar.Set.intension (fun i -> Set.mem (Inl i) e)


let mem_intension (#a:eqtype) (x:a) (f:(a -> Tot bool))
: Lemma 
  (ensures (Set.mem x (Set.intension f) = f x))
  [SMTPat (Set.mem x (Set.intension f))]
= FStar.Set.mem_intension x f

let mem_down_inames (#h:heap_sig u#h) (i:h.iname) (e:eset (ext_iname h))
: Lemma (i `Set.mem` down_inames e <==> Inl i `Set.mem` e)
= ()

let sl_pure_imp (#h:heap_sig u#h) (p:prop) (q: squash p -> ext_slprop h) : ext_slprop h =
  as_slprop (fun m -> p ==> interp (q ()) m)

let cell_pred_pre (h:heap_sig u#h) (c:H.cell) =
  let H.Ref meta a pcm _ = c in
  reveal meta == true /\
  a == PA.agreement h.slprop /\
  pcm == PA.pcm_agreement #h.slprop

let cell_pred_post (h:heap_sig u#h) (c:H.cell) (_:squash (cell_pred_pre h c)) =
  let H.Ref _ _ _ v = c in
  let v : PA.agreement h.slprop = v in
  match v with
  | None -> emp
  | Some p -> up p

let invariant_of_one_cell
      (#h:heap_sig u#a)
      (addr:nat)
      (e:eset (ext_iname h))
      (m:base_heap_core u#(a + 1))
: ext_slprop h
= if Inr addr `Set.mem` e then emp
  else match H2.select_ghost addr m with
       | Some c -> 
         sl_pure_imp
          (cell_pred_pre h c)
          (cell_pred_post h c)
       | _ -> emp

let rec istore_invariant
         (#h:heap_sig u#a)
         (from:nat)
         (e:eset (ext_iname h))
         (l:base_heap_core u#(a + 1))
: ext_slprop h
= invariant_of_one_cell from e l `star` 
  (if from = 0 then emp else istore_invariant (from - 1) e l)

let mem_invariant (#h:heap_sig u#a) (e:eset (ext_iname h)) (m:ext_mem h)
: ext_slprop h
= up (h.mem_invariant (down_inames e) m.small) `star`
  istore_invariant #h (H2.ghost_ctr m.big) e (core_of m.big) `star`
  lift h (H2.base_heap.mem_invariant Set.empty m.big)

let share_gather_equiv #meta (#a:_) (#p:pcm a) (r:ghost_ref a p) (v0:a) (v1:a{composable p v0 v1})
: Lemma (H2.base_heap.ghost_pts_to meta r (v0 `op p` v1) == 
         H2.base_heap.ghost_pts_to meta r v0 `H2.base_heap.star` H2.base_heap.ghost_pts_to meta r v1)
= H2.ghost_pts_to_compatible_equiv #meta r v0 v1

let up_star_ext (#h:heap_sig u#a) (p q:h.slprop)
: Lemma (up (p `h.star` q) == (up p `star` up q))
        [SMTPat (up (p `h.star` q))]
= introduce forall m.
      up (p `h.star` q) m ==>
      (up p `star` up q) m
  with introduce _ ==> _
  with _ . (
    h.star_equiv p q m.small_core;
    eliminate exists m1 m2.
      h.sep.disjoint m1 m2 /\
      m.small_core == h.sep.join m1 m2 /\
      h.interp p m1 /\
      h.interp q m2
    returns (up p `star` up q) m
    with _ . (
      let ml = { m with small_core = m1 } in
      let mr = { m with small_core = m2; big_core = H2.base_heap.sep.empty } in
      H2.base_heap.sep.join_empty m.big_core;
      assert (disjoint ml mr);
      assert (m == join ml mr);
      assert (up p ml);
      assert (up q mr);
      assert ((ext_sep h).disjoint ml mr)
    )
  );
  introduce forall m.
      (up p `star` up q) m ==>
      up (p `h.star` q) m
  with introduce _ ==> _
  with _ . (
    eliminate exists m1 m2.
      disjoint m1 m2 /\
      m == join m1 m2 /\
      up p m1 /\
      up q m2
    returns up (p `h.star` q) m
    with _ . (
      h.star_equiv p q m.small_core
    )    
  );
  slprop_extensionality _ (up (p `h.star` q)) (up p `star` up q)

let lift_star (#h:heap_sig u#a) (p q:base_slprop u#(a + 1))
: Lemma (lift h (p `H2.base_heap.star` q) == lift h p `star` lift h q)
= introduce forall (m:core h). 
    (lift h (p `H2.base_heap.star` q)) m ==>
    (lift h p `star` lift h q) m
  with introduce _ ==> _
  with _ . ( 
    H2.base_heap.star_equiv p q m.big_core;
    eliminate exists (m0 m1:base_heap_core).
      H2.base_heap.sep.disjoint m0 m1 /\
      m.big_core == H2.base_heap.sep.join m0 m1 /\
      H2.base_heap.interp p m0 /\
      H2.base_heap.interp q m1
    returns (lift h p `star` lift h q) m
    with _ . (
      let ml = { m with big_core = m0 } in
      let mr = { small_core = h.sep.empty; big_core = m1 } in
      h.sep.join_empty m.small_core;
      assert ((ext_sep h).disjoint ml mr);
      assert (lift h p ml);
      assert (lift h q mr)
    )
  );
  introduce forall m.
    (lift h p `star` lift h q) m ==>
    (lift h (p `H2.base_heap.star` q)) m
  with (
    H2.base_heap.star_equiv p q m.big_core
  );
  slprop_extensionality _ (lift h (p `H2.base_heap.star` q)) (lift h p `star` lift h q)

let dup_pure_core (#h:heap_sig u#a) (p:prop)
: Lemma (h.pure p == h.pure p `h.star` h.pure p)
= FStar.Classical.forall_intro (h.star_equiv (h.pure p) (h.pure p));
  FStar.Classical.forall_intro (h.pure_interp p);
  FStar.Classical.forall_intro h.sep.join_empty ;
  h.slprop_extensionality (h.pure p) (h.pure p `h.star` h.pure p)

let dup_pure (#h:heap_sig u#a) (p:prop)
: Lemma (pure #h p == pure #h p `star` pure #h p)
= dup_pure_core #h p;
  up_star_ext (h.pure p) (h.pure p) 

let ac_lemmas_ext (h:heap_sig u#a)
: Lemma (
    (forall (p q r:ext_slprop h). (p `star` q) `star` r == p `star` (q `star` r)) /\
    (forall (p q:ext_slprop h). p `star` q == q `star` p) /\
    (forall (p:ext_slprop h). p `star` emp == p)
) = FStar.Classical.forall_intro_3 (star_associative #h);
    FStar.Classical.forall_intro_2 (star_commutative #h);
    FStar.Classical.forall_intro (emp_unit #h)

let dup_inv_equiv (#h:heap_sig u#a) (i:ext_iref h) (p:ext_slprop h)
: Lemma (inv i p == inv i p `star` inv i p)
= match i with
  | Inl j ->
    calc (==) {
      inv i p;
    (==) { }
      up (h.inv j (down p)) `star` pure (is_boxable_ext p);
    (==) {h.dup_inv_equiv j (down p); dup_pure #h (is_boxable_ext p)}
      (up (h.inv j (down p) `h.star` h.inv j (down p))) `star`
      (pure (is_boxable_ext p) `star` pure (is_boxable_ext p));
    (==) { up_star_ext (h.inv j (down p)) (h.inv j (down p)); ac_lemmas_ext h}
      inv i p `star` inv i p;
    }

  | Inr j -> 
    calc (==) {
      inv i p;
    (==) {}
      inv_core j p `star` pure (is_boxable_ext p);
    (==) {  share_gather_equiv #true #_ #(PA.pcm_agreement #h.slprop) j (Some (down p)) (Some (down p)) }
      lift h (H2.base_heap.ghost_pts_to true #_ #(PA.pcm_agreement #h.slprop) j (Some (down p)) `H2.base_heap.star`
              H2.base_heap.ghost_pts_to true #_ #(PA.pcm_agreement #h.slprop) j (Some (down p))) `star` pure (is_boxable_ext p);
    (==) { lift_star #h (H2.base_heap.ghost_pts_to true #_ #(PA.pcm_agreement #h.slprop) j (Some (down p)))
                        (H2.base_heap.ghost_pts_to true #_ #(PA.pcm_agreement #h.slprop) j (Some (down p))) }
      (inv_core j p `star` inv_core j p) `star` pure (is_boxable_ext p);
    (==) { dup_pure #( h) (is_boxable_ext p) }
      (inv_core j p `star` inv_core j p) `star` (pure (is_boxable_ext p) `star` pure (is_boxable_ext p));
    (==) { ac_lemmas_ext h }
      inv i p `star` inv i p;
    }

let iname_ok_ext (#h:heap_sig u#a) (i:ext_iref h) (p:ext_slprop h) (m:ext_mem h)
: Lemma 
  (requires interp (inv i p) (get_core m))
  (ensures iname_ok h (iname_of h i) m)
= match i with
  | Inl j -> h.inv_iname_ok j (down p) m.small
  | Inr j -> H2.interp_ghost_pts_to j #true #_ #(PA.pcm_agreement #h.slprop) (Some (down p)) m.big

let rec istore_invariant_unchanged (#h:heap_sig u#a)
         (from:nat) 
         (e:eset (ext_iname h))
         (l:base_heap_core u#(a + 1))
         (j:ext_iname h { Inl? j })
: Lemma
  (ensures
    istore_invariant #h from e l ==
    istore_invariant #h from (Set.add j e) l)
= if from = 0 then () else istore_invariant_unchanged #h (from - 1) e l j

let inv_i_p_property 
      (#h:heap_sig u#a)
      (i:ext_iref h {Inr? i})
      (p:ext_slprop h)
      (l:base_heap_core u#(a + 1))
= let Inr i = i in
  H2.base_heap.interp
    (H2.base_heap.ghost_pts_to true #_ #(PA.pcm_agreement #h.slprop) i (Some (down p))) l /\
  is_boxable_ext p

let istore_invariant_eq_aux
      (#h:heap_sig u#a)
      (from:nat) 
      (e:eset (ext_iname h))
      (i:ext_iref h { Inr? i })
      (p:ext_slprop h)
      (l:base_heap_core u#(a + 1) { inv_i_p_property i p l })
: Lemma
  (requires not (iname_of h i `Set.mem` e))
  (ensures
    istore_invariant #h from e l ==
    istore_invariant #h from (Set.add (iname_of h i) e) l `star` p)
= admit()

let istore_invariant_eq
      (#h:heap_sig u#a)
      (m:ext_mem h)
      (e:eset (ext_iname h))
      (i:ext_iref h { Inr? i })
      (p:ext_slprop h)
: Lemma
  (requires not (iname_of h i `Set.mem` e))
  (ensures
    istore_invariant #h (H2.ghost_ctr m.big) e (core_of m.big) `star` inv i p==
    istore_invariant #h (H2.ghost_ctr m.big) (Set.add (iname_of h i) e) (core_of m.big) `star` p `star` inv i p)
= admit()

let hmem_invariant_unchanged
      (#h:heap_sig u#a)
      (e:eset (ext_iname h))
      (m:h.mem)
      (j:ext_iname h{Inr? j})
: Lemma
  (ensures
    h.mem_invariant (down_inames e) m ==
    h.mem_invariant (down_inames <| Set.add j e) m)
= assert (Set.equal (down_inames e) (down_inames (Set.add j e)))

let inv_boxes (#h:heap_sig u#a) (i:ext_iref h) (p:ext_slprop h)
: Lemma (up (down p) `star` inv i p == p `star` inv i p)
=   introduce forall m. 
      interp (up (down p) `star` inv i p) m ==> 
      interp (p `star` inv i p) m
    with introduce _ ==> _
    with _ . (
      pure_interp (is_boxable_ext p) m
    );
    introduce forall m. 
      interp (p `star `inv i p) m ==> 
      interp (up (down p) `star` inv i p) m
    with introduce _ ==> _
    with _ . (
      pure_interp (is_boxable_ext p) m
    );
    slprop_extensionality h (up (down p) `star` inv i p) (p `star` inv i p)

let ghost_ctr (#h:heap_sig) (m:ext_mem h) : GTot nat = H2.ghost_ctr m.big

#push-options "--fuel 0 --ifuel 0 --z3rlimit_factor 4"
let mem_invariant_equiv_ext_l
      (#h:heap_sig)
      (e:eset (ext_iname h))
      (m:ext_mem h)
      (i:ext_iref h { Inl? i }) 
      (p:ext_slprop h)
: Lemma 
  (requires
    not (iname_of h i `Set.mem` e))
  (ensures
    mem_invariant e m `star` inv i p ==
    mem_invariant (Set.add (iname_of h i) e) m `star` p `star` inv i p)
= let Inl j = i in
  calc (==) {
    mem_invariant e m `star` inv i p;
  (==) { }
    (up (h.mem_invariant (down_inames e) m.small) `star`
     istore_invariant #h (ghost_ctr m) e (core_of m.big) `star`
     lift h (H2.base_heap.mem_invariant Set.empty m.big)) `star` inv i p;
  (==) { istore_invariant_unchanged #h (ghost_ctr m) e (core_of m.big) (iname_of h i) }
    (up (h.mem_invariant (down_inames e) m.small) `star`
      istore_invariant #h (ghost_ctr m) (Set.add (iname_of h i) e) (core_of m.big) `star`
      lift h (H2.base_heap.mem_invariant Set.empty m.big)
      ) `star` inv i p;
  (==) { ac_lemmas_ext h}
    (up (h.mem_invariant (down_inames e) m.small) `star` inv i p) `star`
      istore_invariant #h (ghost_ctr m) (Set.add (iname_of h i) e) (core_of m.big) `star`
      lift h (H2.base_heap.mem_invariant Set.empty m.big);
  (==) { }
  (up (h.mem_invariant (down_inames e) m.small) `star` (up (h.inv j (down p)) `star` pure (is_boxable_ext p))) `star`
      istore_invariant #h (ghost_ctr m) (Set.add (iname_of h i) e) (core_of m.big) `star`
      lift h (H2.base_heap.mem_invariant Set.empty m.big);
  (==) {ac_lemmas_ext h}
  (up (h.mem_invariant (down_inames e) m.small) `star` up (h.inv j (down p))) `star`
      (istore_invariant #h (ghost_ctr m) (Set.add (iname_of h i) e) (core_of m.big) 
      `star` 
      lift h (H2.base_heap.mem_invariant Set.empty m.big) `star`
      pure (is_boxable_ext p));
  (==) { up_star_ext (h.mem_invariant (down_inames e) m.small) (h.inv j (down p)) }
    (up (h.mem_invariant (down_inames e) m.small `h.star` h.inv j (down p))) `star`
      (istore_invariant #h (ghost_ctr m) (Set.add (iname_of h i) e) (core_of m.big) 
      `star` 
      lift h (H2.base_heap.mem_invariant Set.empty m.big) `star`
      pure (is_boxable_ext p));
  (==) { h.mem_invariant_equiv (down_inames e) m.small j (down p) }
    (up (h.mem_invariant (Set.add (h.iname_of j) (down_inames e)) m.small 
          `h.star` down p `h.star` h.inv j (down p))) `star`
      (istore_invariant #h (ghost_ctr m) (Set.add (iname_of h i) e) (core_of m.big)
      `star` 
      lift h (H2.base_heap.mem_invariant Set.empty m.big) `star`
      pure (is_boxable_ext p));
  (==) { assert (Set.equal (Set.add (h.iname_of j) (down_inames e))
                            (down_inames (Set.add (iname_of h i) e))) }
    (up ((h.mem_invariant (down_inames (Set.add (iname_of h i) e)) m.small 
          `h.star` down p) `h.star` h.inv j (down p))) `star`
      (istore_invariant #h (ghost_ctr m) (Set.add (iname_of h i) e) (core_of m.big)
      `star` 
      lift h (H2.base_heap.mem_invariant Set.empty m.big) `star`
      pure (is_boxable_ext p));
  (==) { up_star_ext (h.mem_invariant (down_inames (Set.add (iname_of h i) e)) m.small `h.star` down p)
                  (h.inv j (down p));
          ac_lemmas_ext h}
    (up (h.mem_invariant (down_inames (Set.add (iname_of h i) e)) m.small 
          `h.star` down p) `star` inv i p) `star`
      istore_invariant #h (ghost_ctr m) (Set.add (iname_of h i) e) (core_of m.big) `star`
      lift h (H2.base_heap.mem_invariant Set.empty m.big);
  (==) { up_star_ext (h.mem_invariant (down_inames (Set.add (iname_of h i) e)) m.small) (down p) }
    (up (h.mem_invariant (down_inames (Set.add (iname_of h i) e)) m.small) `star` up (down p)) `star`
      inv i p `star` istore_invariant #h (ghost_ctr m) (Set.add (iname_of h i) e) (core_of m.big) `star`
      lift h (H2.base_heap.mem_invariant Set.empty m.big);
  (==) { ac_lemmas_ext h }
    mem_invariant (Set.add (iname_of h i) e) m `star` (up (down p) `star` inv i p);
  (==) { inv_boxes i p; ac_lemmas_ext h }
    mem_invariant (Set.add (iname_of h i) e) m `star` p `star` inv i p;
  }
#pop-options

let mem_invariant_equiv_ext_r
      (#h:heap_sig)
      (e:eset (ext_iname h))
      (m:ext_mem h)
      (i:ext_iref h { Inr? i }) 
      (p:ext_slprop h)
: Lemma 
  (requires
    not (iname_of h i `Set.mem` e))
  (ensures
    mem_invariant e m `star` inv i p ==
    mem_invariant (Set.add (iname_of h i) e) m `star` p `star` inv i p)
= let Inr j = i in
  calc (==) {
    mem_invariant e m `star` inv i p;
  (==) { }
    (up (h.mem_invariant (down_inames e) m.small) `star`
      istore_invariant #h (ghost_ctr m) e (core_of m.big) `star`
      lift h (H2.base_heap.mem_invariant Set.empty m.big)) `star` inv i p;
  (==) { hmem_invariant_unchanged #h e m.small (iname_of h i); ac_lemmas_ext h }
    up (h.mem_invariant (down_inames (Set.add (iname_of h i) e)) m.small) `star`
    lift h (H2.base_heap.mem_invariant Set.empty m.big) `star`
      (istore_invariant #h (ghost_ctr m) e (core_of m.big) `star` inv i p);
  (==) { istore_invariant_eq #h m e i p; ac_lemmas_ext h }
    up (h.mem_invariant (down_inames (Set.add (iname_of h i) e)) m.small) `star`
    lift h (H2.base_heap.mem_invariant Set.empty m.big) `star`
      (istore_invariant #h (ghost_ctr m) (Set.add (iname_of h i) e) (core_of m.big) `star` p `star` inv i p);
  (==) { ac_lemmas_ext h }
    mem_invariant (Set.add (iname_of h i) e) m `star` p `star` inv i p;  
  }

let mem_invariant_equiv_ext 
      (#h:heap_sig)
      (e:eset (ext_iname h))
      (m:ext_mem h)
      (i:ext_iref h) 
      (p:ext_slprop h)
: Lemma 
  (requires
    not (iname_of h i `Set.mem` e))
  (ensures
    mem_invariant e m `star` inv i p ==
    mem_invariant (Set.add (iname_of h i) e) m `star` p `star` inv i p)
= match i with
  | Inl j -> mem_invariant_equiv_ext_l e m i p
  | Inr j -> mem_invariant_equiv_ext_r e m i p

let star_congruence (#h:heap_sig u#a) (p q:ext_slprop h)
: Lemma
  (requires is_boxable_ext p /\ is_boxable_ext q)
  (ensures is_boxable_ext (p `star` q))
= admit()

let update_ghost (#h:heap_sig u#h) (m0:ext_mem h) (m1:erased (ext_mem h) { is_ghost_action h m0 m1 })
: m:ext_mem h { m == reveal m1 }
= { ctr=m0.ctr;
    small = h.update_ghost m0.small m1.small; 
    big = H2.base_heap.update_ghost m0.big m1.big }

let extend (h:heap_sig u#a) = {
    mem = ext_mem h;
    sep = ext_sep h;
    slprop = ext_slprop h;
    slprop_extensionality = slprop_extensionality h;
    as_slprop = as_slprop #h;
    interp = interp #h;
    interp_as = (fun p -> ());
    full_mem_pred = full_mem_pred h;
    is_ghost_action = is_ghost_action h;
    is_ghost_action_preorder = (fun m -> h.is_ghost_action_preorder (); H2.base_heap.is_ghost_action_preorder ());
    update_ghost = update_ghost #h;
    non_info_slprop = non_info_slprop h;
    bprop = bprop h;
    up = up #h;
    down = down #h;
    up_down = up_down #h;
    non_info_bprop = non_info_bprop h;
    emp = emp;
    pure = pure;
    star = star;
    pure_interp = pure_interp;
    pure_true_emp = pure_true_emp #h;
    emp_unit = emp_unit;
    intro_emp = intro_emp;
    star_commutative = star_commutative;
    star_associative = star_associative;
    star_equiv = (fun p q m -> ());
    star_congruence;
    pts_to = pts_to h;
    ghost_pts_to = ghost_pts_to h;
    iname = ext_iname h;
    iref = ext_iref h;
    non_info_iref = non_info_iref h;
    iname_of = iname_of h;
    inv = inv #h;
    iname_ok = iname_ok h;
    inv_iname_ok = iname_ok_ext #h;
    dup_inv_equiv = dup_inv_equiv #h;
    mem_invariant = mem_invariant;
    mem_invariant_equiv = mem_invariant_equiv_ext #h;
}

let lift_iref (#h:heap_sig u#a) (i:h.iref)
: ext_iref h
= Inl i

let lift_iname (#h:heap_sig u#a) (i:h.iname)
: ext_iname h
= Inl i

irreducible //weird, without this irreducible, F* hangs on lift_action
let lift_inames_body (#h:heap_sig u#a) (is:Set.set h.iname) (a:(extend h).iname)
: b:bool { b <==> (Inl? a /\ Inl?.v a `Set.mem` is) }
= match a with
  | Inl i -> i `Set.mem` is
  | _ -> false

let lift_inames (#h:heap_sig u#a) (is:inames h)
: inames (extend h) 
= let is = Ghost.reveal is in
  FStar.Set.intension (lift_inames_body #h is)

let lower_inames #h = down_inames #h
let down_frame_core
      (#h:heap_sig u#a)
      (p:h.slprop)
      (frame:ext_slprop h)
      (m:ext_mem h { interpret #(extend h) (up p `star` frame) m })
: frame':h.slprop { 
  interpret #h (p `h.star` frame') m.small /\
  (forall (q:h.slprop) (m':h.mem).
    interpret #h (q `h.star` frame') m' ==>
    interpret #(extend h) (up q `star` frame) ({m with small = m'}))
}
=
  eliminate exists (m0:core h)  (m1: core h).
    disjoint m0 m1 /\
    core_of #(extend h) m == join #h m0 m1 /\
    up #h p m0 /\
    frame m1
  returns exists frame'. 
    interpret #h (p `h.star` frame') m.small /\
    (forall (q:h.slprop) (m':h.mem).
      interpret #h (q `h.star` frame') m' ==>
      interpret #(extend h) (up q `star` frame) ({m with small = m'}))
  with _ . (
    let fr (ms:h.sep.core)
      : prop 
      = interp frame { small_core = ms; big_core = m1.big_core }
    in
    let fr_affine ()
    : Lemma (is_affine_mem_prop h.sep fr)
    = introduce forall s0 s1.
        fr s0 /\ h.sep.disjoint s0 s1 ==> fr (h.sep.join s0 s1)
      with introduce _ ==> _
      with _. ( 
        let left = { small_core = s0; big_core = m1.big_core } in
        let right = { small_core = s1; big_core = H2.base_heap.sep.empty } in
        H2.base_heap.sep.join_empty m1.big_core;
        assert (disjoint left right)
      )
    in
    fr_affine();
    let frame' = h.as_slprop fr in
    up_down p;
    assert (h.interp p m0.small_core);
    assert (fr m1.small_core);
    h.interp_as fr;
    assert (h.interp frame' m1.small_core);
    assert (h.sep.disjoint m0.small_core m1.small_core);
    h.star_equiv p frame' (core_of m.small); 
    assert (h.interp (p `h.star` frame') (core_of m.small));
    introduce forall (q:h.slprop) (m':h.mem).
        interpret #h (q `h.star` frame') m' ==>
        interpret #(extend h) (up q `star` frame) ({m with small = m'})
    with introduce _ ==> _
    with _ . (
        h.star_equiv q frame' (core_of m');
        eliminate exists m0' m1'.
          h.sep.disjoint m0' m1' /\
          core_of #h m' == h.sep.join m0' m1' /\
          h.interp q m0' /\
          fr m1'
        returns _
        with _ . (
          let mres = core_of #(extend h) { m with small = m'} in
          introduce exists ml mr.
            disjoint ml mr /\
            mres == join ml mr /\
            up q ml /\
            frame mr
          with ({ small_core=m0'; big_core=m0.big_core}) ({ small_core = m1'; big_core=m1.big_core })
          and  (
            ()
          );
          assert (interpret #(extend h) (up q `star` frame) ({m with small = m'}))
        )
    )
  );
  let frame' =
    FStar.IndefiniteDescription.indefinite_description_tot 
      h.slprop
      (fun frame' ->
        interpret #h (p `h.star` frame') m.small /\
         (forall (q:h.slprop) (m':h.mem).
            interpret #h (q `h.star` frame') m' ==>
            interpret #(extend h) (up q `star` frame) ({m with small = m'})))
  in
  h.non_info_slprop frame'

let down_frame
      (#h:heap_sig u#a)
      (p:h.slprop)
      (frame:ext_slprop h)
      (m:ext_mem h { interpret #(extend h) (up p `star` frame) m })
: frame':h.slprop { interpret #h (p `h.star` frame') m.small } &
  (q:h.slprop -> m':h.mem -> 
    Lemma (requires interpret #h (q `h.star` frame') m')
          (ensures interpret #(extend h) (up q `star` frame) ({m with small = m'})))
= let frame' = down_frame_core p frame m in
  (| frame', (fun q m' -> ()) |)


let down_inames_ok (#h:heap_sig u#a) (ex:inames h) (m:ext_mem h)
: Lemma 
  (ensures inames_ok (lift_inames ex) m <==> inames_ok ex m.small) 
= introduce inames_ok (lift_inames ex) m ==> inames_ok ex m.small
  with _ . (
    introduce forall i. i `Set.mem` ex ==> h.iname_ok i m.small
    with introduce _ ==> _
    with _ . (
      assert (Inl i `Set.mem` lift_inames ex)
    )
  )



let up_down_inames (#h:heap_sig u#a) (i:inames h)
: Lemma (down_inames (lift_inames i) `Set.equal` i)
= ()

let ac_lemmas (h:heap_sig u#a)
: Lemma (
    (forall p q r. (p `h.star` q) `h.star` r == p `h.star` (q `h.star` r)) /\
    (forall p q. p `h.star` q == q `h.star` p) /\
    (forall p. p `h.star` h.emp == p)
)
= FStar.Classical.forall_intro_3 h.star_associative;
  FStar.Classical.forall_intro_2 h.star_commutative;
  FStar.Classical.forall_intro h.emp_unit

let pqrs_pr_qs (h:heap_sig u#a) (p q r s:h.slprop)
: Lemma (
    p `h.star` q `h.star` (r `h.star` s) == (p `h.star` r) `h.star` (q `h.star` s)
)
= ac_lemmas h

let pqr_prq (h:heap_sig u#a) (p q r:h.slprop)
: Lemma ((p `h.star` q) `h.star` r == p `h.star` r `h.star` q)
= ac_lemmas h

module T = FStar.Tactics.V2
#push-options "--fuel 0 --ifuel 0"
let lift_action
    (#h:heap_sig u#h)
    (#a:Type u#a)
    (#mg:bool)
    (#ex:inames h)
    (#pre:h.slprop)
    (#post:a -> h.slprop)
    (action:_action_except h a mg ex pre post)
: _action_except (extend h)
    a mg (lift_inames ex) 
    ((extend h).up pre)
    (fun x -> (extend h).up (post x))
= fun (frame:ext_slprop h) 
      (m0:ext_mem h {
        (extend h).full_mem_pred m0 /\
        inames_ok (lift_inames ex) m0 /\
        interpret #(extend h) (up pre `star` frame `star` mem_invariant (lift_inames ex) m0) m0
       }) ->
        down_inames_ok #h ex m0;
        up_down_inames ex;
        calc (==) {
          up pre `star` frame `star` mem_invariant (lift_inames ex) m0;
        (==) {} 
          up pre `star` frame `star` (up (h.mem_invariant (down_inames (lift_inames ex)) m0.small) `star`
                                      istore_invariant #h (ghost_ctr m0) (lift_inames ex) (core_of m0.big) `star`
                                      lift h (H2.base_heap.mem_invariant Set.empty m0.big));
        (==) { ac_lemmas_ext h } //_ by (T.mapply (quote (pqrs_pr_qs (extend h)))) }
          (up pre `star` up (h.mem_invariant (down_inames (lift_inames ex)) m0.small)) `star` (
           frame `star` istore_invariant #h (ghost_ctr m0) (lift_inames ex) (core_of m0.big) `star`
           lift h (H2.base_heap.mem_invariant Set.empty m0.big)
          );
        (==) { () }
          (up (pre `h.star` h.mem_invariant (down_inames (lift_inames ex)) m0.small)) `star` (
           frame `star` istore_invariant #h (ghost_ctr m0) (lift_inames ex) (core_of m0.big) `star`
           lift h (H2.base_heap.mem_invariant Set.empty m0.big)
          );
        (==) { () }
          (up (pre `h.star` h.mem_invariant ex m0.small)) `star` (
           frame `star` istore_invariant #h (ghost_ctr m0) (lift_inames ex) (core_of m0.big) `star`
           lift h (H2.base_heap.mem_invariant Set.empty m0.big)
          );
        };
        let (| frame', restore |) =
          down_frame
            (pre `h.star` h.mem_invariant ex m0.small)
            (frame `star` 
             istore_invariant #h (ghost_ctr m0) (lift_inames ex) (core_of m0.big) `star`
             lift h (H2.base_heap.mem_invariant Set.empty m0.big))
            m0
        in
        calc (==) {
          (pre `h.star` h.mem_invariant ex m0.small) `h.star` frame';
        (==) { _ by (T.mapply (quote (pqr_prq h))) }
          pre `h.star` frame' `h.star` h.mem_invariant ex m0.small;
        };
        let (x, m1') = action frame' m0.small in
        let m1 = { m0 with small = m1' } in
        calc (==) {
          (post x `h.star` frame' `h.star` h.mem_invariant ex m1');
        (==) { _ by (T.mapply (quote (pqr_prq h))) }
          (post x `h.star` h.mem_invariant ex m1') `h.star` frame';
        };
        let _ = restore (post x `h.star` h.mem_invariant ex m1') m1' in
        assert (
          interpret #(extend h)
            (up (post x `h.star` h.mem_invariant ex m1') `star`
            (frame `star` istore_invariant #h (ghost_ctr m0) (lift_inames ex) (core_of m0.big) `star`
            lift h (H2.base_heap.mem_invariant Set.empty m0.big)))
          m1
        );
        calc (==) {
          (up (post x `h.star` h.mem_invariant ex m1') `star`
            (frame `star` istore_invariant #h (ghost_ctr m0) (lift_inames ex) (core_of m0.big)
             `star`
            lift h (H2.base_heap.mem_invariant Set.empty m0.big)));
        (==) {}
          (up (post x) `star` up (h.mem_invariant ex m1')) `star`
            (frame `star` istore_invariant #h (ghost_ctr m0) (lift_inames ex) (core_of m0.big)
             `star`
            lift h (H2.base_heap.mem_invariant Set.empty m0.big)
            );
        (==) { ac_lemmas_ext h }
          up (post x) `star` frame `star`
            (up (h.mem_invariant ex m1') `star` 
             istore_invariant #h (ghost_ctr m0) (lift_inames ex) (core_of m0.big) `star`
             lift h (H2.base_heap.mem_invariant Set.empty m0.big));
        (==) {}
          up (post x) `star` frame `star`
            (up (h.mem_invariant (down_inames (lift_inames ex)) m1') `star` 
             istore_invariant #h (ghost_ctr m0) (lift_inames ex) (core_of m0.big)  `star`
             lift h (H2.base_heap.mem_invariant Set.empty m0.big));
        (==) { () }
          up (post x) `star` frame `star` (mem_invariant (lift_inames ex) m1);
        };
        down_inames_ok #h ex m1;
        H2.base_heap.is_ghost_action_preorder();
        (x, m1)

#push-options "--ifuel 1"
let frame_inames_ok (#h:heap_sig u#a) (ex:inames (extend h)) (m0 m1:ext_mem h)
: Lemma
(requires inames_ok ex m0 /\ inames_ok (down_inames ex) m1.small  /\ m0.big == m1.big)
(ensures inames_ok ex m1)
= ()
#pop-options

let lift_action_alt
    (#h:heap_sig u#h)
    (#a:Type u#a)
    (#mg:bool)
    (#ex:inames (extend h))
    (#pre:h.slprop)
    (#post:a -> GTot h.slprop)
    (action:_action_except h a mg (down_inames ex) pre post)
: _action_except (extend h)
    a mg ex 
    ((extend h).up pre)
    (fun x -> (extend h).up (post x))
= fun (frame:ext_slprop h) 
      (m0:ext_mem h {
        (extend h).full_mem_pred m0 /\
        inames_ok ex m0 /\
        interpret #(extend h) (up pre `star` frame `star` mem_invariant ex m0) m0
       }) ->
        // down_inames_ok #h ex m0;
        calc (==) {
          up pre `star` frame `star` mem_invariant ex m0;
        (==) {} 
          up pre `star` frame `star` (up (h.mem_invariant (down_inames ex) m0.small) `star`
                                      istore_invariant #h (ghost_ctr m0) ex (core_of m0.big) `star`
                                      lift h (H2.base_heap.mem_invariant Set.empty m0.big));
        (==) { ac_lemmas_ext h } //_ by (T.mapply (quote (pqrs_pr_qs (extend h)))) }
          (up pre `star` up (h.mem_invariant (down_inames ex) m0.small)) `star` (
           frame `star` istore_invariant #h (ghost_ctr m0) (ex) (core_of m0.big) `star`
           lift h (H2.base_heap.mem_invariant Set.empty m0.big)
          );
        (==) { () }
          (up (pre `h.star` h.mem_invariant (down_inames (ex)) m0.small)) `star` (
           frame `star` istore_invariant #h (ghost_ctr m0) (ex) (core_of m0.big) `star`
           lift h (H2.base_heap.mem_invariant Set.empty m0.big)
          );
        (==) { () }
          (up (pre `h.star` h.mem_invariant (down_inames ex) m0.small)) `star` (
           frame `star` istore_invariant #h (ghost_ctr m0) (ex) (core_of m0.big) `star`
           lift h (H2.base_heap.mem_invariant Set.empty m0.big)
          );
        };
        assert (inames_ok (down_inames ex) m0.small);
        let (| frame', restore |) =
          down_frame
            (pre `h.star` h.mem_invariant (down_inames ex) m0.small)
            (frame `star` 
             istore_invariant #h (ghost_ctr m0) (ex) (core_of m0.big) `star`
             lift h (H2.base_heap.mem_invariant Set.empty m0.big))
            m0
        in
        calc (==) {
          (pre `h.star` h.mem_invariant (down_inames ex) m0.small) `h.star` frame';
        (==) { _ by (T.mapply (quote (pqr_prq h))) }
          pre `h.star` frame' `h.star` h.mem_invariant (down_inames ex) m0.small;
        };
        let (x, m1') = action frame' m0.small in
        let m1 = { m0 with small = m1' } in
        calc (==) {
          (post x `h.star` frame' `h.star` h.mem_invariant (down_inames ex) m1');
        (==) { _ by (T.mapply (quote (pqr_prq h))) }
          (post x `h.star` h.mem_invariant (down_inames ex) m1') `h.star` frame';
        };
        let _ = restore (post x `h.star` h.mem_invariant (down_inames ex) m1') m1' in
        assert (
          interpret #(extend h)
            (up (post x `h.star` h.mem_invariant (down_inames ex) m1') `star`
            (frame `star` istore_invariant #h (ghost_ctr m0) (ex) (core_of m0.big) `star`
            lift h (H2.base_heap.mem_invariant Set.empty m0.big)))
          m1
        );
        calc (==) {
          (up (post x `h.star` h.mem_invariant (down_inames ex) m1') `star`
            (frame `star` istore_invariant #h (ghost_ctr m0) (ex) (core_of m0.big)
             `star`
            lift h (H2.base_heap.mem_invariant Set.empty m0.big)));
        (==) {}
          (up (post x) `star` up (h.mem_invariant (down_inames ex) m1')) `star`
            (frame `star` istore_invariant #h (ghost_ctr m0) (ex) (core_of m0.big)
             `star`
            lift h (H2.base_heap.mem_invariant Set.empty m0.big)
            );
        (==) { ac_lemmas_ext h }
          up (post x) `star` frame `star`
            (up (h.mem_invariant (down_inames ex) m1') `star` 
             istore_invariant #h (ghost_ctr m0) (ex) (core_of m0.big) `star`
             lift h (H2.base_heap.mem_invariant Set.empty m0.big));
        (==) {}
          up (post x) `star` frame `star`
            (up (h.mem_invariant (down_inames (ex)) m1') `star` 
             istore_invariant #h (ghost_ctr m0) (ex) (core_of m0.big)  `star`
             lift h (H2.base_heap.mem_invariant Set.empty m0.big));
        (==) { () }
          up (post x) `star` frame `star` (mem_invariant (ex) m1);
        };
        frame_inames_ok #h ex m0 m1;
        // assert (inames_ok (down_inames ex) m1.small);
        // assert (forall x. H2.select_ghost x (core_of m1.big) == H2.select_ghost x (core_of m0.big));
        // assert (inames_ok ex m1);
        // down_inames_ok #h ex m1;
        H2.base_heap.is_ghost_action_preorder ();
        (x, m1)

let dup_inv 
    (#h:heap_sig u#a)
    (ex:inames (extend h))
    (i:(extend h).iref)
    (p:(extend h).slprop)
: ghost_action_except (extend h) unit ex
    ((extend h).inv i p) 
    (fun _ -> (extend h).inv i p `(extend h).star` (extend h).inv i p)
= fun frame
      (m0:ext_mem h { 
        (extend h).full_mem_pred m0 /\
        inames_ok ex m0 /\
        interpret #(extend h) 
          (inv i p `star` frame `star` mem_invariant ex m0) m0
      }) ->
      dup_inv_equiv i p;
      (extend h).is_ghost_action_preorder ();
      (), m0

let new_invariant
    (#h:heap_sig u#a)
    (ex:inames (extend h))
    (p:boxable (extend h))
: ghost_action_except (extend h) 
    (extend h).iref
    ex
    p
    (fun i -> (extend h).inv i p)
= fun frame h0 ->
   assert (interp (p `star` frame `star` mem_invariant ex h0) (core_of h0)); 
  //  let h1' = H2.ghost_extend true 
   admit()

let with_invariant
    (#h:heap_sig u#a)
    (#a:Type u#aa)
    (#fp:ext_slprop h)
    (#fp':(a -> ext_slprop h))
    (#opened_invariants:inames (extend h))
    (#p:ext_slprop h)
    (#maybe_ghost:bool)
    (i:ext_iref h{not (Set.mem (iname_of h i) opened_invariants)})
    (f:_action_except (extend h) a maybe_ghost
      (Set.add (iname_of h i) opened_invariants) 
      (p `star` fp)
      (fun x -> p `star` fp' x))
: _action_except (extend h) a maybe_ghost opened_invariants 
      (inv i p `star` fp)
      (fun x -> inv i p `star` fp' x)
= fun frame m0 -> 
    assert (interpret ((inv i p `star` fp) `star` frame `star` mem_invariant opened_invariants m0) m0);
    calc (==) {
      inv i p `star` fp `star` frame `star` mem_invariant opened_invariants m0;
    (==) { ac_lemmas_ext h }
      (mem_invariant opened_invariants m0 `star` inv i p) `star` (fp `star` frame);
    (==) { mem_invariant_equiv_ext #h opened_invariants m0 i p }
      (mem_invariant (Set.add (iname_of h i) opened_invariants) m0 `star` p `star` inv i p) `star` (fp `star` frame);
    (==) { ac_lemmas_ext h }
      (p `star` fp) `star` (inv i p `star` frame) `star` mem_invariant (Set.add (iname_of h i) opened_invariants) m0;
    };
    iname_ok_ext #h i p m0;
    let (x, m1) = f (inv i p `star` frame) m0 in
    assert (interpret ((p `star` fp' x) `star`
                       (inv i p `star` frame) `star`
                       mem_invariant (Set.add (iname_of h i) opened_invariants) m1) m1);
    calc (==) {
      (p `star` fp' x) `star`
      (inv i p `star` frame) `star`
      mem_invariant (Set.add (iname_of h i) opened_invariants) m1;
    (==) { ac_lemmas_ext h }
      (fp' x) `star`
      frame `star`
      (mem_invariant (Set.add (iname_of h i) opened_invariants) m1 `star` p `star` inv i p);
    (==) { mem_invariant_equiv_ext #h opened_invariants m1 i p }
      (fp' x) `star`
      frame `star`
      (mem_invariant opened_invariants m1 `star` inv i p);
    (==) { ac_lemmas_ext h }
      (inv i p `star` fp' x) `star` frame `star` mem_invariant opened_invariants m1;
    };
    (x, m1)

let pure_ext (h:heap_sig u#a) (p q:prop)
: Lemma ((p <==> q) ==> pure #h p == pure #h q)
= FStar.PropositionalExtensionality.apply p q

let lift_inv (h:heap_sig u#a) (i:h.iref) (p:h.slprop)
: Lemma ((extend h).up (h.inv i p) == (extend h).inv (lift_iref i) ((extend h).up p))
= calc (==) {
    inv (lift_iref i) (up p);
  (==) {}
    up (h.inv i (down (up p))) `star` pure (is_boxable_ext #h (up p));
  (==) { (extend h).up_down p }
    up (h.inv i p) `star` pure (is_boxable_ext #h (up p));
  (==) { (extend h).up_down p; pure_ext h (is_boxable_ext (up p)) True }
    up (h.inv i p) `star` pure True;
  (==) { (extend h).pure_true_emp (); (extend h).emp_unit (up (h.inv i p)) }
    up (h.inv i p);
  }

let mem_invariant_rest (#h:heap_sig u#a) (e:eset (ext_iname h)) (m:ext_mem h)
: ext_slprop h
= up (h.mem_invariant (down_inames e) m.small) `star`
  istore_invariant #h (H2.ghost_ctr m.big) e (core_of m.big)

let heap_cell_evolves (h0 h1:option H.cell)
: prop
= match h0, h1 with
  | None, None -> True
  | None, Some (H.Ref meta _ _ _) -> reveal meta == false
  | Some (H.Ref meta a p v), Some (H.Ref meta' a' p' v') ->
    meta == meta' /\ (reveal meta ==> a==a' /\ p==p' /\ v==v')
  | _, _ -> False

let heaps_preserve_inames (m0 m1:H2.base_heap.mem) =
  H2.ghost_ctr m0 == H2.ghost_ctr m1 /\
  (forall (addr:nat).
    heap_cell_evolves (H2.select_ghost addr (core_of m0)) (H2.select_ghost addr (core_of m1)))

let preserves_inames 
    (#a:Type u#a)
    (#mg:bool)
    (#pre:base_slprop u#h)
    (#post:a -> GTot (base_slprop u#h))
    (action:_action_except H2.base_heap a mg Set.empty pre post)
= forall (m0:full_mem H2.base_heap) frame. 
    interpret (pre `H2.base_heap.star` frame `H2.base_heap.star` H2.base_heap.mem_invariant Set.empty m0) m0
    ==> ( 
    let x, m1 = action frame m0 in
    heaps_preserve_inames m0 m1
    )

#push-options "--ifuel 2 --fuel 1"
let sl_pure_imp_ext_aux
       (#h:heap_sig u#h)
       (p:prop)
       (q0 q1: squash p -> ext_slprop h)
: Lemma 
  (requires (forall (x:squash p). q0 () == q1 ()))
  (ensures forall m. interp (sl_pure_imp p q0) m ==>
                     interp (sl_pure_imp p q1) m)
= ()

let sl_pure_imp_ext
       (#h:heap_sig u#h)
       (p:prop)
       (q0 q1: squash p -> ext_slprop h)
: Lemma 
  (requires (forall (x:squash p). q0 () == q1 ()))
  (ensures sl_pure_imp p q0 == sl_pure_imp p q1)
= sl_pure_imp_ext_aux #h p q0 q1;
  sl_pure_imp_ext_aux #h p q1 q0;
  slprop_extensionality h
    (sl_pure_imp p q0)
    (sl_pure_imp p q1)

let sl_pure_imp_ext_trivial_aux
       (#h:heap_sig u#h)
       (p:prop)
       (q: squash p -> ext_slprop h)
: Lemma 
  (requires ~p)
  (ensures forall m. interp (sl_pure_imp p q) m)
= ()

let sl_pure_imp_ext_trivial
       (#h:heap_sig u#h)
       (p:prop)
       (q: squash p -> ext_slprop h)
: Lemma 
  (requires ~p)
  (ensures sl_pure_imp p q == emp)
= sl_pure_imp_ext_trivial_aux #h p q;
  FStar.Classical.forall_intro (pure_interp #h True); 
  slprop_extensionality h
    (sl_pure_imp p q)
    (pure True);
  (extend h).pure_true_emp ()
  
let istore_invariant_eq_frame
    (#h:heap_sig u#h)
    (ex:inames (extend h))
    (m0 m1:ext_mem h)
: Lemma 
  (requires
    heaps_preserve_inames m0.big m1.big /\
    m0.small == m1.small /\
    inames_ok ex m0)
  (ensures 
    (istore_invariant #h (H2.ghost_ctr m0.big) ex (core_of m0.big) ==
     istore_invariant #h (H2.ghost_ctr m1.big) ex (core_of m1.big)) /\
    inames_ok ex m1)
= assert (inames_ok ex m1);
  let aux0 (c:nat)
    : Lemma (invariant_of_one_cell #h c ex (core_of m0.big)
              == invariant_of_one_cell #h c ex (core_of m1.big))
    = let m0 = core_of m0.big in
      let m1 = core_of m1.big in
      if Inr c `Set.mem` ex then ()
      else (
        match H2.select_ghost c m0, H2.select_ghost c m1 with
        | Some cell0, Some cell1 -> 
          assert (cell_pred_pre h cell0 <==> cell_pred_pre h cell1);
          FStar.PropositionalExtensionality.apply
            (cell_pred_pre h cell0)
            (cell_pred_pre h cell1);
          sl_pure_imp_ext 
            #h 
            (cell_pred_pre h cell0) 
            (cell_pred_post h cell0)
            (cell_pred_post h cell1)
        | None, Some cell1 ->
          sl_pure_imp_ext_trivial #h (cell_pred_pre h cell1) (cell_pred_post h cell1)
        | _ -> ()
      )
  in
  let rec aux (c:nat)
    : Lemma (istore_invariant #h c ex (core_of m0.big)
             == istore_invariant #h c ex (core_of m1.big))
    = aux0 c;
      if c = 0 then () else aux (c - 1)
  in
  aux (H2.ghost_ctr m0.big)
#pop-options

#push-options "--fuel 0 --ifuel 0"
let lower_frame_core
      (#h:heap_sig u#a)
      (p:base_slprop)
      (frame:ext_slprop h)
      (m:ext_mem h { interpret #(extend h) (lift h p `star` frame) m })
: frame':base_slprop { 
  interpret (p `H2.base_heap.star` frame') m.big /\
  (forall (q:base_slprop) (m':base_heap_mem).
    interpret (q `H2.base_heap.star` frame') m' ==>
    interpret #(extend h) (lift h q `star` frame) ({m with big = m'}))
}
= eliminate exists (m0:core h)  (m1: core h).
    disjoint m0 m1 /\
    core_of #(extend h) m == join #h m0 m1 /\
    lift h p m0 /\
    frame m1
  returns exists frame'. 
    interpret (p `H2.base_heap.star` frame') m.big /\
    (forall (q:base_slprop) (m':base_heap_mem).
      interpret (q `H2.base_heap.star` frame') m' ==>
      interpret #(extend h) (lift h q `star` frame) ({m with big = m'}))
  with _ . ( 
    let fr (ms:base_heap_core)
      : prop 
      = interp frame { small_core = m1.small_core; big_core = ms }
    in
    let fr_affine ()
    : Lemma (is_affine_mem_prop H2.base_heap.sep fr)
    = introduce forall s0 s1.
        fr s0 /\ H2.base_heap.sep.disjoint s0 s1 ==> fr (H2.base_heap.sep.join s0 s1)
      with introduce _ ==> _
      with _. ( 
        let left = { small_core = m1.small_core; big_core = s0 } in
        let right = { small_core = h.sep.empty; big_core=s1 } in
        h.sep.join_empty m1.small_core;
        assert (disjoint left right)
      )
    in
    fr_affine();
    let frame' = H2.base_heap.as_slprop fr in
  //   up_down p;
    assert (H2.base_heap.interp p m0.big_core);
    assert (fr m1.big_core);
    H2.base_heap.interp_as fr;
    assert (H2.base_heap.interp frame' m1.big_core);
    assert (H2.base_heap.sep.disjoint m0.big_core m1.big_core);
    H2.base_heap.star_equiv p frame' (core_of m.big);
    assert (H2.base_heap.interp (p `H2.base_heap.star` frame') (core_of m.big));
    introduce forall (q:base_slprop) (m':base_heap_mem).
        interpret (q `H2.base_heap.star` frame') m' ==>
        interpret #(extend h) (lift h q `star` frame) ({m with big = m'})
    with introduce _ ==> _
    with _ . (
        H2.base_heap.star_equiv q frame' (core_of m');
        eliminate exists m0' m1'.
          H2.base_heap.sep.disjoint m0' m1' /\
          core_of m' == H2.base_heap.sep.join m0' m1' /\
          H2.base_heap.interp q m0' /\
          fr m1'
        returns _
        with _ . (
          let mres = core_of #(extend h) { m with big = m'} in
          introduce exists ml mr.
            disjoint ml mr /\
            mres == join ml mr /\
            lift h q ml /\
            frame mr
          with ({ small_core=m0.small_core; big_core=m0'}) ({ small_core = m1.small_core; big_core=m1'})
          and  (
            ()
          );
          assert (interpret #(extend h) (lift h q `star` frame) ({m with big = m'}))
        )
    )
  );
  let frame' =
    FStar.IndefiniteDescription.indefinite_description_tot 
      base_slprop
      (fun frame' ->
        interpret (p `H2.base_heap.star` frame') m.big /\
         (forall (q:base_slprop) (m':base_heap_mem).
            interpret (q `H2.base_heap.star` frame') m' ==>
            interpret #(extend h) (lift h q `star` frame) ({m with big = m'})))
  in
  H2.base_heap.non_info_slprop frame'

let lower_frame
      (#h:heap_sig u#a)
      (p:base_slprop)
      (frame:ext_slprop h)
      (m:ext_mem h { interpret #(extend h) (lift h p `star` frame) m })
: frame':base_slprop { interpret (p `H2.base_heap.star` frame') m.big } &
  (q:base_slprop -> m':base_heap_mem -> 
    Lemma (requires interpret  (q `H2.base_heap.star` frame') m')
          (ensures interpret #(extend h) (lift h q `star` frame) ({m with big = m'})))
= let frame' = lower_frame_core p frame m in
  (| frame', (fun q m' -> ()) |)

let lift_base_heap_action
    (#h:heap_sig u#h)
    (#a:Type u#a)
    (#mg:bool)
    (#ex:inames (extend h))
    (#pre:erased base_slprop)
    (#post:a -> GTot base_slprop)
    (action:_action_except H2.base_heap a mg Set.empty pre post {
      preserves_inames action
    })
: _action_except (extend h)
    a mg ex
    (lift h pre)
    (fun x -> lift h (post x))
= fun (frame:ext_slprop h) 
      (m0:ext_mem h {
        (extend h).full_mem_pred m0 /\
        inames_ok ex m0 /\
        interpret #(extend h) (lift h pre `star` frame `star` mem_invariant ex m0) m0
       }) ->
        let pre = H2.base_heap.non_info_slprop pre in
        calc (==) {
          lift h pre `star` frame `star` mem_invariant ex m0;
        (==) { ac_lemmas_ext h }
          lift h pre `star`
          lift h (H2.base_heap.mem_invariant Set.empty m0.big) `star`
          (frame `star` mem_invariant_rest ex m0);
        (==) { lift_star #h pre (H2.base_heap.mem_invariant Set.empty m0.big) }
          lift h (pre `H2.base_heap.star` H2.base_heap.mem_invariant Set.empty m0.big) `star`
          (frame `star` mem_invariant_rest ex m0);
        };
        let (| frame', restore |) =
          lower_frame
            (pre `H2.base_heap.star` H2.base_heap.mem_invariant Set.empty m0.big)
            (frame `star` mem_invariant_rest ex m0)
            m0
        in
        calc (==) {
          (pre `H2.base_heap.star` H2.base_heap.mem_invariant Set.empty m0.big) `H2.base_heap.star`
          frame';
        (==) { ac_lemmas H2.base_heap }
          pre `H2.base_heap.star`
          frame' `H2.base_heap.star`
          H2.base_heap.mem_invariant Set.empty m0.big;
        };
        let (x, m1') = action frame' m0.big in
        calc (==) {
          post x `H2.base_heap.star`
          frame' `H2.base_heap.star`
          H2.base_heap.mem_invariant Set.empty m1';
        (==) { ac_lemmas H2.base_heap }
          (post x `H2.base_heap.star` H2.base_heap.mem_invariant Set.empty m1') `H2.base_heap.star`
          frame';
        };
        restore (post x `H2.base_heap.star` H2.base_heap.mem_invariant Set.empty m1') m1';
        let m1 = { m0 with big=m1'} in
        calc (==) {
          lift h (post x `H2.base_heap.star` H2.base_heap.mem_invariant Set.empty m1') `star`
          (frame `star` mem_invariant_rest ex m0);
        (==) { lift_star #h (post x) (H2.base_heap.mem_invariant Set.empty m1') }
          (lift h (post x) `star`
           lift h (H2.base_heap.mem_invariant Set.empty m1')) `star`
          (frame  `star` mem_invariant_rest ex m0);
        (==) { istore_invariant_eq_frame #h ex m0 m1 }
          (lift h (post x) `star`
           lift h (H2.base_heap.mem_invariant Set.empty m1')) `star`
          (frame  `star` mem_invariant_rest ex m1);
        (==) { ac_lemmas_ext h }
          lift h (post x) `star`
          frame `star`
          mem_invariant ex m1;
        };
        h.is_ghost_action_preorder ();
        istore_invariant_eq_frame ex m0 m1;
        assert (inames_ok ex m1);
        x, m1

let select_refine
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#p:pcm a)
    (e:inames _)
    (r:ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: action_except
    (extend h)
    (v:a{compatible p x v /\ p.refine v}) e
    ((extend h).pts_to r x)
    (fun v -> (extend h).pts_to r (f v))
= assume (preserves_inames (H2.read #Set.empty r x f));
  lift_base_heap_action (H2.read r x f)


let upd_gen
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#p:pcm a)
    (e:inames _) 
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: action_except
    (extend h)
    unit e
    ((extend h).pts_to r x)
    (fun _ -> (extend h).pts_to r y)
= assume (preserves_inames (H2.write #Set.empty r x y f));
  lift_base_heap_action (H2.write r x y f)


let coerce_action (#h:heap_sig) #a #mg #e #pre (#post0:a -> GTot h.slprop)
      (f:_action_except h a mg e pre post0)
      (pre1:h.slprop)
      (post1:a -> GTot h.slprop)
      (_: squash (pre == pre1 /\ (forall x. post0 x == post1 x)))
: _action_except h a mg e pre1 post1
= f

let split_action
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#pcm:pcm a)
    (e:inames _)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: ghost_action_except
    (extend h)
    unit e
    ((extend h).pts_to r (v0 `op pcm` v1))
    (fun _ -> (extend h).pts_to r v0 `(extend h).star` (extend h).pts_to r v1)
= assume (preserves_inames (H2.share #Set.empty r v0 v1));
  let res
    : ghost_action_except
        (extend h)
        unit e
        ((extend h).pts_to r (v0 `op pcm` v1))
        (fun _ -> lift h (H2.base_heap.pts_to r v0 `H2.base_heap.star`
                          H2.base_heap.pts_to r v1))
    = lift_base_heap_action #h #unit #true #e (H2.share #Set.empty r v0 v1) in
  lift_star #h (H2.base_heap.pts_to r v0) (H2.base_heap.pts_to r v1);
  coerce_action res _ _ ()

(** Combining separate permissions into a single composite permission *)
let gather_action
  (#h:heap_sig u#h)
  (#a:Type u#(h + 1))
  (#pcm:pcm a)
  (e:inames _)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a)
: ghost_action_except
    (extend h)
    (squash (composable pcm v0 v1)) e
    ((extend h).pts_to r v0 `(extend h).star` (extend h).pts_to r v1)
    (fun _ -> (extend h).pts_to r (op pcm v0 v1))
= assume (preserves_inames (H2.gather #Set.empty r v0 v1));
  let res = lift_base_heap_action #h #_ #true #e (H2.gather #Set.empty r v0 v1) in
  lift_star #h (H2.base_heap.pts_to r v0) (H2.base_heap.pts_to r v1);
  coerce_action res _ _ ()

let alloc_action
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#pcm:pcm a)
    (e:inames _)
    (x:a{pcm.refine x})
: action_except
    (extend h)
    (ref a pcm) e
    (extend h).emp
    (fun r -> (extend h).pts_to r x)
= assume (preserves_inames (H2.extend #Set.empty #a #pcm x));
  let res = lift_base_heap_action #h #(ref a pcm) #false #e (H2.extend #Set.empty #a #pcm x) in
  assume ((extend h).emp == lift h H2.base_heap.emp);
  coerce_action res _ _ ()

let pts_to_not_null_action 
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#pcm:pcm a)
    (e:inames _)
    (r:erased (ref a pcm))
    (v:Ghost.erased a)
: ghost_action_except
    (extend h)
    (squash (not (is_null r))) e
    ((extend h).pts_to r v)
    (fun _ -> (extend h).pts_to r v)
= admit()
//  assume (preserves_inames (H2.pts_to_not_null #Set.empty r v));
//   let res = lift_base_heap_action  (H2.pts_to_not_null r v) in
//   coerce_action res _ _ ()

// Ghost actions

// Ghost operations
let ghost_alloc
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#pcm:pcm a)
    (e:inames _)
    (x:erased a{pcm.refine x})
: ghost_action_except
    (extend h)
    (ghost_ref a pcm)
    e
    (extend h).emp 
    (fun r -> (extend h).ghost_pts_to false r x)
= assume (preserves_inames (H2.ghost_extend false #Set.empty #a #pcm x));
  let res = lift_base_heap_action #h #(ghost_ref a pcm) #true #e (H2.ghost_extend false #Set.empty #a #pcm x) in
  assume ((extend h).emp == lift h H2.base_heap.emp);
  coerce_action res _ _ ()

let ghost_read
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#p:pcm a)
    o
    (r:ghost_ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: ghost_action_except
    (extend h)
    (erased (v:a{compatible p x v /\ p.refine v}))
    o
    ((extend h).ghost_pts_to false r x)
    (fun v -> (extend h).ghost_pts_to false r (f v))
= assume (preserves_inames (H2.ghost_read #Set.empty #false r x f));
  let res = lift_base_heap_action 
              #h #(erased (v:a{compatible p x v /\ p.refine v})) 
              #true #o (H2.ghost_read #Set.empty #false r x f) in
  coerce_action res _ _ ()

let ghost_write
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#p:pcm a)
    o
    (r:ghost_ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: ghost_action_except
    (extend h)
    unit o 
    ((extend h).ghost_pts_to false r x)
    (fun _ -> (extend h).ghost_pts_to false r y)
= assume (preserves_inames (H2.ghost_write #Set.empty #false r x y f));
  let res = lift_base_heap_action #h #unit #true #o (H2.ghost_write #Set.empty #false r x y f) in
  coerce_action res _ _ ()

let ghost_share
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#pcm:pcm a)
    o
    (r:ghost_ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: ghost_action_except
    (extend h)
    unit o
    ((extend h).ghost_pts_to false r (v0 `op pcm` v1))
    (fun _ -> (extend h).ghost_pts_to false r v0 `(extend h).star` 
              (extend h).ghost_pts_to false r v1)
= assume (preserves_inames (H2.ghost_share #Set.empty #false r v0 v1));
  let res = lift_base_heap_action #h #unit #true #o (H2.ghost_share #Set.empty #false r v0 v1) in
  lift_star #h (H2.base_heap.ghost_pts_to false r v0) (H2.base_heap.ghost_pts_to false r v1);
  coerce_action res _ _ ()

let ghost_gather
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#pcm:pcm a)
    o
    (r:ghost_ref a pcm)
    (v0 v1:FStar.Ghost.erased a)
: ghost_action_except
    (extend h)
    (squash (composable pcm v0 v1)) o
    ((extend h).ghost_pts_to false r v0 `(extend h).star`
     (extend h).ghost_pts_to false r v1)
    (fun _ -> (extend h).ghost_pts_to false r (op pcm v0 v1))
= assume (preserves_inames (H2.ghost_gather #Set.empty #false r v0 v1));
  let res = lift_base_heap_action #h #_ #true #o (H2.ghost_gather #Set.empty #false r v0 v1) in
  lift_star #h (H2.base_heap.ghost_pts_to false r v0) (H2.base_heap.ghost_pts_to false r v1);
  coerce_action res _ _ ()

// let interp_exists (#h:heap_sig u#h) (#a:Type u#a) (p: a -> h.slprop)
// : Lemma (forall m. h.interp (exists_ p) m <==> (exists x. h.interp (p x) m))
// = admit() // h.interp_as (fun m -> exists (x:a). h.interp (p x) m)

let interp_up_down (#h:heap_sig u#h) (p:ext_slprop h)
: Lemma (forall m. interp (up (down p)) m <==> interp p { m with big_core=H2.base_heap.sep.empty})
= introduce forall m.
      interp (up (down p)) m <==> interp p { m with big_core=H2.base_heap.sep.empty}
  with (
    calc (<==>) {
      (up (down p)) m;
        (<==>) {}
      up_p (down p) m;
        (<==>) {}
      h.interp (down p) m.small_core;
        (<==>) {  }
      (down_p_affine p;
       h.interp (h.as_slprop (down_p p)) m.small_core);
        (<==>) { h.interp_as (down_p p) }
      down_p p m.small_core;
        (<==>) {}
      p { m with big_core=H2.base_heap.sep.empty};
    }
  )

let exists_congruence
         (#h:heap_sig u#h)
         (#a:Type u#a)
         (p:a -> (extend h).slprop)
: Lemma
  (requires forall x. is_boxable (p x))
  (ensures is_boxable (exists_ p))
= assert (forall p m. {:pattern (interp p m)} interp p m == (extend h).interp p m);
  interp_exists p;
  interp_up_down (exists_ p);
  slprop_extensionality h (exists_ p) (up (down (exists_ p)))

let down_star
    (#h:heap_sig u#h)
    (p q:(extend h).slprop)
: Lemma ((extend h).down (p `(extend h).star` q) ==
         (extend h).down p `h.star` (extend h).down q)
= introduce
    forall m. h.interp (down (p `star` q)) m <==>
              h.interp (down p `h.star` down q) m
  with ( 
    introduce 
       h.interp (down (p `star` q)) m ==> 
       h.interp (down p `h.star` down q) m
    with _ . (
      assert (h.interp (down (p `star` q)) m);
      down_p_affine (p `star` q);
      h.interp_as (down_p (p `star` q));
      let mm = { small_core=m; big_core = H2.base_heap.sep.empty } in
      assert (down_p (p `star` q) m);
      assert (interp (p `star` q) mm);
      eliminate exists m0 m1.
        disjoint m0 m1 /\
        mm == join m0 m1 /\
        interp p m0 /\
        interp q m1
      returns _
      with _ . (
        h.star_equiv (down p) (down q) m;
        assert (H2.base_heap.sep.join m0.big_core m1.big_core == mm.big_core);
        H2.base_heap.sep.join_empty_inverse m0.big_core m1.big_core;
        assert (m0.big_core == mm.big_core);
        assert (m1.big_core == mm.big_core);
        assert (h.sep.disjoint m0.small_core m1.small_core);
        down_p_affine p;
        down_p_affine q;
        h.interp_as (down_p p);
        h.interp_as (down_p q)
      )
    );
    introduce 
       h.interp (down p `h.star` down q) m ==>
       h.interp (down (p `star` q)) m
    with _ . (
      h.star_equiv (down p) (down q) m;
      assert (h.interp (down p `h.star` down q) m);
      // admit();
      eliminate exists m0 m1.
        h.sep.disjoint m0 m1 /\
        m == h.sep.join m0 m1 /\
        h.interp (down p) m0 /\
        h.interp (down q) m1
      returns _
      with _ . (
        down_p_affine (p `star` q);
        h.interp_as (down_p (p `star` q));
        let mm = { small_core = m; big_core = H2.base_heap.sep.empty } in
        down_p_affine p;
        down_p_affine q;
        h.interp_as (down_p p);
        h.interp_as (down_p q);
        assert (down_p p m0);
        assert (down_p q m1);
        let mm0 = { small_core = m0; big_core = H2.base_heap.sep.empty } in
        let mm1 = { small_core = m1; big_core = H2.base_heap.sep.empty } in
        H2.base_heap.sep.join_empty H2.base_heap.sep.empty;
        assert ((ext_sep h).disjoint mm0 mm1);
        assert ((p `star` q) mm);
        assert (down_p (p `star` q) m)
      )
    )
  );
  h.slprop_extensionality (down (p `star` q)) (down p `h.star` down q)

let up_star (#h:heap_sig u#a) (p q:h.slprop)
: Lemma (up (p `h.star` q) == (up p `star` up q))
= ()

let intro_exists (#h:heap_sig u#h) (#a:Type u#a) (p: a -> GTot h.slprop) (m:_)
: Lemma 
  (requires (exists x. h.interp (p x) m))
  (ensures h.interp (exists_ p) m)
= HeapSig.interp_exists #h #a p


let down_exists (#h:heap_sig) #a (p: a -> GTot (extend h).slprop)
: Lemma 
  (ensures (extend h).down (exists_ p) ==
            exists_ #h (fun x -> (extend h).down (p x)))
= introduce forall m. 
    h.interp ((extend h).down (exists_ p)) m ==>
    h.interp (exists_ #h (fun x -> (extend h).down (p x))) m
  with introduce _ ==> _
  with _ . (
    down_p_affine (exists_ p);
    h.interp_as (down_p (exists_ p));
    assert (down_p (exists_ p) m);
    let mm = { small_core=m; big_core=H2.base_heap.sep.empty } in
    assert (interp (exists_ p) mm);
    HeapSig.interp_exists #(extend h) p;
    assert ((extend h).interp (exists_ p) mm);
    eliminate exists x.
      (extend h).interp (p x) mm
    returns _
    with _ . ( 
      HeapSig.interp_exists #h (fun x -> (extend h).down (p x));
      down_p_affine (p x);
      h.interp_as (down_p (p x));
      assert (h.interp (down (p x)) m);
      assert (h.interp (exists_ #h (fun x -> (extend h).down (p x))) m)
    )
  );
  introduce forall m. 
    h.interp (exists_ #h (fun x -> (extend h).down (p x))) m ==>
    h.interp ((extend h).down (exists_ p)) m
  with introduce _ ==> _
  with _ . ( 
    HeapSig.interp_exists #h (fun x -> (extend h).down (p x));
    eliminate exists x.
      h.interp (down (p x)) m
    returns _
    with _ . (
      down_p_affine (p x);
      h.interp_as (down_p (p x));
      let mm = { small_core=m; big_core=H2.base_heap.sep.empty } in
      assert (interp (p x) mm);
      HeapSig.interp_exists #(extend h) p;
      calc (<==>) {
        h.interp (down (exists_ p)) m;
      (<==>) { down_p_affine (exists_ p);
               h.interp_as (down_p (exists_ p)) }
        interp (exists_ p) mm;
      (<==>) {}
        (extend h).interp (exists_ p) mm;
      (<==>) { HeapSig.interp_exists #(extend h) p }
        (exists x. interp (p x) mm);
      }
    )
  );
  h.slprop_extensionality
      ((extend h).down (exists_ p))
      (exists_ #h (fun x -> (extend h).down (p x)))

let emp_trivial (h:heap_sig u#a)
: Lemma (forall m. h.interp h.emp m)
= h.pure_true_emp ();
  FStar.Classical.forall_intro (h.pure_interp True)

let down_emp
    (h:heap_sig u#h)
: Lemma ((extend h).down (extend h).emp == h.emp)
= emp_trivial (extend h);
  emp_trivial h;
  down_p_affine (extend h).emp;
  h.interp_as (down_p (extend h).emp);
  h.slprop_extensionality ((extend h).down (extend h).emp) h.emp

let up_emp (h:heap_sig u#a)
: Lemma ((extend h).up h.emp == (extend h).emp)
= emp_trivial (extend h);
  emp_trivial h;
  (extend h).slprop_extensionality ((extend h).up h.emp) (extend h).emp

let up_pure
        (h:heap_sig u#a)
        (p:prop)
: Lemma ((extend h).pure p == (extend h).up (h.pure p))
= FStar.Classical.forall_intro (h.pure_interp p);
  FStar.Classical.forall_intro ((extend h).pure_interp p);
  (extend h).slprop_extensionality ((extend h).pure p) ((extend h).up (h.pure p))
