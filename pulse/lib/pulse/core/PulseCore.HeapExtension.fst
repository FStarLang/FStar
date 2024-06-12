module PulseCore.HeapExtension
open PulseCore.HeapSig
open FStar.Ghost
open FStar.PCM
open FStar.FunctionalExtensionality
module H = PulseCore.Heap
module H2 = PulseCore.Heap2
module F = FStar.FunctionalExtensionality
module PA = PulseCore.PCM.Agreement

assume
val core_ghost_ref_as_addr (_:core_ghost_ref) : GTot nat

assume
val select (i:nat) (m:H2.heap u#a) : GTot (option (H.cell u#a))

assume
val select_ghost (i:nat) (m:H2.heap u#a) : GTot (option (H.cell u#a))

noeq
type core (h:heap_sig u#a) : Type u#(a + 2) = {
    small_core : h.sep.core;
    big_core : H2.heap u#(a + 1);
}

noeq
type ext_mem (h:heap_sig u#a) : Type u#(a + 2) = {
    small : h.mem;
    big : H2.heap u#(a + 1);
    ctr : nat;
    ghost_ctr: erased nat;
}

(* A lens between mem and core *)
let get_core (#h:heap_sig u#h) (m:ext_mem h) : core h = {
    small_core = h.sep.lens_core.get m.small;
    big_core = m.big;
}

let put_core (#h:heap_sig u#h) (c:core h) (m:ext_mem h) : ext_mem h = {
    small = h.sep.lens_core.put c.small_core m.small;
    big = c.big_core;
    ctr = m.ctr;
    ghost_ctr = m.ghost_ctr;
}

let get_put (#h:heap_sig u#h) (m:ext_mem h)
: Lemma (put_core (get_core m) m == m)
= h.sep.lens_core.get_put m.small

let put_get (#h:heap_sig u#h) (c:core h) (m:ext_mem h)
: Lemma (get_core (put_core c m) == c)
= h.sep.lens_core.put_get c.small_core m.small

let put_put (#h:heap_sig u#h) (c1 c2:core h) (m:ext_mem h)
: Lemma (put_core c2 (put_core c1 m) == put_core c2 m)
= h.sep.lens_core.put_put c1.small_core c2.small_core m.small

let lens_core (h:heap_sig u#a) : lens (ext_mem h) (core h) = {
    get = get_core #h;
    put = put_core #h;
    get_put = get_put #h;
    put_get = put_get #h;
    put_put = put_put #h;
}

let empty (#h:heap_sig u#a) : core h = {
    small_core = h.sep.empty;
    big_core = H2.empty_heap;
}

let disjoint (#h:heap_sig u#a) (m1 m2:core h)
: prop
= h.sep.disjoint m1.small_core m2.small_core /\
  H2.disjoint m1.big_core m2.big_core

let join (#h:heap_sig u#a) (m1:core h) (m2:core h { disjoint m1 m2 })
: core h
= {
    small_core = h.sep.join m1.small_core m2.small_core;
    big_core = H2.join m1.big_core m2.big_core;
  }

let disjoint_sym (#h:heap_sig u#a) (m1 m2:core h)
: Lemma (disjoint m1 m2 <==> disjoint m2 m1)
        [SMTPat (disjoint m1 m2)]
= h.sep.disjoint_sym m1.small_core m2.small_core

let join_commutative (#h:heap_sig u#a) (m1:core h) (m2:core h { disjoint m1 m2 })
: Lemma (join m1 m2 == join m2 m1)
        [SMTPat (join m1 m2)]
= h.sep.join_commutative m1.small_core m2.small_core;
  H2.join_commutative m1.big_core m2.big_core

let disjoint_join (#h:heap_sig u#a) (m0 m1 m2:core h)
: Lemma (
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2) ==>
        disjoint m0 m1 /\
        disjoint m0 m2 /\
        disjoint (join m0 m1) m2 /\
        disjoint (join m0 m2) m1)
= h.sep.disjoint_join m0.small_core m1.small_core m2.small_core;
  H2.disjoint_join m0.big_core m1.big_core m2.big_core

let join_associative (#h:heap_sig u#a) 
        (m0:core h)
        (m1:core h)
        (m2:core h { disjoint m1 m2 /\ disjoint m0 (join m1 m2) })
: Lemma (disjoint m0 m1 /\
         disjoint (join m0 m1) m2 /\
         join m0 (join m1 m2) == join (join m0 m1) m2)
= h.sep.join_associative m0.small_core m1.small_core m2.small_core;
  H2.join_associative m0.big_core m1.big_core m2.big_core

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
  H2.join_empty m.big_core

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
  }

let full_mem_pred (h:heap_sig u#a) (m:ext_mem h) : prop =
    h.full_mem_pred m.small /\
    H2.full_heap_pred m.big

let is_ghost_action (h:heap_sig u#a) (m0 m1:ext_mem h) : prop =
    h.is_ghost_action m0.small m1.small /\
    H2.concrete m0.big == H2.concrete m1.big /\
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
= fun h -> p { small_core = h; big_core = H2.empty_heap }

let down_p_affine (#h:heap_sig u#a) (p:ext_slprop h)
: Lemma (is_affine_mem_prop h.sep (down_p #h p))
= introduce 
    forall (h1 h2:h.sep.core).
      down_p p h1 /\ h.sep.disjoint h1 h2 ==> down_p p (h.sep.join h1 h2)
  with introduce _ ==> _
  with _ . (
    assert (down_p p h1);
    let h1_ = { small_core = h1; big_core = H2.empty_heap } in
    assert (p h1_);
    let h2_ = { small_core = h2; big_core = H2.empty_heap } in
    H2.join_empty H2.empty_heap;
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

let h2_of_slprop (p:H2.slprop u#a) : H2.a_heap_prop u#a =
  H2.interp_depends_only_on p;
  fun h -> H2.interp p h

let lift (h:heap_sig u#a) (p:H2.slprop u#(a + 1))
: ext_slprop h
= as_slprop (fun c -> h2_of_slprop p c.big_core)

let pts_to (h:heap_sig u#a) (#a:Type u#(a + 1)) (#p:pcm a) (r:ref a p) (x:a)
: ext_slprop h
= lift h (H2.pts_to #a #p r x)

let ghost_pts_to (h:heap_sig u#a) (#a:Type u#(a + 1)) (#p:pcm a) (r:ghost_ref a p) (x:a)
: ext_slprop h
= lift h (H2.ghost_pts_to #a #p r x)

let ext_iname (h:heap_sig u#a) : eqtype = either h.iname nat
let ext_iref (h:heap_sig u#a) : Type0 = erased (either h.iref (ghost_ref _ (PA.pcm_agreement #h.slprop)))
let iref_erasable (h:heap_sig u#a) : non_info (ext_iref h) = fun x -> reveal x
let iname_of (h:heap_sig u#a) (r:ext_iref h) : GTot (ext_iname h) =
  match r with
  | Inl i -> Inl (h.iname_of i)
  | Inr r -> Inr (core_ghost_ref_as_addr r)
let is_boxable (#h:heap_sig u#a) (p:ext_slprop h) = up (down p) == p
let inv (#h:heap_sig u#a) (i:ext_iref h) (p:ext_slprop h)
: ext_slprop h
= match i with
  | Inl i -> up (h.inv i (down p))
  | Inr r -> ghost_pts_to h r (Some (down p)) `star` pure (is_boxable p)

let iname_ok (h:heap_sig u#a) (i:ext_iname h) (m:ext_mem h) : prop =
  match i with
  | Inl i -> h.iname_ok i m.small
  | Inr i -> Some? (select_ghost i m.big)

let down_inames (#h:heap_sig u#h) (e:eset (ext_iname h))
: inames h
= let e = Ghost.reveal e in
  FStar.Set.intension (fun i -> Set.mem (Inl i) e)

let sl_pure_imp (#h:heap_sig u#h) (p:prop) (q: squash p -> ext_slprop h) : ext_slprop h =
  as_slprop (fun m -> p ==> interp (q ()) m)

let cell_pred_pre (h:heap_sig u#h) (c:H.cell) =
  let H.Ref a pcm _ = c in
  a == PA.agreement h.slprop /\
  pcm == PA.pcm_agreement #h.slprop

let cell_pred_post (h:heap_sig u#h) (c:H.cell) (_:squash (cell_pred_pre h c)) =
  let H.Ref _ _ v = c in
  let v : PA.agreement h.slprop = v in
  match v with
  | None -> emp
  | Some p -> up p

let invariant_of_one_cell
      (#h:heap_sig u#a)
      (addr:nat)
      (e:eset (ext_iname h))
      (m:H2.heap u#(a + 1))
: ext_slprop h
= if Inr addr `Set.mem` e then emp
  else match select_ghost addr m with
       | Some c -> 
         sl_pure_imp
          (cell_pred_pre h c)
          (cell_pred_post h c)
       | _ -> emp

let rec istore_invariant
         (#h:heap_sig u#a)
         (from:nat)
         (e:eset (ext_iname h))
         (l:H2.heap u#(a + 1))
: ext_slprop h
= invariant_of_one_cell from e l `star` 
  (if from = 0 then emp else istore_invariant (from - 1) e l)

let mem_invariant (#h:heap_sig u#a) (e:eset (ext_iname h)) (m:ext_mem h)
: ext_slprop h
= up (h.mem_invariant (down_inames e) m.small) `star`
  istore_invariant #h m.ctr e m.big

let share_gather_equiv (#a:_) (#p:pcm a) (r:H2.ghost_ref p) (v0:a) (v1:a{composable p v0 v1})
: Lemma (H2.ghost_pts_to r (v0 `op p` v1) == 
         H2.ghost_pts_to r v0 `H2.star` H2.ghost_pts_to r v1)
= H2.ghost_pts_to_compatible_equiv r v0 v1;
  H2.slprop_extensionality (H2.ghost_pts_to r (v0 `op p` v1)) (H2.ghost_pts_to r v0 `H2.star` H2.ghost_pts_to r v1)

let up_star (#h:heap_sig u#a) (p q:h.slprop)
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
      let mr = { m with small_core = m2; big_core = H2.empty_heap } in
      H2.join_empty m.big_core;
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

let h2_star_equiv (p q:H2.slprop) (m:H2.heap)
: Lemma (
    H2.interp (p `H2.star` q) m <==> 
        (exists m0 m1. 
          H2.disjoint m0 m1 /\
          m == H2.join m0 m1 /\
          H2.interp p m0 /\
          H2.interp q m1)
  )
= introduce  
    H2.interp (p `H2.star` q) m ==> 
        (exists m0 m1. 
          H2.disjoint m0 m1 /\
          m == H2.join m0 m1 /\
          H2.interp p m0 /\
          H2.interp q m1)
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


let core_of (#h:heap_sig) (m:h.mem)
: h.sep.core
= h.sep.lens_core.get m


let lift_star (#h:heap_sig u#a) (p q:H2.slprop u#(a + 1))
: Lemma (lift h (p `H2.star` q) == lift h p `star` lift h q)
= introduce forall (m:core h). 
    (lift h (p `H2.star` q)) m ==>
    (lift h p `star` lift h q) m
  with introduce _ ==> _
  with _ . ( 
    h2_star_equiv p q m.big_core;
    eliminate exists (m0 m1:H2.heap).
      H2.disjoint m0 m1 /\
      m.big_core == H2.join m0 m1 /\
      H2.interp p m0 /\
      H2.interp q m1
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
    (lift h (p `H2.star` q)) m
  with (
    h2_star_equiv p q m.big_core
  );
  slprop_extensionality _ (lift h (p `H2.star` q)) (lift h p `star` lift h q)

let dup_pure (#h:heap_sig u#a) (p:prop) : Lemma (pure #h p == pure #h p `star` pure #h p) = admit()

let ac_lemmas_ext (h:heap_sig u#a)
: Lemma (
    (forall (p q r:ext_slprop h). (p `star` q) `star` r == p `star` (q `star` r)) /\
    (forall (p q:ext_slprop h). p `star` q == q `star` p) /\
    (forall (p:ext_slprop h). p `star` emp == p)
) = admit()

let dup_inv_equiv (#h:heap_sig u#a) (i:ext_iref h) (p:ext_slprop h)
: Lemma (inv i p == inv i p `star` inv i p)
= match i with
  | Inl j ->
    calc (==) {
      inv i p;
    (==) { }
      up (h.inv j (down p));
    (==) {h.dup_inv_equiv j (down p)}
      (up (h.inv j (down p) `h.star` h.inv j (down p)));
    (==) { up_star (h.inv j (down p)) (h.inv j (down p)) }
      inv i p `star` inv i p;
    }

  | Inr j -> 
    calc (==) {
      inv i p;
    (==) {}
      ghost_pts_to h j (Some (down p)) `star` pure (is_boxable p);
    (==) {  share_gather_equiv #_ #(PA.pcm_agreement #h.slprop) j (Some (down p)) (Some (down p)) }
      lift h (H2.ghost_pts_to #_ #(PA.pcm_agreement #h.slprop) j (Some (down p)) `H2.star`
              H2.ghost_pts_to #_ #(PA.pcm_agreement #h.slprop) j (Some (down p))) `star` pure (is_boxable p);
    (==) { lift_star #h (H2.ghost_pts_to #_ #(PA.pcm_agreement #h.slprop) j (Some (down p)))
                        (H2.ghost_pts_to #_ #(PA.pcm_agreement #h.slprop) j (Some (down p))) }
      (ghost_pts_to h j (Some (down p)) `star` ghost_pts_to h j (Some (down p))) `star` pure (is_boxable p);
    (==) { dup_pure #( h) (is_boxable p) }
      (ghost_pts_to h j (Some (down p)) `star` ghost_pts_to h j (Some (down p))) `star` (pure (is_boxable p) `star` pure (is_boxable p));
    (==) { ac_lemmas_ext h }
      inv i p `star` inv i p;
    }

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
    is_ghost_action_refl = (fun m -> h.is_ghost_action_refl m.small);
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
    pts_to = pts_to h;
    ghost_pts_to = ghost_pts_to h;
    iname = ext_iname h;
    iref = ext_iref h;
    iref_erasable = iref_erasable h;
    iname_of = iname_of h;
    inv = inv #h;
    iname_ok = iname_ok h;
    dup_inv_equiv = dup_inv_equiv #h;
    mem_invariant = mem_invariant;
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
        let right = { small_core = s1; big_core = H2.empty_heap } in
        H2.join_empty m1.big_core;
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

let mem_intension (#a:eqtype) (x:a) (f:(a -> Tot bool))
: Lemma 
  (ensures (Set.mem x (Set.intension f) = f x))
  [SMTPat (Set.mem x (Set.intension f))]
= FStar.Set.mem_intension x f

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
                                      istore_invariant #h m0.ctr (lift_inames ex) m0.big);
        (==) { _ by (T.mapply (quote (pqrs_pr_qs (extend h)))) }
          (up pre `star` up (h.mem_invariant (down_inames (lift_inames ex)) m0.small)) `star` (
           frame `star` istore_invariant #h m0.ctr (lift_inames ex) m0.big
          );
        (==) { () }
          (up (pre `h.star` h.mem_invariant (down_inames (lift_inames ex)) m0.small)) `star` (
           frame `star` istore_invariant #h m0.ctr (lift_inames ex) m0.big
          );
        (==) { }
          (up (pre `h.star` h.mem_invariant ex m0.small)) `star` (
           frame `star` istore_invariant #h m0.ctr (lift_inames ex) m0.big
          );
        };
        let (| frame', restore |) =
          down_frame
            (pre `h.star` h.mem_invariant ex m0.small)
            (frame `star` istore_invariant #h m0.ctr (lift_inames ex) m0.big)
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
            (frame `star` istore_invariant #h m0.ctr (lift_inames ex) m0.big))
          m1
        );
        calc (==) {
          (up (post x `h.star` h.mem_invariant ex m1') `star`
            (frame `star` istore_invariant #h m0.ctr (lift_inames ex) m0.big));
        (==) {}
          (up (post x) `star` up (h.mem_invariant ex m1')) `star`
            (frame `star` istore_invariant #h m0.ctr (lift_inames ex) m0.big);
        (==) { _ by (T.mapply (quote (pqrs_pr_qs (extend h)))) }
          up (post x) `star` frame `star`
            (up (h.mem_invariant ex m1') `star` 
             istore_invariant #h m0.ctr (lift_inames ex) m0.big);
        (==) {}
          up (post x) `star` frame `star`
            (up (h.mem_invariant (down_inames (lift_inames ex)) m1') `star` 
             istore_invariant #h m0.ctr (lift_inames ex) m0.big);
        (==) { () }
          up (post x) `star` frame `star` (mem_invariant (lift_inames ex) m1);
        };
        down_inames_ok #h ex m1;
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
      h.is_ghost_action_refl m0.small;
      (), m0
 