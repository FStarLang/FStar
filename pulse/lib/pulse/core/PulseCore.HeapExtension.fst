module PulseCore.HeapExtension
open PulseCore.HeapSig
open FStar.Ghost
open FStar.PCM
open FStar.FunctionalExtensionality
module H2 = PulseCore.Heap2
module F = FStar.FunctionalExtensionality

noeq
type core (h:heap_sig u#a) : Type u#(a + 2) = {
    small_core : h.sep.core;
    big_core : H2.heap u#(a + 1);
}

noeq
type mem (h:heap_sig u#a) : Type u#(a + 2) = {
    small : h.mem;
    big : H2.heap u#(a + 1);
    ctr : nat;
    ghost_ctr: erased nat;
}

(* A lens between mem and core *)
let get_core (#h:heap_sig u#h) (m:mem h) : core h = {
    small_core = h.sep.lens_core.get m.small;
    big_core = m.big;
}

let put_core (#h:heap_sig u#h) (c:core h) (m:mem h) : mem h = {
    small = h.sep.lens_core.put c.small_core m.small;
    big = c.big_core;
    ctr = m.ctr;
    ghost_ctr = m.ghost_ctr;
}

let get_put (#h:heap_sig u#h) (m:mem h)
: Lemma (put_core (get_core m) m == m)
= h.sep.lens_core.get_put m.small

let put_get (#h:heap_sig u#h) (c:core h) (m:mem h)
: Lemma (get_core (put_core c m) == c)
= h.sep.lens_core.put_get c.small_core m.small

let put_put (#h:heap_sig u#h) (c1 c2:core h) (m:mem h)
: Lemma (put_core c2 (put_core c1 m) == put_core c2 m)
= h.sep.lens_core.put_put c1.small_core c2.small_core m.small

let lens_core (h:heap_sig u#a) : lens (mem h) (core h) = {
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

let sep (h:heap_sig u#a)
: separable (mem h)
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

let full_mem_pred (h:heap_sig u#a) (m:mem h) : prop =
    h.full_mem_pred m.small /\
    H2.full_heap_pred m.big

let is_ghost_action (h:heap_sig u#a) (m0 m1:mem h) : prop =
    h.is_ghost_action m0.small m1.small /\
    H2.concrete m0.big == H2.concrete m1.big /\
    m0.ctr == m1.ctr

let ext_affine_mem_prop (#m:Type u#a) (sep:separable m)
: Type u#(max 1 a)
= p:(sep.core ^-> prop){ is_affine_mem_prop sep p }

let slprop (h:heap_sig u#a) : Type u#(a + 2) = ext_affine_mem_prop (sep h)
let is_restricted_any (#a #b:Type) (f:a ^-> b) : Lemma (F.is_restricted a f) = ()
let slprop_is_restricted (#h:heap_sig u#a) (p:slprop h) 
: Lemma (is_restricted (sep h).core p)
= is_restricted_any p
let interp (#h:heap_sig u#a) (p:slprop h) : affine_mem_prop (sep h) = p
let as_slprop (#h:heap_sig u#a) (p:affine_mem_prop (sep h)) : slprop h = F.on _ p
let equiv (#h:heap_sig u#a) (p1 p2:slprop h) : prop = forall c. interp p1 c <==> interp p2 c
let slprop_extensionality (h:heap_sig u#a) (p1 p2:slprop h)
: Lemma ((forall c. (interp p1 c <==> interp p2 c)) ==> p1 == p2)
        [SMTPat (equiv p1 p2)]
= introduce (forall (c:(sep h).core). (interp p1 c <==> interp p2 c)) ==> p1 == p2
  with _ . (
    FStar.PredicateExtensionality.predicateExtensionality (sep h).core p1 p2;
    slprop_is_restricted p1;
    slprop_is_restricted p2
  )

let non_info_slprop (h:heap_sig u#a) : non_info (slprop h) = fun x -> reveal x
let bprop (h:heap_sig u#a)  : Type u#(a + 1) = h.slprop

let up_p (#h:heap_sig u#a) (p:h.slprop)
: core h -> prop 
= fun c -> h.interp p c.small_core
let up_p_affine (#h:heap_sig u#a) (p:h.slprop)
: Lemma (is_affine_mem_prop (sep h) (up_p #h p))
= ()
let up (#h:heap_sig u#a) (b:h.slprop) : slprop h = as_slprop #h (up_p b)

let down_p (#h:heap_sig u#a) (p:slprop h)
: h.sep.core -> prop
= fun h -> p { small_core = h; big_core = H2.empty_heap }

let down_p_affine (#h:heap_sig u#a) (p:slprop h)
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
    assert ((sep h).disjoint h1_ h2_);
    assert (p (join #h h1_ h2_));
    ()
  )
let down (#h:heap_sig u#a) (p:slprop h) 
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
let pure (h:heap_sig u#a) (p:prop) : slprop h = up (h.pure p)
let emp (h:heap_sig u#a) : slprop h = up h.emp
let star (h:heap_sig u#a) (p1 p2:slprop h) 
: slprop h
= as_slprop (fun (c:(sep h).core) ->
    exists (c1 c2 : core h).
      c1 `(sep h).disjoint` c2 /\
      c == (sep h).join c1 c2 /\
      p1 c1 /\
      p2 c2)
let pure_interp (#h:heap_sig u#a) (p:prop) (c:core h) 
: Lemma (interp (pure h p) c == p)
= h.pure_interp p c.small_core
let pure_true_emp (h:heap_sig u#a) (_:unit)
: Lemma (pure h True == emp h)
= h.pure_true_emp ()
let intro_emp (h:heap_sig u#a) (c:core h)
: Lemma (interp (emp h) c)
= h.intro_emp c.small_core
let emp_unit (h:heap_sig u#a) (p:slprop h)
: Lemma (p == p `star h` emp h)
= introduce forall c. 
    (interp p c <==> interp (p `star h` emp h) c)
  with (
    assert (c == (sep h).join c (empty #h));
    h.intro_emp (empty #h).small_core    
  ); 
  slprop_extensionality h p (p `star h` emp h)
  
let star_commutative (h:heap_sig u#a) (p1 p2:slprop h)
: Lemma (p1 `star h` p2 == p2 `star h` p1)
= assert (equiv (p1 `star h` p2) (p2 `star h` p1))

let star_associative (h:heap_sig u#a) (p1 p2 p3:slprop h)
: Lemma (p1 `star h` (p2 `star h` p3) == (p1 `star h` p2) `star h` p3)
= assert (equiv (p1 `star h` (p2 `star h` p3)) ((p1 `star h` p2) `star h` p3))

let pts_to (h:heap_sig u#a) (#a:Type u#(a + 1)) (#p:pcm a) (r:ref a p) (x:a) : slprop h = admit()
let ghost_pts_to (h:heap_sig u#a) (#a:Type u#(a + 1)) (#p:pcm a) (r:ghost_ref a p) (x:a) : slprop h = admit()

let iname (h:heap_sig u#a) : eqtype = admit()
let iref (h:heap_sig u#a) : Type0 = erased (iname h)
let iref_erasable (h:heap_sig u#a) : non_info (iref h) = admit()
let iname_of (h:heap_sig u#a) (r:iref h) : GTot (iname h) = reveal r
let inv (h:heap_sig u#a) (i:iref h) (p:slprop h) : slprop h = admit()
let inames_ok (h:heap_sig u#a) (e:eset (iname h)) (m:mem h) : prop = admit()
let mem_invariant (h:heap_sig u#a) (e:eset (iname h)) (m:mem h) : slprop h = admit()

let extend (h:heap_sig u#a) = {
    mem = mem h;
    sep = sep h;
    slprop = slprop h;
    slprop_extensionality = slprop_extensionality h;
    as_slprop = as_slprop #h;
    interp = interp #h;
    interp_as = (fun p -> ());
    full_mem_pred = full_mem_pred h;
    is_ghost_action = is_ghost_action h;
    non_info_slprop = non_info_slprop h;
    bprop = bprop h;
    up = up #h;
    down = down #h;
    up_down = up_down #h;
    non_info_bprop = non_info_bprop h;
    emp = emp h;
    pure = pure h;
    star = star h;
    pure_true_emp = pure_true_emp h;
    emp_unit = emp_unit h;
    intro_emp = intro_emp h;
    star_commutative = star_commutative h;
    star_associative = star_associative h;
    pts_to = pts_to h;
    ghost_pts_to = ghost_pts_to h;
    iname = iname h;
    iref = iref h;
    iref_erasable = iref_erasable h;
    iname_of = iname_of h;
    inv = inv h;
    inames_ok = inames_ok h;
    mem_invariant = mem_invariant h;
}
    