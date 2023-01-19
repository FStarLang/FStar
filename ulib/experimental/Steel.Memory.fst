(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Steel.Memory
module F = FStar.FunctionalExtensionality
open FStar.FunctionalExtensionality
open FStar.PCM
module H = Steel.Heap

noeq
type lock_state : Type u#(a + 1) =
  | Invariant : inv:H.slprop u#a -> lock_state

let lock_store : Type u#(a+1) = list (lock_state u#a)

noeq
type mem : Type u#(a + 1) =
  {
    ctr: nat;
    heap: H.heap u#a;
    locks: lock_store u#a;
  }

let heap_of_mem (x:mem) : H.heap = x.heap

let mem_of_heap (h:H.heap) : mem = {
  ctr = 0;
  heap = h;
  locks = []
}

let mem_set_heap (m:mem) (h:H.heap) : mem = {
  ctr = m.ctr;
  heap = h;
  locks = m.locks;
}

let core_mem (m:mem) : mem = mem_of_heap (heap_of_mem m)

let core_mem_invol m = ()

let disjoint (m0 m1:mem u#h)
  : prop
  = m0.ctr == m1.ctr /\
    H.disjoint m0.heap m1.heap /\
    m0.locks == m1.locks

let disjoint_sym m0 m1 = ()

let join m0 m1 = {
  ctr = m0.ctr;
  heap = H.join m0.heap m1.heap;
  locks = m0.locks
}

let join_commutative m0 m1 =
  H.join_commutative m0.heap m1.heap

let disjoint_join m0 m1 m2 =
  H.disjoint_join m0.heap m1.heap m2.heap

let join_associative m0 m1 m2 =
  H.join_associative m0.heap m1.heap m2.heap

let slprop = H.slprop

let interp p m = H.interp p m.heap

let equiv p1 p2 = forall m. interp p1 m <==> interp p2 m

let slprop_extensionality p q =
  assert (forall m. interp p m <==> interp q m);
  let aux (h:H.heap)
    : Lemma (H.interp p h <==> H.interp q h)
            [SMTPat (H.interp p h)]
    = let m : mem = { ctr = 0; heap = h; locks = [] } in
      assert (interp p m <==> interp q m)
  in
  assert (forall h. H.interp p h <==> H.interp q h);
  Steel.Heap.slprop_extensionality p q

let reveal_equiv p1 p2 = ()

let core_ref = H.core_ref

let null = H.null

let is_null = H.is_null

let emp : slprop u#a = H.emp
let pure = H.pure
let pts_to = H.pts_to
let h_and = H.h_and
let h_or = H.h_or
let star = H.star
let wand = H.wand
let h_exists = H.h_exists
let h_forall = H.h_forall

////////////////////////////////////////////////////////////////////////////////
//properties of equiv
////////////////////////////////////////////////////////////////////////////////

let equiv_symmetric (p1 p2:slprop u#a) = H.equiv_symmetric p1 p2

#push-options "--warn_error -271"
let equiv_heap_iff_equiv (p1 p2:slprop u#a)
  : Lemma (ensures (H.equiv p1 p2 <==> equiv p1 p2))
          [SMTPat (equiv p1 p2)]
  = let aux_lr ()
      : Lemma
        (requires H.equiv p1 p2)
        (ensures equiv p1 p2)
        [SMTPat ()]
      = ()
    in
    let aux_rl_helper1 (h:H.heap)
      : Lemma
        (requires equiv p1 p2 /\ H.interp p1 h)
        (ensures H.interp p2 h)
        [SMTPat ()]
      = assert (interp p2 (mem_of_heap h))
    in
    let aux_rl_helper2 (h:H.heap)
      : Lemma
        (requires equiv p1 p2 /\ H.interp p2 h)
        (ensures H.interp p1 h)
        [SMTPat ()]
      = assert (interp p2 (mem_of_heap h))
    in
    let aux_rl ()
      : Lemma
        (requires equiv p1 p2)
        (ensures H.equiv p1 p2)
        [SMTPat ()]
      = () in
    ()

let equiv_heap_iff_equiv_forall ()
  : Lemma (ensures (forall p1 p2. H.equiv p1 p2 <==> equiv p1 p2))
  = let aux p1 p2
      : Lemma (ensures (H.equiv p1 p2 <==> equiv p1 p2))
              [SMTPat ()]
      = equiv_heap_iff_equiv p1 p2
    in
    ()
#pop-options

let equiv_extensional_on_star (p1 p2 p3:slprop u#a) =
  equiv_heap_iff_equiv_forall ();
  H.equiv_extensional_on_star p1 p2 p3

let emp_unit p = H.emp_unit p

let intro_emp m = H.intro_emp (heap_of_mem m)

let pure_equiv p q = H.pure_equiv p q
let pure_interp q m = H.pure_interp q (heap_of_mem m)
let pure_star_interp p q m = H.pure_star_interp p q (heap_of_mem m)

////////////////////////////////////////////////////////////////////////////////
//pts_to
////////////////////////////////////////////////////////////////////////////////

let pts_to_compatible #a #pcm x v0 v1 m
  = H.pts_to_compatible #a #pcm x v0 v1 (heap_of_mem m)
let pts_to_compatible_equiv #a #pcm x v0 v1
  = H.pts_to_compatible_equiv #a #pcm x v0 v1
let pts_to_not_null #a #pcm x v m
  = H.pts_to_not_null #a #pcm x v (heap_of_mem m)

////////////////////////////////////////////////////////////////////////////////
// star
////////////////////////////////////////////////////////////////////////////////

let intro_star p q mp mq =
  H.intro_star p q (heap_of_mem mp) (heap_of_mem mq)

let elim_star p q m =
  let h = heap_of_mem m in
  H.elim_star p q h;
  assert (exists hl hr. H.disjoint hl hr /\ H.join hl hr == h /\ H.interp p hl /\ H.interp q hr);
  let hl = FStar.IndefiniteDescription.indefinite_description_tot H.heap (fun hl ->
     exists hr. H.disjoint hl hr /\ H.join hl hr == h /\ H.interp p hl /\ H.interp q hr) in
  let hr = FStar.IndefiniteDescription.indefinite_description_tot H.heap (fun hr ->
     H.disjoint hl hr /\ H.join hl hr == h /\ H.interp p hl /\ H.interp q hr) in
  let ml = mem_set_heap m hl in
  let mr = mem_set_heap m hr in
  assert (disjoint ml mr);
  assert (m == join ml mr);
  assert (interp p ml);
  assert (interp q mr);
  ()

let interp_star
  (p q: slprop)
  (m: mem)
: Lemma
  (interp (p `star` q) m <==> (exists (mp: mem) (mq: mem) . disjoint mp mq /\ interp p mp /\ interp q mq /\ join mp mq == m))
= let left = interp (p `star` q) m in
  let right = exists (mp: mem) (mq: mem) . disjoint mp mq /\ interp p mp /\ interp q mq /\ join mp mq == m in
  let f ()
  : Lemma
    (requires left)
    (ensures right)
  =
    elim_star p q m
  in
  let g ()
  : Lemma
    (requires right)
    (ensures left)
  =
    Classical.exists_elim left #_ #(fun mp -> exists (mq: mem) . disjoint mp mq /\ interp p mp /\ interp q mq /\ join mp mq == m) () (fun mp ->
      Classical.exists_elim left #_ #(fun mq -> disjoint mp mq /\ interp p mp /\ interp q mq /\ join mp mq == m) () (fun mq ->
        intro_star p q mp mq
      )
    )
  in
  Classical.move_requires f ();
  Classical.move_requires g ()

let star_commutative (p1 p2:slprop) =
  H.star_commutative p1 p2

let star_associative (p1 p2 p3:slprop) =
  H.star_associative p1 p2 p3

let star_congruence (p1 p2 p3 p4:slprop) =
  equiv_heap_iff_equiv_forall ();
  H.star_congruence p1 p2 p3 p4

let affine_star (p q:slprop) (m:mem) =
  H.affine_star p q (heap_of_mem m)

////////////////////////////////////////////////////////////////////////////////
// Invariants on the lock store
////////////////////////////////////////////////////////////////////////////////

let iname = nat
module S = FStar.Set
module L = FStar.List.Tot
module W = FStar.Witnessed.Core

let rec lock_store_invariant (e:inames) (l:lock_store u#a) : slprop u#a =
  let current_addr = L.length l - 1 in
  match l with
  | [] -> emp
  | Invariant p :: tl ->
    if current_addr `S.mem` e then
      lock_store_invariant e tl
    else
      p `star` lock_store_invariant e tl

let lock_i (i:iname) (l:lock_store { i < L.length l }) =
  let ix = L.length l - i - 1 in
  L.index l ix

let iname_for_p (i:iname) (p:slprop) : W.s_predicate lock_store =
  fun l ->
    i < L.length l /\
    (lock_i i l).inv == p

let lock_store_evolves : FStar.Preorder.preorder lock_store =
  fun (l1 l2 : lock_store) ->
    L.length l2 >= L.length l1 /\
    (forall (i:nat{i < L.length l1}).
       (lock_i i l1).inv == (lock_i i l2).inv)

let inames_in (e:inames) (l:lock_store) : prop = forall i. Set.mem i e ==> i < L.length l

let inames_ok e m = inames_in e m.locks

let inames_ok_empty m = ()

let extend_lock_store (e:inames) (l:lock_store{e `inames_in` l}) (p:slprop)
  : i:iname &
    l':lock_store {
      lock_store_invariant e l' == p `star` lock_store_invariant e l /\
      iname_for_p i p l'
    }
  = (| L.length l, Invariant p :: l |)

let set_add (i:iname) (s:inames) = Set.union (Set.singleton i) s

let rec move_invariant (e:inames) (l:lock_store) (p:slprop)
                       (i:iname{iname_for_p i p l /\ ~(i `Set.mem` e)})
   : Lemma (H.equiv (lock_store_invariant e l)
                    (p `star` lock_store_invariant (set_add i e) l))
   = let rec aux (i:iname) (m:lock_store)
       : Lemma (requires i >= L.length m)
               (ensures (lock_store_invariant e m `H.equiv`  lock_store_invariant (set_add i e) m))
       = match m with
         | [] -> ()
         | Invariant p::tl ->
           aux i tl;
           H.star_congruence p (lock_store_invariant e tl) p (lock_store_invariant (set_add i e) tl)
     in
     let current_addr = L.length l - 1 in
     match l with
     | [] -> ()
     | Invariant q::tl ->
       if i = current_addr
       then begin
         assert (lock_store_invariant e l == p `star` lock_store_invariant e tl);
         aux i tl;
         H.star_congruence p (lock_store_invariant e tl) p (lock_store_invariant (set_add i e) tl);
         ()
       end
       else begin
         move_invariant e tl p i;
         assert (lock_store_invariant e tl `equiv`
                 (p `star` lock_store_invariant (set_add i e) tl));
         H.star_congruence q (lock_store_invariant e tl) q (p `star` lock_store_invariant (set_add i e) tl);
         if Set.mem current_addr e
         then ()
         else begin
           let r = lock_store_invariant (set_add i e) tl in
           assert (lock_store_invariant e l `equiv`
                   (q `star` (p `star` r)));
           H.star_associative q p r;
           H.star_commutative q p;
           H.star_congruence (q `star` p) r (p `star` q) r;
           H.star_associative p q r
         end
       end

let heap_ctr_valid (ctr:nat) (h:H.heap u#a) : prop =
    h `H.free_above_addr` ctr

let ctr_validity (ctr:nat) (h:H.heap) : slprop =
    H.pure (heap_ctr_valid ctr h)

let locks_invariant (e:inames) (m:mem u#a) : slprop u#a =
   lock_store_invariant e m.locks
   `star`
   ctr_validity m.ctr (heap_of_mem m)

let full_mem_pred (m:mem) = H.full_heap_pred (heap_of_mem m)

(***** Following lemmas are needed in Steel.Effect *****)

let core_mem_interp (hp:slprop u#a) (m:mem u#a) = ()

let interp_depends_only_on (hp:slprop u#a) = H.interp_depends_only_on hp

let a_mem_prop_as_a_heap_prop
  (sl: slprop u#a)
  (f: a_mem_prop sl)
: Tot (H.a_heap_prop u#a)
=
  let g (h: H.heap u#a) : Tot prop = interp sl (mem_of_heap h) /\ f (mem_of_heap h) in
  let phi0 (h0 h1: H.heap u#a) : Lemma
    (requires (g h0 /\ H.disjoint h0 h1))
    (ensures (g h0 /\ H.disjoint h0 h1 /\ g (H.join h0 h1)))
  = assert (mem_of_heap (H.join h0 h1) == mem_of_heap h0 `join` mem_of_heap h1);
    interp_depends_only_on sl
  in
  let phi1 (h0 h1: H.heap u#a) : Lemma
    (ensures ((g h0 /\ H.disjoint h0 h1) ==> g (H.join h0 h1)))
  =
    Classical.move_requires (phi0 h0) h1
  in
  Classical.forall_intro_2 phi1;
  g

let refine_slprop sl f = H.as_slprop (a_mem_prop_as_a_heap_prop sl f)

let interp_refine_slprop sl f m =
  assert ((interp sl m /\ f m) <==> interp sl (core_mem m) /\ f (core_mem m))

let dep_hprop
  (s: slprop)
  (f: (hmem s -> Tot slprop))
  (h: H.heap)
: Tot prop
= exists (h1: H.heap) . exists (h2: H.heap) . interp s (mem_of_heap h1) /\ H.disjoint h1 h2 /\ interp (f (mem_of_heap h1)) (mem_of_heap h2) /\ h == h1 `H.join` h2

let dep_hprop_is_affine0
  (s: slprop)
  (f: (hmem s -> Tot slprop))
  (h h': H.heap)
  (sq' : squash (dep_hprop s f h /\ H.disjoint h h'))
: Lemma
  (H.disjoint h h' /\ dep_hprop s f (H.join h h'))
=
  let p2 (h h1 h2: H.heap) : Tot prop =
    interp s (mem_of_heap h1) /\
    H.disjoint h1 h2 /\ interp (f (mem_of_heap h1)) (mem_of_heap h2) /\ h == h1 `H.join` h2
  in
  let p1 (h h1: H.heap) : Tot prop =
    (exists h2 . p2 h h1 h2)
  in
  let h1 =
    FStar.IndefiniteDescription.indefinite_description_ghost H.heap (p1 h)
  in
  let h2 =
    FStar.IndefiniteDescription.indefinite_description_ghost H.heap (p2 h h1)
  in
  H.disjoint_join h' h1 h2;
  assert (H.disjoint h2 h');
  let h2' = H.join h2 h' in
  H.join_commutative h2 h' ;
  assert (h2' == H.join h' h2);
  assert (H.disjoint h1 h2');
  assert (mem_of_heap h2' == mem_of_heap h2 `join` mem_of_heap h');
  interp_depends_only_on (f (mem_of_heap h1));
  assert (interp (f (mem_of_heap h1)) (mem_of_heap h2'));
  H.join_commutative h1 h2;
  H.join_associative h' h2 h1;
  H.join_commutative h' h;
  H.join_commutative h2' h1;
  assert (H.join h h' == h1 `H.join` h2')

let impl_intro_gen (#p: Type0) (#q: Type0) ($prf: (squash p -> Lemma (q )))
    : Lemma (p ==> q)
= Classical.impl_intro_gen #p #(fun _ -> q) prf

let dep_hprop_is_affine1
  (s: slprop)
  (f: (hmem s -> Tot slprop))
  (h0 h1: H.heap)
: Lemma
  ((dep_hprop s f h0 /\ H.disjoint h0 h1) ==> (H.disjoint h0 h1 /\ dep_hprop s f (H.join h0 h1)))
= impl_intro_gen (dep_hprop_is_affine0 s f h0 h1)

let dep_hprop_is_affine
  (s: slprop)
  (f: (hmem s -> Tot slprop))
: Lemma
  (H.heap_prop_is_affine (dep_hprop s f))
= Classical.forall_intro_2 (dep_hprop_is_affine1 s f)

let sdep
  (s: slprop)
  (f: (hmem s -> Tot slprop))
: Tot slprop
=
  dep_hprop_is_affine s f;
  H.as_slprop (dep_hprop s f)

let interp_sdep
  (s: slprop)
  (f: (hmem s -> Tot slprop))
  (m: mem)
: Lemma
  (requires (dep_slprop_is_affine s f))
  (ensures (
    interp (sdep s f) m <==> (exists m1 m2 . interp s m1 /\ interp (f m1) m2 /\ disjoint m1 m2 /\ join m1 m2 == m)
  ))
=
  dep_hprop_is_affine s f;
  assert (forall m1 m2 . (interp s m1 /\ interp (f m1) m2 /\ disjoint m1 m2 /\ join m1 m2 == m) ==> (
    interp s (mem_of_heap m1.heap) /\ interp (f (mem_of_heap m1.heap)) (mem_of_heap m2.heap) /\
    H.disjoint m1.heap m2.heap /\
    H.join m1.heap m2.heap == m.heap
  ));
  interp_depends_only_on s;
  Classical.forall_intro (fun m -> interp_depends_only_on (f m));
  assert (forall h1 h2 . (interp s (mem_of_heap h1) /\ interp (f (mem_of_heap h1)) (mem_of_heap h2) /\ H.disjoint h1 h2 /\ H.join h1 h2 == m.heap) ==> (
    core_mem (mem_of_heap h1) == core_mem (mem_set_heap m h1) /\
    interp s (core_mem (mem_of_heap h1)) /\
    interp s (mem_set_heap m h1) /\
    core_mem (mem_of_heap h1) == core_mem (mem_set_heap m h1) /\
    f (mem_set_heap m h1) `equiv` f (mem_of_heap h1) /\
    interp (f (mem_set_heap m h1)) (mem_of_heap h2) /\
    interp (f (mem_set_heap m h1)) (mem_set_heap m h2) /\
    disjoint (mem_set_heap m h1) (mem_set_heap m h2) /\
    join (mem_set_heap m h1) (mem_set_heap m h2) == m
  ));
  ()

let h_exists_cong (#a:Type) (p q : a -> slprop)
    : Lemma
      (requires (forall x. p x `equiv` q x))
      (ensures (h_exists p `equiv` h_exists q))
    = equiv_heap_iff_equiv_forall ();
      H.h_exists_cong p q

let intro_h_exists #a x p m = H.intro_h_exists x p (heap_of_mem m)

let elim_h_exists (#a:_) (p:a -> slprop) (m:mem) = H.elim_h_exists p (heap_of_mem m)

////////////////////////////////////////////////////////////////////////////////
// Preorders and effects
////////////////////////////////////////////////////////////////////////////////
module PP = Steel.Preorder

let mem_evolves =
  fun (m0 m1:full_mem) ->
    H.heap_evolves (heap_of_mem m0) (heap_of_mem m1) /\
    m0.ctr <= m1.ctr /\
    lock_store_evolves m0.locks m1.locks

(** See [Steel.Heap.is_frame_preserving]. We add in [lock_invariants] now *)
let preserves_frame (e:inames) (pre post:slprop) (m0 m1:mem) =
  forall (frame:slprop).
    interp ((pre `star` frame) `star` locks_invariant e m0) m0 ==>
    (interp ((post `star` frame) `star` locks_invariant e m1) m1 /\
     (forall (f_frame:mprop frame). f_frame (core_mem m0) == f_frame (core_mem m1)))

(**
  This is a version of MstTot with frame quantified, as part of preserves_frame
*)
effect MstTotNF (a:Type u#a) (except:inames) (expects:slprop u#1) (provides: a -> slprop u#1) =
  NMSTTotal.NMSTATETOT a (full_mem u#1) mem_evolves
    (requires fun m0 ->
        inames_ok except m0 /\
        interp (expects `star` locks_invariant except m0) m0)
    (ensures fun m0 x m1 ->
        inames_ok except m1 /\
        interp (provides x `star` locks_invariant except m1) m1 /\
        preserves_frame except expects (provides x) m0 m1)

////////////////////////////////////////////////////////////////////////////////
// Lifting heap actions
////////////////////////////////////////////////////////////////////////////////

(**
  Heap actions come in two equivalent flavors:
  - one that take an explicit frame as argument (action_with_frame)
  - and one that quantify over all the frame

  We therefore define two lift routes:
  - a direct route for those with explicit frame
  - via MstTotNF for the rest
*)

let tot_pre_action_nf_except (e:inames) (fp:slprop u#a) (a:Type u#b) (fp':a -> slprop u#a) =
  hmem_with_inv_except e fp ->
  (x:a & hmem_with_inv_except e (fp' x))

let tot_pre_action_nf = tot_pre_action_nf_except S.empty

let ac_reasoning_for_m_frame_preserving
    (p q r:slprop u#a) (m:mem u#a)
  : Lemma
    (requires interp ((p `star` q) `star` r) m)
    (ensures interp (p `star` r) m)
  = calc (equiv) {
    (p `star` q) `star` r;
       (equiv) { star_commutative p q;
                 equiv_extensional_on_star (p `star` q) (q `star` p) r }
    (q `star` p) `star` r;
       (equiv) { star_associative q p r }
    q `star` (p `star` r);
    };
    assert (interp (q `star` (p `star` r)) m);
    affine_star q (p `star` r) m

let is_frame_preserving
  (#e:inames)
  (#a:Type u#b)
  (#fp:slprop u#a)
  (#fp':a -> slprop u#a)
  (f:tot_pre_action_nf_except e fp a fp') =
  forall (frame:slprop u#a) (m0:hmem_with_inv_except e (fp `star` frame)).
    (ac_reasoning_for_m_frame_preserving fp frame (locks_invariant e m0) m0;
     let (| x, m1 |) = f m0 in
     interp ((fp' x `star` frame) `star` locks_invariant e m1) m1 /\
     mem_evolves m0 m1 /\
     (forall (mp:mprop frame). mp (core_mem m0) == mp (core_mem m1)))

let tot_action_nf_except (e:inames) (fp:slprop u#a) (a:Type u#b) (fp':a -> slprop u#a) =
  f:tot_pre_action_nf_except e fp a fp'{ is_frame_preserving f }

let tot_action_nf = tot_action_nf_except S.empty

let linv e (m:mem) = locks_invariant e m

let hheap_of_hmem #fp #e (m:hmem_with_inv_except e fp)
  : h:H.hheap (fp `star` linv e m) { h `H.free_above_addr` m.ctr}
  = let h = heap_of_mem m in
    H.pure_interp (heap_ctr_valid m.ctr (heap_of_mem m)) h;
    h

let hmem_of_hheap #e (#fp0 #fp1:slprop) (m:hmem_with_inv_except e fp0)
                  (h:H.full_hheap (fp1 `star` linv e m) {
                       h `Heap.free_above_addr` m.ctr
                  })
    : m1:hmem_with_inv_except e fp1{linv e m `equiv` linv e m1}
    = let m1 : mem = { m with heap = h } in
      assert (interp (fp1 `star` linv e m) m1);
      star_commutative fp1 (linv e m);
      assert (interp (linv e m `star` fp1) m1);
      assert (linv e m1 ==  (lock_store_invariant e m1.locks)
                            `star` ctr_validity m1.ctr (heap_of_mem m1));
      assert (linv e m ==  (lock_store_invariant e m1.locks)
                             `star` ctr_validity m1.ctr (heap_of_mem m));
      H.pure_interp (heap_ctr_valid m1.ctr (heap_of_mem m))
                    (heap_of_mem m);
      assert (heap_ctr_valid m1.ctr (heap_of_mem m) <==>
              heap_ctr_valid m1.ctr (heap_of_mem m1));
      H.pure_equiv (heap_ctr_valid m1.ctr (heap_of_mem m))
                   (heap_ctr_valid m1.ctr (heap_of_mem m1));
      H.star_congruence (lock_store_invariant e m1.locks)
                        (ctr_validity m1.ctr (heap_of_mem m1))
                        (lock_store_invariant e m1.locks)
                        (ctr_validity m1.ctr (heap_of_mem m));
      assert (linv e m `equiv` linv e m1);
      let _ = equiv_extensional_on_star (linv e m) (linv e m1) fp1 in
      assert ((linv e m `star` fp1) `equiv` (linv e m1 `star` fp1));
      assert (interp (linv e m1 `star` fp1) m1);
      star_commutative (linv e m1) fp1;
      assert (interp (fp1 `star` linv e m1) m1);
      m1

let with_inv_except (m:mem) e (fp:slprop) = interp (fp `star` locks_invariant e m) m

#push-options "--warn_error -271"
let as_hprop (frame:slprop) (mp:mprop frame)
    : hp:H.hprop frame{forall m. mp (core_mem m) == hp (heap_of_mem m)}
    = let f = fun h -> mp (mem_of_heap h) in
      assert (forall m. mp (core_mem m) == f (heap_of_mem m));
      let aux (m0:H.hheap frame) (m1:H.heap{H.disjoint m0 m1})
        : Lemma
          (ensures (mem_of_heap (H.join m0 m1) == join (mem_of_heap m0) (mem_of_heap m1)))
          [SMTPat ()]
        = ()
      in
      f

let mprop_preservation_of_hprop_preservation
       (p:slprop) (m0 m1:mem)
    : Lemma
      (requires (forall (hp:H.hprop p). hp (heap_of_mem m0) == hp (heap_of_mem m1)))
      (ensures (forall (mp:mprop p). mp (core_mem m0) == mp (core_mem m1)))
    = let aux (mp:mprop p)
        : Lemma (mp (core_mem m0) == mp (core_mem m1))
          [SMTPat()]
        = assert (as_hprop p mp (heap_of_mem m0) == as_hprop p mp (heap_of_mem m1))
      in
      ()

let lift_heap_action (#fp:slprop) (#a:Type) (#fp':a -> slprop)
                     (e:inames)
                     ($f:H.action fp a fp')
  : tot_action_nf_except e fp a fp'
  = let g : tot_pre_action_nf_except e fp a fp' = fun m ->
        let h0 = hheap_of_hmem m in
        let (| x, h' |) = f h0 in
        (| x, hmem_of_hheap m h' |)
    in
    let aux (frame:slprop) (m0:hmem_with_inv_except e (fp `star` frame))
      : Lemma
        (ensures
          (ac_reasoning_for_m_frame_preserving fp frame (locks_invariant e m0) m0;
           let (| x, m1 |) = g m0 in
           interp ((fp' x `star` frame) `star` locks_invariant e m1) m1 /\
           mem_evolves m0 m1 /\
           (forall (mp:mprop frame). mp (core_mem m0) == mp (core_mem m1))))
        [SMTPat ()]
      = ac_reasoning_for_m_frame_preserving fp frame (locks_invariant e m0) m0;
        let (| x, m1 |) = g m0 in
        let h0 = hheap_of_hmem m0 in
        let (| x', h1 |) = f h0 in
        H.action_framing f (linv e m0) h0;
        assert (x == x');
        star_associative fp frame (linv e m0);
        H.action_framing f (frame `star` linv e m0) h0;
        assert (H.interp ((fp' x) `star` (frame `star` linv e m0)) h1);
        star_associative (fp' x) frame (linv e m0);
        assert (H.interp ((fp' x `star` frame) `star` linv e m0) h1);
        let h1' : H.hheap ((fp' x `star` frame) `star` linv e m0) = h1 in
        assert (m1 == hmem_of_hheap m0 h1');
        assert (with_inv_except m1 e (fp' x `star` frame));
        assert (forall (hp:H.hprop frame). hp h0 == hp h1);
        mprop_preservation_of_hprop_preservation frame m0 m1;
        ()
    in
    assert (is_frame_preserving g);
    g

let frame_preserving_respects_preorder #a #e #fp #fp' ($f:tot_action_nf_except e fp a fp') (m0:hmem_with_inv_except e fp)
  : Lemma (let (| x, m1 |) = f m0 in
           mem_evolves m0 m1)
  = let aux (frame:slprop) (m0:hmem_with_inv_except e (fp `star` frame))
        : Lemma
          (ac_reasoning_for_m_frame_preserving fp frame (locks_invariant e m0) m0;
            let (| x, m1 |) = f m0 in
            interp ((fp' x `star` frame) `star` locks_invariant e m1) m1 /\
            mem_evolves m0 m1)
        = ()
    in
    H.emp_unit fp;
    assert (interp (fp `star` linv e m0) m0);
    H.star_congruence (fp `star` emp) (linv e m0) fp (linv e m0);
    assert (interp ((fp `star` emp) `star` linv e m0) m0);
    aux emp m0

let lift_tot_action_nf #a #e #fp #fp' ($f:tot_action_nf_except e fp a fp')
  : MstTotNF a e fp fp'
  = let m0 = NMSTTotal.get () in
    let m0' : hmem_with_inv_except e fp = m0 in
    let r = f m0' in
    let (| x, m1 |) = r in
    let m1' : hmem_with_inv_except e (fp' x) = m1 in
    assert (is_frame_preserving f);
    assert (m1 == dsnd (f m0));
    frame_preserving_respects_preorder f m0;
    NMSTTotal.put #_ #(mem_evolves) m1;
    x

let lift_tot_action #a #e #fp #fp'
  ($f:tot_action_nf_except e fp a fp')
  (frame:slprop)
  : MstTot a e fp fp' frame (fun _ -> True) (fun _ _ _ -> True)
  = let m0 = NMSTTotal.get #(full_mem) #_ () in
    ac_reasoning_for_m_frame_preserving fp frame (locks_invariant e m0) m0;
    assert (interp (fp `star` frame `star` locks_invariant e m0) m0);
    assert (interp (fp `star` locks_invariant e m0) m0);
    lift_tot_action_nf f


(**
  Now defining the lift for heap actions with explicit frame
*)

let tot_action_with_frame_except
  (e:inames)
  (fp:slprop u#a)
  (a:Type u#b)
  (fp':a -> slprop u#a)
  = frame:slprop u#a ->
    m0:hmem_with_inv_except e (fp `star` frame) ->
    Pure (x:a & hmem_with_inv_except e (fp' x `star` frame))
      (requires True)
      (ensures fun (| x, m1 |) ->
        mem_evolves m0 m1 /\
        (forall (mp:mprop frame). mp (core_mem m0) == mp (core_mem m1)))

let tot_action_with_frame = tot_action_with_frame_except S.empty

let lift_heap_action_with_frame
  (#fp:slprop u#a)
  (#a:Type u#b)
  (#fp':a -> slprop u#a)
  (e:inames)
  ($f:H.action_with_frame fp a fp')
  : tot_action_with_frame_except e fp a fp'
  = fun frame m0 ->
    let h0 = hheap_of_hmem m0 in

    calc (equiv) {
      fp `star` frame `star` locks_invariant e m0;
         (equiv) { star_associative fp frame (locks_invariant e m0) }
      fp `star` (frame `star` locks_invariant e m0);
    };
    assert (H.interp (fp `star` frame `star` locks_invariant e m0) h0);
    assert (H.interp (fp `star` (frame `star` locks_invariant e m0)) h0);

    //key: apply the heap action with frame * locks_invariant e m0
    let (| x, h1 |) = f (frame `star` locks_invariant e m0) h0 in

    calc (equiv) {
      fp' x `star` (frame `star` locks_invariant e m0);
         (equiv) { star_associative (fp' x) frame (locks_invariant e m0) }
      fp' x `star` frame `star` locks_invariant e m0;
    };
    assert (H.interp (fp' x `star` (frame `star` locks_invariant e m0)) h1);
    assert (H.interp (fp' x `star` frame `star` locks_invariant e m0) h1);

    let m1 = hmem_of_hheap m0 h1 in
    assert (mem_evolves m0 m1);
    mprop_preservation_of_hprop_preservation (frame `star` locks_invariant e m0) m0 m1;
    assert (forall (mp:mprop frame). mp (core_mem m0) == mp (core_mem m1));
    (| x, m1 |)

let lift_tot_action_with_frame #a #e #fp #fp'
  ($f:tot_action_with_frame_except e fp a fp')
  (frame:slprop)
  : MstTot a e fp fp' frame (fun _ -> True) (fun _ _ _ -> True)
  = let m0 = NMSTTotal.get () in
    assert (inames_ok e m0);
    ac_reasoning_for_m_frame_preserving fp frame (locks_invariant e m0) m0;
    assert (interp (fp `star` frame `star` locks_invariant e m0) m0);
    assert (interp (fp `star` locks_invariant e m0) m0);
    let m0' : hmem_with_inv_except e fp = m0 in
    let r = f frame m0' in
    let (| x, m1 |) = r in
    ac_reasoning_for_m_frame_preserving (fp' x) frame (locks_invariant e m1) m1;
    assert (interp (fp' x `star` frame `star` locks_invariant e m1) m1);
    assert (interp (fp' x `star` locks_invariant e m1) m1);
    let m1' : hmem_with_inv_except e (fp' x) = m1 in
    NMSTTotal.put #_ #(mem_evolves) m1;
    x

let sel_action #a #pcm e r v0
  = lift_tot_action (lift_heap_action e (H.sel_action #a #pcm r v0))

let upd_action #a #pcm e r v0 v1
  = lift_tot_action (lift_heap_action e (H.upd_action #a #pcm r v0 v1))

let free_action #a #pcm e r v0
  = lift_tot_action (lift_heap_action e (H.free_action #a #pcm r v0))

let split_action #a #pcm e r v0 v1
  = lift_tot_action (lift_heap_action e (H.split_action #a #pcm r v0 v1))

let gather_action #a #pcm e r v0 v1
  = lift_tot_action (lift_heap_action e (H.gather_action #a #pcm r v0 v1))

let weaken (p q r:slprop) (h:H.hheap (p `star` q) { H.stronger q r })
  : H.hheap (p `star` r)
  = H.weaken p q r h; h

let weaken_pure (q r: prop)
  : Lemma
    (requires (q ==> r))
    (ensures H.stronger (H.pure q) (H.pure r))
  = let aux (h:H.heap)
        : Lemma (ensures (H.interp (H.pure q) h ==> H.interp (H.pure r) h))
                [SMTPat ()]
        = H.pure_interp q h;
          H.pure_interp r h
    in
    ()

let inc_ctr (#p:slprop) #e (m:hmem_with_inv_except e p)
  : m':hmem_with_inv_except e p{m'.ctr = m.ctr + 1 /\ H.stronger (linv e m) (linv e m')}
  = let m' : mem = { m with ctr = m.ctr + 1} in
    assert (interp (p `star` linv e m) m');
    assert (linv e m == lock_store_invariant e m.locks
                        `star`
                        ctr_validity m.ctr (heap_of_mem m));
    assert (linv e m' == lock_store_invariant e m.locks
                         `star`
                        ctr_validity (m.ctr + 1) (heap_of_mem m));
    H.weaken_free_above (heap_of_mem m) m.ctr (m.ctr + 1);
    weaken_pure (heap_ctr_valid m.ctr (heap_of_mem m))
                (heap_ctr_valid (m.ctr + 1) (heap_of_mem m));
    assert (H.stronger
                  (ctr_validity m.ctr (heap_of_mem m))
                  (ctr_validity (m.ctr + 1) (heap_of_mem m)));
    H.star_associative p (lock_store_invariant e m.locks)
                         (ctr_validity m.ctr (heap_of_mem m));
    H.stronger_star (lock_store_invariant e m.locks)
                    (ctr_validity m.ctr (heap_of_mem m))
                    (ctr_validity (m.ctr + 1) (heap_of_mem m));
    H.weaken (p `star` lock_store_invariant e m.locks)
             (ctr_validity m.ctr (heap_of_mem m))
             (ctr_validity (m.ctr + 1) (heap_of_mem m))
             (heap_of_mem m');
    H.star_associative p (lock_store_invariant e m.locks)
                         (ctr_validity (m.ctr + 1) (heap_of_mem m));
    let m' : hmem_with_inv_except e p = m' in
    m'

let frame_related_mems (fp0 fp1:slprop u#a) e (m0:hmem_with_inv_except e fp0) (m1:hmem_with_inv_except e fp1) =
    forall (frame:slprop u#a).
      interp ((fp0 `star` frame) `star` linv e m0) m0 ==>
      interp ((fp1 `star` frame) `star` linv e m1) m1 /\
      mem_evolves m0 m1 /\
      (forall (mp:mprop frame). mp (core_mem m0) == mp (core_mem m1))

let refined_pre_action e (fp0:slprop) (a:Type) (fp1:a -> slprop) =
  m0:hmem_with_inv_except e fp0 ->
  Pure (x:a &
        hmem_with_inv_except e (fp1 x))
       (requires True)
       (ensures fun  (| x, m1 |) ->
         frame_related_mems fp0 (fp1 x) e m0 m1)

let refined_pre_action_as_action (#fp0:slprop) (#a:Type) (#fp1:a -> slprop)
                                 #e ($f:refined_pre_action e fp0 a fp1)
  : tot_action_nf_except e fp0 a fp1
  = let g : tot_pre_action_nf_except e fp0 a fp1 = fun m -> f m in
    let aux (frame:slprop)
            (m0:hmem_with_inv_except e (fp0 `star` frame))
      : Lemma
        (ensures
          (ac_reasoning_for_m_frame_preserving fp0 frame (locks_invariant e m0) m0;
           let (| x, m1 |) = g m0 in
           interp ((fp1 x `star` frame) `star` locks_invariant e m1) m1 /\
           mem_evolves m0 m1 /\
          (forall (mp:mprop frame). mp (core_mem m0) == mp (core_mem m1))))
        [SMTPat ()]
      = ac_reasoning_for_m_frame_preserving fp0 frame (locks_invariant e m0) m0;
        let (| x', m1' |) = g m0 in
        let (| x, m1 |) = f m0 in
        assert (x == x' /\ m1 == m1')
    in
    g

let alloc_action #a #pcm e x
  = let f : refined_pre_action e emp (ref a pcm) (fun r -> pts_to r x)
      = fun m0 ->
        (* NS: 9/29/22 I needed to annotate h : Heap.full_heap, for use with the Core checker
           which generates a guard for checking the implicit pattern "dot" term in the dependent
           pair pattern on the next line. That guard expects `h` to be a full_heap, which is it,
           because it is a projection of m0. However, this is not reflected in `h`'s type. So,
           the Core checker, which produces a guard for the pat_dot_term in isolation, cannot
           recheck the term. If we were to fold in the checking of pat_dot_terms and their guards
           with the rest of the VC, this would work.  *)
        let h : Heap.full_heap = hheap_of_hmem m0 in
        let (|r, h'|) = H.extend #a #pcm x m0.ctr h in
        let m' : hmem_with_inv_except e emp = inc_ctr m0 in
        let h' : H.hheap (pts_to #a #pcm r x `star` linv e m') = weaken _ (linv e m0) (linv e m') h' in
        let m1 : hmem_with_inv_except e (pts_to #a #pcm r x) = hmem_of_hheap m' h' in
        assert (forall frame. H.frame_related_heaps h h' emp (pts_to #a #pcm r x) frame true);
        let aux (frame:slprop)
          : Lemma
            (requires
               interp ((emp `star` frame) `star` linv e m0) m0)
            (ensures
               interp ((pts_to #a #pcm r x `star` frame) `star` linv e m1) m1 /\
               mem_evolves m0 m1 /\
               (forall (mp:mprop frame). mp (core_mem m0) == mp (core_mem m1)))
            [SMTPat (emp `star` frame)]
          = star_associative emp frame (linv e m0);
            assert (H.interp (emp `star` (frame `star` linv e m0)) h);
            assert (H.interp (pts_to #a #pcm r x `star` (frame `star` linv e m0)) h');
            star_associative (pts_to #a #pcm r x) frame (linv e m0);
            assert (H.interp ((pts_to #a #pcm r x `star` frame) `star` linv e m0) h');
            assert (H.stronger (linv e m0) (linv e m'));
            assert (H.equiv (linv e m') (linv e m1));
            assert (H.stronger (linv e m0) (linv e m1));
            let h' : H.hheap ((pts_to #a #pcm r x `star` frame) `star` linv e m1) = weaken _ (linv e m0) (linv e m1) h' in
            assert (H.interp ((pts_to #a #pcm r x `star` frame) `star` linv e m1) h');
            assert (forall (mp:H.hprop frame). mp h == mp h');
            mprop_preservation_of_hprop_preservation frame m0 m1;
            assert (forall (mp:mprop frame). mp (core_mem m0) == mp (core_mem m1))
        in
        assert (frame_related_mems emp (pts_to r x) e m0 m1);
        (| r, m1 |)
    in
    lift_tot_action (refined_pre_action_as_action f)


let select_refine #a #p e r x f
  = lift_tot_action (lift_heap_action e (H.select_refine #a #p r x f))

let upd_gen #a #p e r x y f
  = lift_tot_action (lift_heap_action e (H.upd_gen_action r x y f))

////////////////////////////////////////////////////////////////////////////////
// witness / recall
////////////////////////////////////////////////////////////////////////////////

let witnessed_ref #a #pcm (r:ref a pcm) (fact:property a) (m:full_mem)
  = H.witnessed_ref #a #pcm r fact (heap_of_mem m)

let witnessed_ref_stability #a #pcm (r:ref a pcm) (fact:property a)
  : Lemma
    (requires FStar.Preorder.stable fact (Steel.Preorder.preorder_of_pcm pcm))
    (ensures FStar.Preorder.stable (witnessed_ref r fact) mem_evolves)
  = H.witnessed_ref_stability #a #pcm r fact

let witnessed (#a:Type u#1)
              (#pcm:pcm a)
              (r:ref a pcm)
              (fact:property a)
  = W.witnessed _ mem_evolves (witnessed_ref r fact)

let rearrange_pqr_prq (p q r:slprop)
      : Lemma (((p `star` q) `star` r) `equiv`
               ((p `star` r) `star` q))
      = calc (equiv)
        {
           (p `star` q) `star` r;
             (equiv) { star_associative p q r }
           p `star` (q `star` r);
             (equiv) {
                       star_commutative q r;
                       star_congruence p (q `star` r) p (r `star` q)
                     }
           p `star` (r `star` q);
             (equiv) { star_associative p r q }
           (p `star` r) `star` q;
        }


let preserves_frame_cong (e:inames) (p q:slprop) (r s:slprop) (m0 m1:mem)
  : Lemma
    (requires p `equiv` r /\ q `equiv` s /\       preserves_frame e p q m0 m1)
    (ensures
      preserves_frame e r s m0 m1)
  = let aux0 (p q r s:slprop)
      : Lemma
        (requires p `equiv` s)
        (ensures (((p `star` q) `star` r) `equiv`
                  ((s `star` q) `star` r)))
      = star_congruence p q s q;
        star_congruence (p `star` q) r (s `star` q) r
    in
    let aux (frame:slprop)
      : Lemma (requires interp ((r `star` frame) `star` locks_invariant e m0) m0)
              (ensures interp ((s `star` frame) `star` locks_invariant e m1) m1 /\
               interp ((p `star` frame) `star` locks_invariant e m0) m0)
              [SMTPat (r `star` frame)]
      = aux0 p frame (locks_invariant e m0) r;
        aux0 q frame (locks_invariant e m1) s;
        assert (((p `star` frame) `star` locks_invariant e m0) `equiv`
                ((r `star` frame) `star` locks_invariant e m0));
        assert (interp ((p `star` frame) `star` locks_invariant e m0) m0);
        assert (interp ((q `star` frame) `star` locks_invariant e m1) m1);
        assert (((q `star` frame) `star` locks_invariant e m1) `equiv`
                ((s `star` frame) `star` locks_invariant e m1));
        ()
    in
    ()

let pure_true_equiv (p:slprop)
  : Lemma ((p `star` pure True) `equiv` p)
  = FStar.Classical.forall_intro (pure_star_interp p True);
    emp_unit p;
    assert ((p `star` pure True) `equiv` p)

let preserves_frame_star_pure (e:inames) (p q:slprop) (r s:prop) (m:mem)
  : Lemma
    (requires r /\ s)
    (ensures
      preserves_frame e p q m m <==>
      preserves_frame e (p `star` pure r) (q `star` pure s) m m)
  = pure_equiv r True;
    star_congruence p (pure r) p (pure True);
    pure_equiv s True;
    star_congruence q (pure s) q (pure True);
    pure_true_equiv p;
    pure_true_equiv q;
    let fwd ()
      : Lemma
        (requires preserves_frame e p q m m)
        (ensures  preserves_frame e (p `star` pure r) (q `star` pure s) m m)
        [SMTPat ()]
      = preserves_frame_cong e p q (p `star` pure r) (q `star` pure s) m m
    in
    let bk ()
      : Lemma
        (requires preserves_frame e (p `star` pure r) (q `star` pure s) m m)
        (ensures preserves_frame e p q m m)
        [SMTPat ()]
      = preserves_frame_cong e (p `star` pure r) (q `star` pure s) p q m m
    in
    ()


let witness (#a:Type) (#pcm:pcm a)
            (e:inames)
            (r:erased (ref a pcm))
            (fact:stable_property pcm)
            (v:Ghost.erased a)
            (_:squash (forall z. compatible pcm v z ==> fact z))
            (frame:slprop)
  : MstTot (witnessed r fact) e
           (pts_to r v)
           (fun _ -> pts_to r v) frame
           (fun _ -> True)
           (fun _ _ _ -> True)
  = let m0 = NMSTTotal.get () in
    let _ : unit = 
      let hr : H.ref a pcm = r in
      let v' = H.sel_v hr v (heap_of_mem m0) in
      assert (interp (H.ptr hr) m0 /\ H.sel #a #pcm hr (heap_of_mem m0) == v');
      assert (compatible pcm v v');
      assert (fact v');
      assert (witnessed_ref r fact m0);
      witnessed_ref_stability r fact;
      assert (FStar.Preorder.stable (witnessed_ref r fact) mem_evolves)
    in
    let w = NMSTTotal.witness _ mem_evolves (witnessed_ref r fact) in
    w

let recall (#a:Type u#1) (#pcm:pcm a) (#fact:property a)
           (e:inames)
           (r:erased (ref a pcm))
           (v:Ghost.erased a)
           (w:witnessed r fact)
           (frame:slprop)
  = let m0 = NMSTTotal.get () in
    NMSTTotal.recall _ mem_evolves (witnessed_ref r fact) w;
    let hr : H.ref a pcm = r in
    assert (witnessed_ref r fact m0);
    let v1 = H.sel_v hr v (heap_of_mem m0) in
    assert (compatible pcm v v1);
    assert (H.sel hr (heap_of_mem m0) == v1);
    assert (fact v1);
    assert (interp ((pts_to r v `star` frame) `star` locks_invariant e m0) m0);
    emp_unit ((pts_to r v `star` frame) `star` locks_invariant e m0);
    pure_star_interp ((pts_to r v `star` frame) `star` locks_invariant e m0) (fact v1) m0;
    assert (interp (((pts_to r v `star` frame)
                     `star` locks_invariant e m0)
                     `star` pure (fact v1)) m0);
    rearrange_pqr_prq (pts_to r v `star` frame)
                      (locks_invariant e m0)
                      (pure (fact v1));
    assert (interp (((pts_to r v `star` frame) `star` pure (fact v1)) 
                   `star` locks_invariant e m0) m0);
    rearrange_pqr_prq (pts_to r v) frame (pure (fact v1));
    star_congruence ((pts_to r v `star` frame) `star` pure (fact v1))
                    (locks_invariant e m0)
                    ((pts_to r v `star` pure (fact v1)) `star` frame)
                    (locks_invariant e m0);                    
    Ghost.hide v1

let iname_for_p_mem (i:iname) (p:slprop) : W.s_predicate mem =
  fun m -> iname_for_p i p m.locks

let iname_for_p_stable (i:iname) (p:slprop)
  : Lemma (W.stable full_mem mem_evolves (iname_for_p_mem i p))
  = ()

let ( >--> ) (i:iname) (p:slprop) : Type0 = W.witnessed full_mem mem_evolves (iname_for_p_mem i p)

let hmem_with_inv_equiv e (m:mem) (p:slprop)
  : Lemma (interp (p `star` linv e m) m <==>
           interp (p `star` lock_store_invariant e m.locks) m /\
           heap_ctr_valid m.ctr (heap_of_mem m))
  = calc (<==>) {
      interp (p `star` linv e m) m;
      (<==>) { H.star_associative p (lock_store_invariant e m.locks) (ctr_validity m.ctr (heap_of_mem m)) }
      interp ((p `star` lock_store_invariant e m.locks) `star` ctr_validity m.ctr (heap_of_mem m)) m;
      (<==>) { H.pure_star_interp (p `star` lock_store_invariant e m.locks) (heap_ctr_valid m.ctr (heap_of_mem m)) (heap_of_mem m) }
      interp ((p `star` lock_store_invariant e m.locks) `star` emp) m /\
             (heap_ctr_valid m.ctr (heap_of_mem m));
      (<==>) { H.emp_unit (p `star` lock_store_invariant e m.locks) }
      interp (p `star` lock_store_invariant e m.locks) m /\
             (heap_ctr_valid m.ctr (heap_of_mem m));
    }


let new_invariant_tot_action (e:inames) (p:slprop) (m0:hmem_with_inv_except e p{ e `inames_in` m0.locks })
  : Pure (iname & hmem_with_inv_except e emp)
         (requires True)
         (ensures fun (i, m1) ->
           iname_for_p_mem i p m1 /\
           frame_related_mems p emp e m0 m1 /\
           mem_evolves m0 m1)
  = let (| i, l1 |) = extend_lock_store e m0.locks p in
    let m1 = { m0 with locks = l1 } in
    assert (lock_store_invariant e m1.locks ==
            p `star` lock_store_invariant e m0.locks);
    calc (equiv) {
      linv e m1;
        (equiv) {}
      (lock_store_invariant e m1.locks
        `star`
       ctr_validity m1.ctr (heap_of_mem m1));
        (equiv) {}
      ((p `star` lock_store_invariant e m0.locks)
        `star`
       ctr_validity m1.ctr (heap_of_mem m1));
        (equiv) {
          H.star_associative p (lock_store_invariant e m0.locks) (ctr_validity m1.ctr (heap_of_mem m1))
         }
      (p `star` (lock_store_invariant e m0.locks
        `star`
       ctr_validity m1.ctr (heap_of_mem m1)));
        (equiv) { }
      (p `star` linv e m0);
    };
    assert (iname_for_p_mem i p m1);
    assert (lock_store_evolves m0.locks l1);
    assert (mem_evolves m0 m1);
    hmem_with_inv_equiv e m0 p;
    assert (interp (p `star` lock_store_invariant e m0.locks) m1);
    assert (interp (lock_store_invariant e m1.locks) m1);
    H.emp_unit (lock_store_invariant e m1.locks);
    H.star_commutative (lock_store_invariant e m1.locks) emp;
    assert (interp (emp `star` lock_store_invariant e m1.locks) m1);
    hmem_with_inv_equiv e m1 emp;
    let m1 : hmem_with_inv_except e emp = m1 in
    let aux (frame:slprop)
      : Lemma
        (requires interp ((p `star` frame) `star` linv e m0) m0)
        (ensures interp ((emp `star` frame) `star` linv e m1) m1 /\
                 mem_evolves m0 m1 /\
                 (forall (mp:mprop frame). mp (core_mem m0) <==> mp (core_mem m1)))
        [SMTPat (p `star` frame)]
      = assert (interp ((p `star` frame) `star` linv e m0) m1);
        calc (equiv) {
          ((p `star` frame) `star` linv e m0);
            (equiv) {
                      H.star_commutative p frame;
                      H.star_congruence (p `star` frame) (linv e m0) (frame `star` p) (linv e m0);
                      H.star_associative frame p (linv e m0)
                    }
          (frame `star` (p `star` linv e m0));
            (equiv) {
                      H.star_congruence frame (p `star` linv e m0) frame (linv e m1)
                    }
          (frame `star` linv e m1);
            (equiv) {
                       H.emp_unit (frame `star` linv e m1);
                       H.star_commutative (frame `star` linv e m1) emp;
                       H.star_associative emp frame (linv e m1)
                    }
          ((emp `star` frame) `star` linv e m1);
        };
        assert (interp ((emp `star` frame) `star` linv e m1) m1)
    in
    assert (frame_related_mems p emp e m0 m1);
    ( i, m1 )

let inv (p:slprop u#1) = i:erased iname & (i >--> p)
let name_of_inv #p (i:inv p) = dfst i

let new_invariant (e:inames) (p:slprop) (frame:slprop)
  : MstTot (inv p) e p (fun _ -> emp) frame (fun _ -> True) (fun _ _ _ -> True)
  = let m0 = NMSTTotal.get () in
    ac_reasoning_for_m_frame_preserving p frame (locks_invariant e m0) m0;
    assert (interp (p `star` locks_invariant e m0) m0);
    let r = new_invariant_tot_action e p m0 in
    let ( i, m1 ) = r in
    assert (mem_evolves m0 m1);
    NMSTTotal.put #full_mem #mem_evolves m1;
    iname_for_p_stable i p;
    let w  = NMSTTotal.witness full_mem mem_evolves (iname_for_p_mem i p) in
    (| hide i, w |)

let rearrange_invariant (p q r : slprop) (q0 q1:slprop)
  : Lemma
    (requires q `equiv` (q0 `star` q1))
    (ensures  (p `star` (q `star` r)) `equiv`
              ((q0 `star` p) `star` (q1 `star` r)))
  = calc (equiv)
    {
       p `star` (q `star` r);
         (equiv)
           {
             calc (equiv)
             {
               (q `star` r);
                 (equiv) {
                             star_congruence q r (q0 `star` q1) r
                         }
               (q0 `star` q1) `star` r;
             };
             star_congruence p (q `star` r) p ((q0 `star` q1) `star` r)
           }
       (p `star` ((q0 `star` q1) `star` r));
          (equiv) {
                    star_associative q0 q1 r;
                    star_congruence p ((q0 `star` q1) `star` r)
                                    p (q0 `star` (q1 `star` r));
                    star_associative p q0 (q1 `star` r)
                  }
       (p `star` q0) `star` (q1 `star` r);
          (equiv) {
                     star_commutative p q0;
                     star_congruence (p `star` q0) (q1 `star` r)
                                     (q0 `star` p)  (q1 `star` r)
                  }
       (q0 `star` p) `star` (q1 `star` r);
    }

let preserves_frame_invariant (fp fp':slprop)
                              (opened_invariants:inames)
                              (p:slprop)
                              (i:inv p{not (mem_inv opened_invariants i)})
                              (m0:hmem_with_inv_except (add_inv opened_invariants i) (p `star` fp))
                              (m1:mem)
    : Lemma
      (requires preserves_frame (set_add (name_of_inv i) opened_invariants) (p `star` fp) (p `star` fp') m0 m1 /\
                interp (fp' `star` linv opened_invariants m1) m1 /\
                inames_ok opened_invariants m1 /\
                (lock_store_invariant opened_invariants m0.locks `equiv`
                   (p `star` lock_store_invariant (set_add (name_of_inv i) opened_invariants) m0.locks)) /\
                (lock_store_invariant opened_invariants m1.locks `equiv`
                 (p `star` lock_store_invariant (set_add (name_of_inv i) opened_invariants) m1.locks)))
      (ensures  preserves_frame opened_invariants fp fp' m0 m1)
    =
      let aux (frame:slprop)
        : Lemma
           (requires
             interp ((fp `star` frame) `star` linv opened_invariants m0) m0)
           (ensures
             interp ((fp' `star` frame) `star` linv opened_invariants m1) m1 /\
             (forall (f_frame:mprop frame). f_frame (core_mem m0) == f_frame (core_mem m1)))
           [SMTPat()]
        = rearrange_invariant (fp `star` frame) (lock_store_invariant opened_invariants m0.locks) (ctr_validity m0.ctr (heap_of_mem m0))
                                                p (lock_store_invariant (set_add (name_of_inv i) opened_invariants) m0.locks);
          assert (interp ((p `star` (fp `star` frame)) `star` linv (set_add (name_of_inv i) opened_invariants) m0) m0);
          star_associative p fp frame;
          star_congruence (p `star` (fp `star` frame)) (linv (set_add (name_of_inv i) opened_invariants) m0)
                          ((p `star` fp) `star` frame)  (linv (set_add (name_of_inv i) opened_invariants) m0);
          assert (interp (((p `star` fp) `star` frame) `star` linv (set_add (name_of_inv i) opened_invariants) m0) m0);
          assert (interp (((p `star` fp') `star` frame) `star` linv (set_add (name_of_inv i) opened_invariants) m1) m1);
          star_associative p fp' frame;
          star_congruence ((p `star` fp') `star` frame) (linv (set_add (name_of_inv i) opened_invariants) m1)
                          (p `star` (fp' `star` frame)) (linv (set_add (name_of_inv i) opened_invariants) m1);
          assert (interp ((p `star` (fp' `star` frame)) `star` linv (set_add (name_of_inv i) opened_invariants) m1) m1);
          rearrange_invariant (fp' `star` frame) (lock_store_invariant opened_invariants m1.locks) (ctr_validity m1.ctr (heap_of_mem m1))
                                                 p (lock_store_invariant (set_add (name_of_inv i) opened_invariants) m1.locks);
          assert (interp ((fp' `star` frame) `star` linv opened_invariants m1) m1);
          ()
      in
      ()


let equiv_ext_right (p q r:slprop)
  : Lemma
      (requires q `equiv` r)
      (ensures (p `star` q) `equiv` (p `star` r))
  = calc (equiv) {
      p `star` q;
         (equiv) { star_commutative p q }
      q `star` p;
         (equiv) { equiv_extensional_on_star q r p }
      r `star` p;
         (equiv) { star_commutative p r }
      p `star` r;
    }

let with_inv_helper (fp frame ls1 ctr p ls2:slprop)
  : Lemma
      (requires ls1 `equiv` (p `star` ls2))
      (ensures
        (fp `star` frame `star` (ls1 `star` ctr)) `equiv`
        (p `star` fp `star` frame `star` (ls2 `star` ctr)))
  = calc (equiv) {
      ls1 `star` ctr;
         (equiv) { equiv_extensional_on_star ls1 (p `star` ls2) ctr }
      p `star` ls2 `star` ctr;
    };
    calc (equiv) {
      p `star` ls2 `star` ctr;
         (equiv) { star_associative p ls2 ctr }
      p `star` (ls2 `star` ctr);
    };
    calc (equiv) {
      fp `star` frame `star` p;
         (equiv) { star_commutative (fp `star` frame) p }
      p `star` (fp `star` frame);
         (equiv) { star_associative p fp frame }
      p `star` fp `star` frame;
    };
    calc (equiv) {
      fp `star` frame `star` (ls1 `star` ctr);
         (equiv) { equiv_ext_right (fp `star` frame)
                     (ls1 `star` ctr)
                     (p `star` ls2 `star` ctr) }
      (fp `star` frame) `star` (p `star` ls2 `star` ctr);
         (equiv) { equiv_ext_right (fp `star` frame)
                     (p `star` ls2 `star` ctr)
                     (p `star` (ls2 `star` ctr)) }
      (fp `star` frame) `star` (p `star` (ls2 `star` ctr));
         (equiv) { star_associative (fp `star` frame) p (ls2 `star` ctr) }
      (fp `star` frame `star` p) `star` (ls2 `star` ctr);
         (equiv) { equiv_extensional_on_star
                     (fp `star` frame `star` p)
                     (p `star` fp `star` frame)
                     (ls2 `star` ctr) }
      (p `star` fp `star` frame) `star` (ls2 `star` ctr);
    }

let with_invariant (#a:Type)
                   (#fp:slprop)
                   (#fp':a -> slprop)
                   (#opened_invariants:inames)
                   (#p:slprop)
                   (i:inv p{not (mem_inv opened_invariants i)})
                   (f:action_except a (add_inv opened_invariants i) (p `star` fp) (fun x -> p `star` fp' x))
                   (frame:slprop)
  : MstTot a opened_invariants fp fp' frame (fun _ -> True) (fun _ _ _ -> True)
  = let m0 = NMSTTotal.get () in
    NMSTTotal.recall _ mem_evolves (iname_for_p_mem (name_of_inv i) p) (dsnd i);
    assert (iname_for_p (name_of_inv i) p m0.locks);

    assert (interp (fp `star` frame `star` locks_invariant opened_invariants m0) m0);
    assert (interp (fp `star` frame `star`
      (lock_store_invariant opened_invariants m0.locks `star`
       ctr_validity m0.ctr (heap_of_mem m0))) m0);

    move_invariant opened_invariants m0.locks p (name_of_inv i);
    assert (lock_store_invariant opened_invariants m0.locks `equiv`
            (p `star` lock_store_invariant (set_add (name_of_inv i) opened_invariants) m0.locks));

    with_inv_helper
      fp
      frame
      (lock_store_invariant opened_invariants m0.locks)
      (ctr_validity m0.ctr (heap_of_mem m0))
      p
      (lock_store_invariant (set_add (name_of_inv i) opened_invariants) m0.locks);

    assert (interp (p `star` fp `star` frame `star` locks_invariant (set_add (name_of_inv i) opened_invariants) m0) m0);

    let r = f frame in
    let m1 : full_mem = NMSTTotal.get () in

    assert (interp (p `star` fp' r `star` frame `star` locks_invariant (set_add (name_of_inv i) opened_invariants) m1) m1);
    assert (interp (p `star` fp' r `star` frame `star`
      (lock_store_invariant (set_add (name_of_inv i) opened_invariants) m1.locks `star`
       ctr_validity m1.ctr (heap_of_mem m1))) m1);

    NMSTTotal.recall _ mem_evolves (iname_for_p_mem (name_of_inv i) p) (dsnd i);

    move_invariant opened_invariants m1.locks p (name_of_inv i);
    assert (lock_store_invariant opened_invariants m1.locks `equiv`
            (p `star` lock_store_invariant (set_add (name_of_inv i) opened_invariants) m1.locks));

    with_inv_helper
      (fp' r)
      frame
      (lock_store_invariant opened_invariants m1.locks)
      (ctr_validity m1.ctr (heap_of_mem m1))
      p
      (lock_store_invariant (set_add (name_of_inv i) opened_invariants) m1.locks);

    assert (interp (fp' r `star` frame `star` locks_invariant opened_invariants m1) m1);

    assert (inames_ok opened_invariants m1);
    r

let equiv_pqrs_p_qr_s (p q r s:slprop)
  : Lemma ((p `star` q `star` r `star` s) `equiv`
           (p `star` (q `star` r) `star` s))
  = star_associative p q r;
    equiv_extensional_on_star
      (p `star` q `star` r)
      (p `star` (q `star` r))
      s

let frame (#a:Type)
          (#opened_invariants:inames)
          (#pre:slprop)
          (#post:a -> slprop)
          (#req:mprop pre)
          (#ens:mprop2 pre post)
          (frame:slprop)
          ($f:action_except_full a opened_invariants pre post req ens)
          (frame0:slprop)
  : MstTot a opened_invariants (pre `star` frame) (fun x -> post x `star` frame) frame0
           req ens
  = let m0 : full_mem = NMSTTotal.get () in
    equiv_pqrs_p_qr_s pre frame frame0 (linv opened_invariants m0);
    assert (interp (pre `star` frame `star` frame0 `star` linv opened_invariants m0) m0);
    assert (interp (pre `star` (frame `star` frame0) `star` linv opened_invariants m0) m0);
    let x = f (frame `star` frame0) in
    let m1 : full_mem = NMSTTotal.get () in
    equiv_pqrs_p_qr_s (post x) frame frame0 (linv opened_invariants m1);
    assert (interp (post x `star` (frame `star` frame0) `star` linv opened_invariants m1) m1);
    assert (interp (post x `star` frame `star` frame0 `star` linv opened_invariants m1) m1);
    x

let change_slprop (#opened_invariants:inames)
                  (p q:slprop)
                  (proof: (m:mem -> Lemma (requires interp p m) (ensures interp q m)))
  = let proof (h:H.heap)
      : Lemma (requires H.interp p h)
              (ensures H.interp q h)
      = proof (mem_of_heap h)
    in
    lift_tot_action (lift_heap_action opened_invariants (Steel.Heap.change_slprop p q proof))

(* This module reuses is_frame_monotonic from Heap, but does not expose that
to clients, so we need this lemma to typecheck witness_h_exists below. *)
let relate_frame_monotonic_1 #a p
  : Lemma (requires (H.is_frame_monotonic p))
          (ensures (is_frame_monotonic p))
  = ()

let relate_frame_monotonic_2 #a p
  : Lemma (requires (is_frame_monotonic p))
          (ensures (H.is_frame_monotonic p))
  =  let aux (x y : a) (h : H.heap) (f : H.slprop) :
      Lemma (requires (H.interp (p x `H.star` f) h /\ H.interp (p y) h))
            (ensures (H.interp (p y `H.star` f) h))
      =
        let m = mem_of_heap h in
        assert (interp (p x `star` f) m);
        assert (interp (p y)          m);
        assert (interp (p y `star` f) m)
    in
    Classical.forall_intro_4 (fun x y h f -> Classical.move_requires (aux x y h) f)

let witness_h_exists #opened_invariants #a p =
  lift_tot_action_with_frame (lift_heap_action_with_frame opened_invariants (H.witness_h_exists p))

let lift_h_exists #opened_invariants p = lift_tot_action (lift_heap_action opened_invariants (H.lift_h_exists p))

let elim_pure #opened_invariants p = lift_tot_action (lift_heap_action opened_invariants (H.elim_pure p))

let pts_to_join (#a:Type) (#pcm:pcm a) (r:ref a pcm) (x y : a) (m:mem) :
  Lemma (requires (interp (pts_to r x) m /\ interp (pts_to r y) m))
        (ensures (joinable pcm x y)) =
  H.pts_to_join #a #pcm r x y (heap_of_mem m)

let pts_to_evolve (#a:Type u#a) (#pcm:_) (r:ref a pcm) (x y : a) (m:mem)
  : Lemma (requires (interp (pts_to r x) m /\ compatible pcm y x))
          (ensures  (interp (pts_to r y) m))
  = H.pts_to_evolve #a #pcm r x y (heap_of_mem m)

let id_elim_star p q m =
  let starprop (ml:mem) (mr:mem) =
      disjoint ml mr
    /\ m == join ml mr
    /\ interp p ml
    /\ interp q mr
  in
  elim_star p q m;
  let p1 : mem -> prop = fun ml -> (exists mr. starprop ml mr) in
  let ml = IndefiniteDescription.indefinite_description_tot _ p1 in
  let starpropml mr : prop = starprop ml mr in // this prop annotation seems needed
  let mr = IndefiniteDescription.indefinite_description_tot _ starpropml in
  (ml, mr)

let id_elim_exists #a p m =
  let existsprop (x:a) =
    interp (p x) m
  in
  elim_h_exists p m;
  let x = IndefiniteDescription.indefinite_description_tot _ existsprop in
  x


let slimp_star (p q r s : slprop)
  : Lemma (requires (slimp p q /\ slimp r s))
          (ensures (slimp (p `star` r) (q `star` s)))
  = let aux (m:mem) : Lemma (requires (interp (p `star` r) m))
                            (ensures (interp (q `star` s) m))
    =
      let (ml, mr) = id_elim_star p r m in
      intro_star q s ml mr
   in
   Classical.forall_intro (Classical.move_requires aux)

let elim_wi #a (p : a -> slprop{is_witness_invariant p}) (x y : a) (m : mem)
  : Lemma (requires (interp (p x) m /\ interp (p y) m))
          (ensures (x == y))
  = ()

let witinv_framon (#a:Type) (p : a -> slprop)
  : Lemma (is_witness_invariant p ==> is_frame_monotonic p)
          [SMTPatOr [[SMTPat (is_witness_invariant p)]; [SMTPat (is_frame_monotonic p)]]]
  = ()

let star_is_frame_monotonic (#a:Type)
    (f g : a -> slprop)
  : Lemma (requires (is_frame_monotonic f /\ is_frame_monotonic g))
          (ensures (is_frame_monotonic (fun x -> f x `star` g x)))
  = let aux (x y : a) (m:mem) (frame : slprop)
       : Lemma (requires interp ((f x `star` g x) `star` frame) m
                        /\ interp (f y `star` g y) m)
               (ensures (interp ((f y `star` g y) `star` frame) m))
       = star_associative (f x) (g x) frame;
         let (m1, m23) = id_elim_star (f x) (g x `star` frame) m in
         let (m2, m3)  = id_elim_star (g x) frame m23 in
         affine_star (f y) (g y) m;
         assert (interp (f y) m);
         assert (interp (g y) m);
         assert (interp (f x `star` (g x `star` frame)) m);
         assert (interp (f y `star` (g x `star` frame)) m);

         (* flip and do the same reasoning *)
         star_associative (f y) (g x) frame;
         star_commutative (f y) (g x);
         star_congruence (f y `star` g x) frame (g x `star` f y) frame;
         star_associative (g x) (f y) frame;
         assert (interp (g x `star` (f y `star` frame)) m);
         assert (interp (g y `star` (f y `star` frame)) m);

         (* get back in shape *)
         star_associative (f y) (g y) frame;
         star_commutative (f y) (g y);
         star_congruence (f y `star` g y) frame (g y `star` f y) frame;
         star_associative (g y) (f y) frame;
         assert (interp (f y `star` (g y `star` frame)) m);
         ()
    in
    Classical.forall_intro_4 (fun x y m -> Classical.move_requires (aux x y m));
    ()

let star_is_witinv_left (#a:Type)
    (f g : a -> slprop)
  : Lemma (requires (is_witness_invariant f))
          (ensures  (is_witness_invariant (fun x -> f x `star` g x)))
  = ()

let star_is_witinv_right (#a:Type)
    (f g : a -> slprop)
  : Lemma (requires (is_witness_invariant g))
          (ensures  (is_witness_invariant (fun x -> f x `star` g x)))
  = ()
