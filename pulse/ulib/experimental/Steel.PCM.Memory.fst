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
module Steel.PCM.Memory
module F = FStar.FunctionalExtensionality
open FStar.FunctionalExtensionality
open Steel.PCM
module H = Steel.PCM.Heap

noeq
type lock_state : Type u#(a + 1) =
  | Invariant : H.slprop u#a -> lock_state

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

let core_mem (m:mem) : mem = mem_of_heap (heap_of_mem m)

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

let interp p m = H.interp p m.heap

let ref = H.ref

let emp : slprop u#a = H.emp
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
  : Lemma (H.equiv p1 p2 <==> equiv p1 p2)
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

////////////////////////////////////////////////////////////////////////////////
//pts_to
////////////////////////////////////////////////////////////////////////////////

let pts_to_compatible (#a:Type u#a)
                      (#pcm:_)
                      (x:ref a pcm)
                      (v0 v1:a)
                      (m:mem u#a)
  = H.pts_to_compatible x v0 v1 (heap_of_mem m)

////////////////////////////////////////////////////////////////////////////////
// star
////////////////////////////////////////////////////////////////////////////////

let intro_star p q mp mq =
  H.intro_star p q (heap_of_mem mp) (heap_of_mem mq)

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

let lock_addr = nat
module S = FStar.Set
module L = FStar.List.Tot
let rec lock_store_invariant (e:S.set lock_addr) (l:lock_store u#a) : slprop u#a =
  let current_addr = L.length l - 1 in
  match l with
  | [] -> emp
  | Invariant p :: tl ->
    if current_addr `S.mem` e then
      lock_store_invariant e tl
    else
      p `star` lock_store_invariant e tl

let heap_ctr_valid (ctr:nat) (h:H.heap u#a) : H.a_heap_prop u#a =
  fun _ -> h `H.free_above_addr` ctr

let locks_invariant (e:S.set lock_addr) (m:mem u#a) : slprop u#a =
  H.h_refine (lock_store_invariant e m.locks)
             (heap_ctr_valid m.ctr (heap_of_mem m))

(***** Following lemmas are needed in Steel.Effect *****)

let core_mem_interp (hp:slprop u#a) (m:mem u#a) = ()

let interp_depends_only_on (hp:slprop u#a) = H.interp_depends_only_on hp

let h_exists_cong (#a:Type) (p q : a -> slprop)
    : Lemma
      (requires (forall x. p x `equiv` q x))
      (ensures (h_exists p `equiv` h_exists q))
    = equiv_heap_iff_equiv_forall ();
      H.h_exists_cong p q

////////////////////////////////////////////////////////////////////////////////
// Lifting heap actions
////////////////////////////////////////////////////////////////////////////////

let linv (m:mem) = locks_invariant Set.empty m

let hheap_of_hmem #fp (m:hmem_with_inv fp) : H.hheap (fp `star` linv m) =
  heap_of_mem m

let hmem_of_hheap (#fp0 #fp1:slprop) (m:hmem_with_inv fp0)
                  (h:H.hheap (fp1 `star` linv m) {
                    forall ctr. heap_of_mem m `H.free_above_addr` ctr <==>
                           h `Heap.free_above_addr` ctr
                  })
    : hmem_with_inv fp1
    = let m1 : mem = { m with heap = h } in
      assert (interp (fp1 `star` linv m) m1);
      star_commutative fp1 (linv m);
      assert (interp (linv m `star` fp1) m1);
      assert (linv m1 ==  H.h_refine (lock_store_invariant S.empty m1.locks)
                                     (heap_ctr_valid m1.ctr (heap_of_mem m1)));
      assert (linv m ==  H.h_refine (lock_store_invariant S.empty m1.locks)
                                    (heap_ctr_valid m1.ctr (heap_of_mem m)));
      assert (forall h. (heap_ctr_valid m1.ctr (heap_of_mem m)) h <==>
                   (heap_ctr_valid m1.ctr (heap_of_mem m1)) h);
      H.refine_equiv (lock_store_invariant S.empty m1.locks)
                     (lock_store_invariant S.empty m1.locks)
                     (heap_ctr_valid m1.ctr (heap_of_mem m))
                     (heap_ctr_valid m1.ctr (heap_of_mem m1));
      assert (linv m `equiv` linv m1);
      let _ = equiv_extensional_on_star (linv m) (linv m1) fp1 in
      assert ((linv m `star` fp1) `equiv` (linv m1 `star` fp1));
      assert (interp (linv m1 `star` fp1) m1);
      star_commutative (linv m1) fp1;
      assert (interp (fp1 `star` linv m1) m1);
      m1

let ac_reasoning_for_m_frame_preserving _ _ _ _ = admit()

let with_inv (m:mem) (fp:slprop) = interp (fp `star` locks_invariant Set.empty m) m

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

let lift_heap_action (#fp:slprop) (#a:Type) (#fp':a -> slprop)
                     ($f:H.action fp a fp')
  : action fp a fp'
  = let g : pre_action fp a fp' = fun m ->
        let h0 = hheap_of_hmem m in
        let (| x, h' |) = f h0 in
        (| x, hmem_of_hheap m h' |)
    in
    let aux (frame:slprop) (m0:hmem_with_inv (fp `star` frame))
      : Lemma
        (ensures
          (ac_reasoning_for_m_frame_preserving fp frame (locks_invariant Set.empty m0) m0;
           let (| x, m1 |) = g m0 in
           interp ((fp' x `star` frame) `star` locks_invariant Set.empty m1) m1 /\
           (forall (mp:mprop frame). mp (core_mem m0) == mp (core_mem m1))))
        [SMTPat ()]
      = ac_reasoning_for_m_frame_preserving fp frame (locks_invariant Set.empty m0) m0;
        let (| x, m1 |) = g m0 in
        let h0 = hheap_of_hmem m0 in
        let (| x', h1 |) = f h0 in
        H.action_framing f (linv m0) h0;
        assert (x == x');
        star_associative fp frame (linv m0);
        H.action_framing f (frame `star` linv m0) h0;
        assert (H.interp ((fp' x) `star` (frame `star` linv m0)) h1);
        star_associative (fp' x) frame (linv m0);
        assert (H.interp ((fp' x `star` frame) `star` linv m0) h1);
        let h1' : H.hheap ((fp' x `star` frame) `star` linv m0) = h1 in
        assert (m1 == hmem_of_hheap m0 h1');
        assert (with_inv m1 (fp' x `star` frame));
        assert (forall (hp:H.hprop frame). hp h0 == hp h1);
        let aux_h (hp:H.hprop frame)
          : Lemma (hp h0 == hp h1)
          = ()
        in
        let aux (mp:mprop frame)
          : Lemma
            (ensures mp (core_mem m0) == mp (core_mem m1))
            [SMTPat ()]
          = assert (core_mem m1 == (core_mem ({m0 with heap = h1})));
            assert (heap_of_mem m0 == h0);
            let q = as_hprop frame mp in
            assert (mp (core_mem m0) == q h0);
            aux_h q
        in
        ()
    in
    assert (is_frame_preserving g);
    g

let sel_action r v0
  = lift_heap_action (H.sel_action r v0)

let upd_action r v0 v1
  = lift_heap_action (H.upd_action r v0 v1)
