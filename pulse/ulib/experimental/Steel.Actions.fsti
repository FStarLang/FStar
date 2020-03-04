(*
   Copyright 2019 Microsoft Research

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
module Steel.Actions
open Steel.Memory
open FStar.Real
module U32 = FStar.UInt32
module U = FStar.Universe

let pre_m_action (fp:hprop u#a) (a:Type u#b) (fp':a -> hprop u#a) =
  hmem_with_inv fp -> (x:a & hmem_with_inv (fp' x))

let ac_reasoning_for_m_frame_preserving
  (p q r:hprop u#a) (m:mem u#a)
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

val mem_evolves : FStar.Preorder.preorder (mem u#a)

let is_m_frame_and_preorder_preserving
  (#a:Type u#b)
  (#fp:hprop u#a)
  (#fp':a -> hprop u#a)
  (f:pre_m_action u#a u#b fp a fp') =
  forall (frame:hprop u#a) (m0:hmem_with_inv (fp `star` frame)).
    (ac_reasoning_for_m_frame_preserving fp frame (locks_invariant Set.empty m0) m0;
     let (| x, m1 |) = f m0 in
     interp ((fp' x `star` frame) `star` locks_invariant Set.empty m1) m1 /\
     mem_evolves m0 m1 /\
     (forall (mp:mprop frame). mp (core_mem m0) == mp (core_mem m1)))

let m_action (fp:hprop u#a) (a:Type u#b) (fp':a -> hprop u#a) =
  f:pre_m_action fp a fp'{ is_m_frame_and_preorder_preserving f }

///////////////////////////////////////////////////////////////////////////////
// Locks
///////////////////////////////////////////////////////////////////////////////

val lock (p:hprop u#a) : Type0

val new_lock (p:hprop u#a)
  : m_action u#a u#0 p (lock p) (fun _ -> emp)

val lock_ok (#p:hprop u#a) (l:lock p) (m:mem u#a) : prop

// let pure (p:prop) : hprop = refine emp (fun _ -> p)

// val maybe_acquire
//   (#p: hprop)
//   (l:lock p)
//   (m:hmem emp { lock_ok l m } )
//   : (b:bool & m:hmem (h_or (pure (b == false)) p))

val release
  (#p: hprop u#a)
  (l:lock p)
  (m:hmem_with_inv p { lock_ok l m } )
  : (b:bool & hmem_with_inv u#a emp)

///////////////////////////////////////////////////////////////////////////////
// Invariants
///////////////////////////////////////////////////////////////////////////////
let inv (p:hprop u#a) : Type0 = lock_addr

val inv_ok (#p:hprop u#a) (l:inv p) (m:mem u#a) : prop

val inv_ok_stable (#p: hprop u#a) (l:inv p) (m0 m1:mem u#a)
  : Lemma (inv_ok l m0 /\
           m0 `mem_evolves` m1 ==>
           inv_ok l m1)

val new_inv (p:hprop u#a)
  : f:( m:hmem_with_inv p -> (i:inv p & (m':hmem_with_inv emp{inv_ok i m'})))

val new_inv_mem_evolves (p:hprop u#a) (m0:hmem_with_inv p)
  : Lemma (
      let (| i, m1 |) = new_inv p m0 in
      mem_evolves m0 m1)

val new_inv_preserves_frame (p:hprop u#a) (m0:hmem_with_inv p) (frame:hprop)
  : Lemma
    (requires interp ((p `star` frame) `star` locks_invariant Set.empty m0) m0)
    (ensures (
      let (| i, m1 |) = new_inv p m0 in
      interp ((emp `star` frame) `star` locks_invariant Set.empty m1) m1 /\
           (forall (mp:mprop frame). mp (core_mem m0) == mp (core_mem m1))))

let pre_atomic (uses:Set.set lock_addr)
               (fp:hprop)
               (a:Type)
               (fp':a -> hprop) =
    m:hmem_with_inv' uses fp -> (x:a & hmem_with_inv' uses (fp' x))

let is_atomic_frame_and_preorder_preserving
  (#uses:Set.set lock_addr) (#a:Type) (#fp:hprop) (#fp':a -> hprop)
  (f:pre_atomic uses fp a fp') =
  forall (frame:hprop) (m0:hmem_with_inv' uses (fp `star` frame)).
    (ac_reasoning_for_m_frame_preserving fp frame (locks_invariant uses m0) m0;
     let (| x, m1 |) = f m0 in
     interp ((fp' x `star` frame) `star` locks_invariant uses m1) m1 /\
     mem_evolves m0 m1 /\
     (forall (mp:mprop frame). mp (core_mem m0) == mp (core_mem m1)))

let atomic (uses:Set.set lock_addr)
           (is_ghost:bool)
           (fp:hprop)
           (a:Type)
           (fp':a -> hprop) =
    f:pre_atomic uses fp a fp'{ is_atomic_frame_and_preorder_preserving f}

val interp_inv_unused
  (#p:hprop u#a) (i:inv p)
  (uses:Set.set lock_addr)
  (frame:hprop)
  (m0:mem)
  : Lemma
  (requires inv_ok i m0 /\ not (i `Set.mem` uses))
  (ensures
    (frame `star` locks_invariant uses m0) `equiv`
    ((p `star` frame) `star` locks_invariant (
      Set.union (Set.singleton i) uses) m0
    ))

val promote_atomic_m_action
    (#a:Type u#b) (#fp:hprop u#a) (#fp':a -> hprop u#a) (#is_ghost:bool)
    (f:atomic Set.empty is_ghost fp a fp')
    : m_action fp a fp'

///////////////////////////////////////////////////////////////////////////////
// Utilities
///////////////////////////////////////////////////////////////////////////////

val rewrite_hprop (p:hprop u#a) (p':hprop u#a{p `equiv` p'}) : m_action p unit (fun _ -> p')

val weaken_hprop
  (uses:Set.set lock_addr)
  (p q:hprop u#a)
  (proof: (m:mem u#a) -> Lemma (requires interp p m) (ensures interp q m))
  : atomic
    uses
    true
    p
    unit
    (fun _ -> q)

////////////////////////////////////////////////////////////////////////////////
// Arrays
////////////////////////////////////////////////////////////////////////////////

val as_seq (#t:_) (a:array_ref t) (m:hmem (array a))
  : (Seq.lseq t (U32.v (length a)))

/// as_seq respect pts_to_array
val as_seq_lemma
  (#t:_)
  (a:array_ref t)
  (i:U32.t{U32.v i < U32.v (length a)})
  (p:perm{readable p})
  (m:hmem (array_perm a p))
  : Lemma (interp (array a) m /\
           interp (pts_to_array a p (as_seq a m)) m)

val index_array
  (#t:_)
  (uses:Set.set lock_addr)
  (a:array_ref t{not (is_null_array a)})
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p:perm{readable p})
  (i:U32.t{U32.v i < U32.v (length a)})
  : atomic
    uses
    false
    (pts_to_array a p iseq)
    (x:t{x == Seq.index iseq (U32.v i)})
    (fun _ -> pts_to_array a p iseq)

val upd_array
  (#t:_)
  (uses:Set.set lock_addr)
  (a:array_ref t{not (is_null_array a)})
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v: t)
  : atomic
    uses
    false
    (pts_to_array a full_perm iseq)
    unit
    (fun _ -> pts_to_array a full_perm (Seq.upd iseq (U32.v i) v))

val alloc_array
  (#t: Type u#a)
  (len:U32.t)
  (init: t)
  : m_action
    emp
    (a:array_ref t{length a = len /\ offset a = 0ul /\ max_length a = len})
    (fun a -> pts_to_array a full_perm (Seq.Base.create (U32.v len) init))

val free_array
  (#t: _)
  (a: array_ref t{freeable a})
  : m_action
    (array_perm a full_perm)
    unit
    (fun _ -> emp)

val split_array
  (#t: _)
  (uses:Set.set lock_addr)
  (a: array_ref t)
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (p: perm{readable p})
  (i:U32.t{U32.v i < U32.v (length a)})
  : atomic
    uses
    false
    (pts_to_array a p iseq)
    (as:(array_ref t & array_ref t){
     length (fst as) = i /\ length (snd as) = U32.sub (length a) i /\
      (not (is_null_array a) ==>
        (U32.v i > 0 ==> address (fst as) = address a /\ max_length (fst as) = max_length a /\
          offset (fst as) = offset a) /\
        (U32.v i < U32.v (length a) ==> address (snd as) = address a /\
          max_length (snd as) = max_length a /\ offset (snd as) = U32.add (offset a) i)
      )
    })
    (fun (a1, a2) -> star
      (pts_to_array a1 p (Seq.slice iseq 0 (U32.v i)))
      (pts_to_array a2 p (Seq.slice iseq (U32.v i) (U32.v (length a))))
    )


val glue_array
  (#t: _)
  (uses:Set.set lock_addr)
  (a: array_ref t)
  (a': array_ref t{
    ((not (is_null_array a) /\ not (is_null_array a')) ==> address a = address a') /\
    max_length a = max_length a' /\
    offset a' = U32.add (offset a) (length a)
  })
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (iseq': Ghost.erased (Seq.lseq t (U32.v (length a'))))
  (p: perm{readable p})
  : atomic
    uses
    false
    (star (pts_to_array a p iseq) (pts_to_array a' p iseq'))
    (new_a:array_ref t{
      max_length new_a = max_length a /\
      offset new_a = offset a /\ length new_a = U32.add (length a) (length a') /\
      (not (is_null_array a) ==> address new_a = address a)
    })
    (fun new_a -> pts_to_array new_a p (Seq.Base.append iseq iseq'))


///////////////////////////////////////////////////////////////////////////////
// References with preorders
///////////////////////////////////////////////////////////////////////////////

val sel_ref
  (#t: Type)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (h: hmem (ref r))
  : Tot t

val sel_ref_lemma
  (#t: Type)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (p: perm{readable p})
  (m: hmem (ref_perm r p))
  : Lemma (
    interp (ref r) m /\
    interp (pts_to_ref r p (sel_ref r m)) m
  )

val sel_ref_or_dead
  (#t: Type)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (h: hmem (ref_or_dead r))
  : Tot t

val sel_ref_or_dead_lemma
  (#t: Type)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (m: hmem (ref r))
  : Lemma (
    interp (ref_or_dead r) m /\ sel_ref r m == sel_ref_or_dead r m
  )

val sel_ref_depends_only_on (#a:Type) (#pre:Preorder.preorder a)
  (r:reference a pre) (p:perm{readable p})
  (m0:hmem (ref_perm r p)) (m1:mem)
: Lemma
  (requires disjoint m0 m1)
  (ensures
    interp (ref_perm r p) (join m0 m1) /\
    interp (ref r) m0 /\ interp (ref r) (join m0 m1) /\
    sel_ref r m0 == sel_ref r (join m0 m1))

val get_ref
  (#t: Type)
  (uses:Set.set lock_addr)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (p: perm{readable p})
  : atomic
    uses
    false
    (ref_perm r p)
    (x:t)
    (fun x -> pts_to_ref r p x)

val set_ref
  (#t: Type)
  (uses:Set.set lock_addr)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (old_v: Ghost.erased t)
  (v:t{pre old_v v})
  : atomic
    uses
    false
    (pts_to_ref r full_perm old_v)
    unit
    (fun _ -> pts_to_ref r full_perm v)

val alloc_ref
  (#t: Type)
  (v: t)
  (pre: Ghost.erased (Preorder.preorder t))
  : m_action
    emp
    (reference t pre)
    (fun r -> pts_to_ref r full_perm v)

val free_ref
  (#t: Type)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  : m_action
    (ref_perm r full_perm)
    unit
    (fun _ -> emp)

val get_ref_refine
  (#t:Type)
  (uses:Set.set lock_addr)
  (#pre:Preorder.preorder t)
  (r:reference t pre)
  (p:perm{readable p})
  (q:t -> hprop)
  : atomic
    uses
    false
    (h_exists (fun (v:t) -> pts_to_ref r p v `star` q v))
    (x:t)
    (fun v -> pts_to_ref r p v `star` q v)

val get_ref_refine_ghost
  (#t:Type)
  (uses:Set.set lock_addr)
  (#pre:Preorder.preorder t)
  (r:reference t pre)
  (p:perm{readable p})
  (q:t -> hprop)
  : atomic
    uses
    true
    (h_exists (fun (v:t) -> pts_to_ref r p v `star` q v))
    (x:t)
    (fun v -> pts_to_ref r p v `star` q v)


let raise_preorder (#t: Type0) (pre: Preorder.preorder t) : Preorder.preorder (U.raise_t u#0 u#a t)
  =
  (fun x y -> pre (U.downgrade_val x) (U.downgrade_val y))

val cas
  (#t:eqtype)
  (uses:Set.set lock_addr)
  (r:reference (U.raise_t u#0 u#a t) (trivial_preorder (U.raise_t u#0 u#a t)))
  (v:Ghost.erased t)
  (v_old:t)
  (v_new:t)
  : atomic
    uses
    false
    (pts_to_ref r full_perm (U.raise_val (Ghost.reveal v)))
    (b:bool{b <==> (Ghost.reveal v == v_old)})
    (fun b -> if b then
      pts_to_ref r full_perm (U.raise_val v_new)
    else
      pts_to_ref r full_perm (U.raise_val (Ghost.reveal v))
    )

//////////////////////////////////////////////////////////////////////////
// Monotonic state
//////////////////////////////////////////////////////////////////////////

val reference_preorder_respected
  (#t: Type)
  (#pre: Preorder.preorder t)
  (r: reference t pre)
  (m0 m1:mem)
  : Lemma
    (requires (
      interp (ref_or_dead r) m0 /\
      mem_evolves m0 m1
    ))
    (ensures (interp (ref_or_dead r) m1 /\ pre (sel_ref_or_dead r m0) (sel_ref_or_dead r m1)))
