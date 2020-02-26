module Steel.Effect.Atomic

open Steel.Memory
open Steel.Actions
module Sem = Steel.Semantics.Hoare.MST
open Steel.Semantics.Instantiate

type pre_t = hprop
type post_t (a:Type) = a -> hprop

// TODO: Add pre/postconditions
let atomic_t (#a:Type) (uses:Set.set lock_addr) (is_ghost:bool) (pre:pre_t) (post:post_t a) =
  unit ->
  Sem.Mst a #state
  (requires fun m0 ->
    interp (pre `star` locks_invariant uses m0) m0)
  (ensures fun m0 x m1 ->
    interp ((post x) `star` locks_invariant uses m1) m1)
//    Sem.preserves_frame pre (post x) m0 m1)

type atomic_repr (a:Type) (uses:Set.set lock_addr) (is_ghost:bool) (pre:pre_t) (post:post_t a) =
  atomic_t uses is_ghost pre post

let returnc (a:Type u#a) (x:a) : atomic_repr a Set.empty true emp (fun _ -> emp)
  = fun _ -> x

// TODO: Move refinement to Pure once it is supported
let bind (a:Type) (b:Type) (uses:Set.set lock_addr)
  (is_ghost1:bool) (is_ghost2:bool{is_ghost1 \/ is_ghost2})
  (pre_f:pre_t) (post_f:post_t a) (post_g:post_t b)
  (f:atomic_repr a uses is_ghost1 pre_f post_f)
  (g:(x:a -> atomic_repr b uses is_ghost2 (post_f x) post_g))
  : (atomic_repr b uses (is_ghost1 && is_ghost2) pre_f post_g)
  = fun m0 ->
    let x = f () in
    g x ()

let subcomp (a:Type) (uses:Set.set lock_addr) (is_ghost:bool) (pre:pre_t) (post:post_t a)
  (f:atomic_repr a uses is_ghost pre post)
  : Pure (atomic_repr a uses is_ghost pre post)
    (requires True)
    (ensures fun _ -> True)
  = f

let if_then_else (a:Type) (uses:Set.set lock_addr) (pre:pre_t) (post:post_t a)
  (f:atomic_repr a uses true pre post)
  (g:atomic_repr a uses true pre post)
  (p:Type0)
  : Type
  = atomic_repr a uses true pre post

reflectable
layered_effect {
  SteelAtomic : a:Type -> uses:Set.set lock_addr -> is_ghost:bool -> pre:pre_t -> post:post_t a
    -> Effect
  with
  repr = atomic_repr;
  return = returnc;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

assume WP_monotonic_pure:
  forall (a:Type) (wp:pure_wp a).
    (forall (p q:pure_post a).
       (forall x. p x ==> q x) ==>
       (wp p ==> wp q))

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
inline_for_extraction
let lift_pure_steel_atomic (a:Type) (uses:Set.set lock_addr) (p:pre_t) (wp:pure_wp a) (f:unit -> PURE a wp)
: Pure (atomic_repr a uses true p (fun _ -> p))
  (requires wp (fun _ -> True))
  (ensures fun _ -> True)
= fun _ -> let x = f () in x
#pop-options

sub_effect PURE ~> SteelAtomic = lift_pure_steel_atomic


// let bind_pure_steel (a:Type) (b:Type)
//   (wp:pure_wp a)
//   (uses:Set.set lock_addr)
//   (is_ghost:bool)
//   (pre_g:pre_t) (post_g:post_t b)
//   (f:unit -> PURE a wp) (g:(x:a -> atomic_repr b uses is_ghost pre_g post_g))
// : atomic_repr b uses is_ghost pre_g post_g
// = admit()


// polymonadic_bind (PURE, SteelAtomic) |> SteelAtomic = bind_pure_steel


effect Mst (a:Type) (req:mem -> Type0) (ens:mem -> a -> mem -> Type0) =
  RMST.RMSTATE a mem mem_evolves req ens

let mst_get ()
  : Mst mem (fun _ -> True) (fun m0 r m1 -> m0 == r /\ r == m1)
  = RMST.get ()

let mst_put (m:mem)
  : Mst unit (fun m0 -> mem_evolves m0 m) (fun _ _ m1 -> m1 == m)
  = RMST.put m

assume val atomic_preserves_preorder
  (#a:Type)
  (#uses:Set.set lock_addr)
  (#is_ghost:bool)
  (#pre:hprop)
  (#post:a -> hprop)
  (act:atomic uses is_ghost pre a post)
  (m0:hmem_with_inv' uses pre)
  : Lemma (
    let (| x, m1 |) = act m0 in
//    Sem.preserves_frame #state pre (post x) m0 m1 /\
    mem_evolves m0 m1
  )


assume
val atomic_noop (uses:Set.set lock_addr) : atomic uses true emp unit (fun _ -> emp)

/// By default, if we demote an m_action, it is not a ghost atomic
/// If we want a ghost atomic, it should be exposed this way in Steel.Actions
val demote_m_action_atomic
    (#a:Type) (#fp:hprop) (#fp':a -> hprop)
    (f : m_action fp a fp')
    : atomic Set.empty false fp a fp'

#push-options "--fuel 0 --ifuel 0"
let demote_m_action_atomic #a #fp #fp' f = f
#pop-options

// TODO: If we expose directly an atomic new_inv, this should probably be considered a ghost action?
// Or maybe it shouldn't be in SteelAtomic at all?
val atomic_new_inv (p:hprop) : atomic Set.empty false p (inv p) (fun _ -> emp)
let atomic_new_inv p = demote_m_action_atomic (new_inv p)

#push-options "--fuel 0 --ifuel 1"
let noop (uses:Set.set lock_addr) : SteelAtomic unit uses true emp (fun _ -> emp)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      let (| x, m1 |) = atomic_noop uses m0 in
      atomic_preserves_preorder (atomic_noop uses) m0;
      mst_put m1)
#pop-options

#push-options "--fuel 0 --ifuel 1"
let new_inv (p:hprop) : SteelAtomic (inv p) Set.empty false p (fun _ -> emp)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      let (| x, m1 |) = atomic_new_inv p m0 in
      atomic_preserves_preorder (atomic_new_inv p) m0;
      mst_put m1;
      x)
#pop-options

#push-options "--fuel 0 --ifuel 1"
let change_hprop
  (#uses:Set.set lock_addr)
  (p q:hprop)
  (proof: (m:mem) -> Lemma (requires interp p m) (ensures interp q m))
  : SteelAtomic unit uses true p (fun _ -> q)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      let (| x, m1 |) = weaken_hprop uses p q proof m0 in
      atomic_preserves_preorder (weaken_hprop uses p q proof) m0;
      mst_put m1;
      x)
#pop-options

module U32 = FStar.UInt32
open Steel.Permissions

#push-options "--fuel 0 --ifuel 1 --z3rlimit 10"
let index
  (#t:_)
  (#uses:Set.set lock_addr)
  (a:array_ref t{not (is_null_array a)})
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  : SteelAtomic t uses false
      (pts_to_array a full_permission iseq)
      (fun _ -> pts_to_array a full_permission iseq)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      let at = (index_array uses a iseq full_permission i) in
      let (| x, m1 |) = at m0 in
      atomic_preserves_preorder at m0;
      mst_put m1;
      x)
#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 10"
let upd
  (#t:_)
  (#uses:Set.set lock_addr)
  (a:array_ref t{not (is_null_array a)})
  (iseq: Ghost.erased (Seq.lseq t (U32.v (length a))))
  (i:U32.t{U32.v i < U32.v (length a)})
  (v:t)
  : SteelAtomic unit uses false
      (pts_to_array a full_permission iseq)
      (fun _ -> pts_to_array a full_permission (Seq.upd iseq (U32.v i) v))
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      let at = (upd_array uses a iseq i v) in
      let (| x, m1 |) = at m0 in
      atomic_preserves_preorder at m0;
      mst_put m1)
#pop-options

assume val steelatomic_reify
  (#a:Type) (#uses:Set.set lock_addr) (#is_ghost:bool) (#pre:pre_t) (#post:post_t a)
  ($f:unit -> SteelAtomic a uses is_ghost pre post)
: atomic_repr a uses is_ghost pre post

// TODO: This should be implemented using with_invariant in Steel.Actions
// But for this, we need a with_invariant that takes directly an atomic_t
// instead of an atomic
let with_invariant0
  (#a:Type) (#fp:hprop) (#fp':a -> hprop) (#uses:Set.set lock_addr) (#is_ghost:bool)
  (#p:hprop)
  (i:inv p{not (i `Set.mem` uses)})
  (f:atomic_repr a (Set.union (Set.singleton i) uses) is_ghost (p `star` fp) (fun x -> p `star` fp' x))
  : SteelAtomic a uses is_ghost fp fp'
  = SteelAtomic?.reflect (fun _ -> admit())

let with_invariant_frame
  (#a:Type) (#fp:hprop) (#fp':a -> hprop) (#uses:Set.set lock_addr) (#is_ghost:bool)
  (#p:hprop)
  (i:inv p{not (i `Set.mem` uses)})
  (f:unit -> SteelAtomic a (Set.union (Set.singleton i) uses) is_ghost (p `star` fp) (fun x -> p `star` fp' x))
  : SteelAtomic a uses is_ghost fp fp'
  = with_invariant0 i (steelatomic_reify f)

assume
val with_invariant
  (#a:Type) (#uses:Set.set lock_addr) (#is_ghost:bool)
  (#p:hprop)
  (i:inv p{not (i `Set.mem` uses)})
  ($f:unit -> SteelAtomic a (Set.union (Set.singleton i) uses) is_ghost p (fun x -> p))
  : SteelAtomic a uses is_ghost emp (fun _ -> emp)

let test
  (#t:_)
  (a:array_ref t{not (is_null_array a) /\ U32.v (length a) == 1})
  (iseq: Ghost.erased (Seq.lseq t 1))
  : SteelAtomic t Set.empty false
      (pts_to_array a full_permission iseq)
      (fun _ -> emp)
  = let i = new_inv  (pts_to_array a full_permission iseq) in
    // TODO: Add a frame function, and only keep with_invariant_frame
    with_invariant i (fun _ -> index a iseq 0ul)
