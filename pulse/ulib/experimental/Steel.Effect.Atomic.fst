module Steel.Effect.Atomic

open Steel.Memory
open Steel.Actions
module Sem = Steel.Semantics.Hoare.MST
open Steel.Semantics.Instantiate

type pre_t = hprop
type post_t (a:Type) = a -> hprop

// TODO: Add pre/postconditions
// TODO: Add nat index
let atomic_t (#a:Type) (uses:Set.set lock_addr) (pre:pre_t) (post:post_t a) =
  unit ->
  Sem.Mst a #state
  (requires fun m0 ->
    interp (pre `star` locks_invariant uses m0) m0)
  (ensures fun m0 x m1 ->
    interp ((post x) `star` locks_invariant uses m1) m1)
//    Sem.preserves_frame pre (post x) m0 m1)

type atomic_repr (a:Type) (uses:Set.set lock_addr) (pre:pre_t) (post:post_t a) =
  atomic_t uses pre post

let returnc (a:Type u#a) (x:a) : atomic_repr a Set.empty emp (fun _ -> emp)
  = fun _ -> x

let bind (a:Type) (b:Type) (uses:Set.set lock_addr)
  (pre_f:pre_t) (post_f:post_t a) (post_g:post_t b)
  (f:atomic_repr a uses pre_f post_f) (g:(x:a -> atomic_repr b uses (post_f x) post_g))
  : atomic_repr b uses pre_f post_g
  = fun m0 ->
    let x = f () in
    g x ()

let subcomp (a:Type) (uses:Set.set lock_addr) (pre:pre_t) (post:post_t a)
  (f:atomic_repr a uses pre post)
  : Pure (atomic_repr a uses pre post)
    (requires True)
    (ensures fun _ -> True)
  = f

let if_then_else (a:Type) (uses:Set.set lock_addr) (pre:pre_t) (post:post_t a)
  (f:atomic_repr a uses pre post)
  (g:atomic_repr a uses pre post)
  (p:Type0)
  : Type
  = atomic_repr a uses pre post

reflectable
layered_effect {
  SteelAtomic : a:Type -> uses:Set.set lock_addr -> pre:pre_t -> post:post_t a -> Effect
  with
  repr = atomic_repr;
  return = returnc;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

effect Mst (a:Type) (req:mem -> Type0) (ens:mem -> a -> mem -> Type0) =
  MST.MSTATE a mem mem_evolves req ens

let mst_get ()
  : Mst mem (fun _ -> True) (fun m0 r m1 -> m0 == r /\ r == m1)
  = MST.get ()

let mst_put (m:mem)
  : Mst unit (fun m0 -> mem_evolves m0 m) (fun _ _ m1 -> m1 == m)
  = MST.put m

assume val atomic_preserves_preorder
  (#a:Type)
  (#uses:Set.set lock_addr)
  (#pre:hprop)
  (#post:a -> hprop)
  (act:atomic uses pre a post)
  (m0:hmem_with_inv' uses pre)
  : Lemma (
    let (| x, m1 |) = act m0 in
//    Sem.preserves_frame #state pre (post x) m0 m1 /\
    mem_evolves m0 m1
  )


assume
val atomic_noop (uses:Set.set lock_addr) : atomic uses emp unit (fun _ -> emp)


#push-options "--fuel 0 --ifuel 1"
let noop (uses:Set.set lock_addr) : SteelAtomic unit uses emp (fun _ -> emp)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      let (| x, m1 |) = atomic_noop uses m0 in
      atomic_preserves_preorder (atomic_noop uses) m0;
      mst_put m1)
#pop-options
