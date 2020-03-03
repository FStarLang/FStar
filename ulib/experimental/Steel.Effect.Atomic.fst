module Steel.Effect.Atomic

open Steel.Memory
open Steel.Actions
module Sem = Steel.Semantics.Hoare.MST
open Steel.Semantics.Instantiate

type pre_t = hprop u#1
type post_t (a:Type) = a -> hprop u#1

let state_uses (uses:Set.set lock_addr) : Sem.st = state_obeys_st_laws uses; state0 uses

type atomic_repr (a:Type) (uses:Set.set lock_addr) (is_ghost:bool) (pre:pre_t) (post:post_t a) =
  Sem.action_t #(state_uses uses) pre post (fun _ -> True) (fun _ _ _ -> True)

let return (a:Type u#a) (x:a) (uses:Set.set lock_addr) (p:a -> hprop u#1)
: atomic_repr a uses true (p x) p
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

#set-options "--print_universes --print_implicits"

reflectable
layered_effect {
  SteelAtomic : a:Type -> uses:Set.set lock_addr -> is_ghost:bool -> pre:pre_t -> post:post_t a
    -> Effect
  with
  repr = atomic_repr;
  return = return;
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


// val bind_pure_steel (a:Type) (b:Type)
//   (wp:pure_wp a)
//   (uses:Set.set lock_addr)
//   (is_ghost:bool)
//   (pre_g:pre_t) (post_g:post_t b)
//   (f:unit -> PURE a wp) (g:(x:a -> atomic_repr b uses is_ghost pre_g post_g))
// : atomic_repr b uses is_ghost pre_g post_g


// polymonadic_bind (PURE, SteelAtomic) |> SteelAtomic = bind_pure_steel


effect Mst (a:Type) (req:mem -> Type0) (ens:mem -> a -> mem -> Type0) =
  RMST.RMSTATE a mem mem_evolves req ens

let mst_get ()
  : Mst mem (fun _ -> True) (fun m0 r m1 -> m0 == r /\ r == m1)
  = RMST.get ()

let mst_put (m:mem)
  : Mst unit (fun m0 -> mem_evolves m0 m) (fun _ _ m1 -> m1 == m)
  = RMST.put m

let steel_admit (a:Type) (uses:Set.set lock_addr) (p:hprop) (q:a -> hprop)
  : SteelAtomic a uses true p q
  = SteelAtomic?.reflect (fun _ ->
      let m0 = RMST.rmst_admit() in
      mst_put m0
    )

let steel_assert (uses:Set.set lock_addr) (p:hprop)
  : SteelAtomic unit uses true p (fun _ -> p)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get() in
      mst_put m0
    )

let intro_emp_left (p1 p2:hprop) (m:mem)
: Lemma
  (requires interp (p1 `star` p2) m)
  (ensures interp ((p1 `star` emp) `star` p2) m)
= emp_unit p1;
  equiv_symmetric (p1 `star` emp) p1;
  equiv_extensional_on_star p1 (p1 `star` emp) p2

assume val steelatomic_reify
  (#a:Type) (#uses:Set.set lock_addr) (#is_ghost:bool) (#pre:pre_t) (#post:post_t a)
  ($f:unit -> SteelAtomic a uses is_ghost pre post)
: atomic_repr a uses is_ghost pre post


#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let atomic_preserves_frame_and_preorder
  (#a:Type)
  (#uses:Set.set lock_addr)
  (#is_ghost:bool)
  (#pre:hprop)
  (#post:a -> hprop)
  (act:atomic uses is_ghost pre a post)
  (m0:hmem_with_inv' uses pre)
  : Lemma (
    let (| x, m1 |) = act m0 in
    Sem.preserves_frame #(state_uses uses) pre (post x) m0 m1 /\
    mem_evolves m0 m1
  )
= let (| x, m1 |) = act m0 in
  let frame : hprop = emp in
  intro_emp_left pre (locks_invariant uses m0) m0;
  let m0 : hmem_with_inv' uses (pre `star` emp) = m0 in
  ()
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let frame0 (#a:Type) (#uses:Set.set lock_addr) (#is_ghost:bool) (#pre:pre_t) (#post:post_t a)
  (f:atomic_repr a uses is_ghost pre post)
  (frame:hprop)
: SteelAtomic a
  uses
  is_ghost
  (pre `star` frame)
  (fun x -> post x `star` frame)
= SteelAtomic?.reflect (fun _ -> Sem.run #(state_uses uses) #_ #_ #_ #_ #_ (Sem.Frame (Sem.Act f) frame (fun _ -> True)))
#pop-options

let atomic_frame (#a:Type) (#uses:Set.set lock_addr) (#is_ghost:bool) (#pre:pre_t) (#post:post_t a)
  (frame:hprop)
  ($f:unit -> SteelAtomic a uses is_ghost pre post)
: SteelAtomic a
  uses
  is_ghost
  (pre `star` frame)
  (fun x -> post x `star` frame)
= frame0 (steelatomic_reify f) frame

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
let new_inv (p:hprop) : SteelAtomic (inv p) Set.empty false p (fun _ -> emp)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      let (| x, m1 |) = atomic_new_inv p m0 in
      atomic_preserves_frame_and_preorder (atomic_new_inv p) m0;
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
      atomic_preserves_frame_and_preorder (weaken_hprop uses p q proof) m0;
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
      (pts_to_array a full_perm iseq)
      (fun _ -> pts_to_array a full_perm iseq)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      let at = (index_array uses a iseq full_perm i) in
      let (| x, m1 |) = at m0 in
      atomic_preserves_frame_and_preorder at m0;
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
      (pts_to_array a full_perm iseq)
      (fun _ -> pts_to_array a full_perm (Seq.upd iseq (U32.v i) v))
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      let at = (upd_array uses a iseq i v) in
      let (| x, m1 |) = at m0 in
      atomic_preserves_frame_and_preorder at m0;
      mst_put m1)
#pop-options

module U = FStar.Universe

#push-options "--fuel 0 --ifuel 1 --z3rlimit 30"
let cas
  (#t:eqtype)
  (#uses:Set.set lock_addr)
  (r:reference (U.raise_t u#0 u#1 t) (trivial_preorder (U.raise_t u#0 u#1 t)))
  (v:Ghost.erased t)
  (v_old:t)
  (v_new:t)
  : SteelAtomic
    (b:bool{b <==> (Ghost.reveal v == v_old)})
    uses
    false
    (pts_to_ref r full_perm (U.raise_val (Ghost.reveal v)))
    (fun b -> if b then
      pts_to_ref r full_perm (U.raise_val v_new)
    else
      pts_to_ref r full_perm (U.raise_val (Ghost.reveal v))
    )
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      let at = cas uses r v v_old v_new in
      let (| x, m1 |) = at m0 in
      atomic_preserves_frame_and_preorder at m0;
      mst_put m1;
      x)
#pop-options


#push-options "--fuel 0 --ifuel 1"
let lemma_sem_preserves (#p:hprop) (fp fp':hprop)
  (m0 m1:mem) (uses:Set.set lock_addr)
  (i:inv p{not (i `Set.mem` uses) /\ inv_ok i m0 /\ inv_ok i m1})
  : Lemma
   (requires Sem.preserves_frame #(state_uses (Set.union (Set.singleton i) uses))
     (p `star` fp) (p `star` fp') m0 m1)
   (ensures Sem.preserves_frame #(state_uses uses) fp fp' m0 m1)
  = let s = Set.union (Set.singleton i) uses in
    let aux (frame:hprop) : Lemma
      (requires interp ((fp `star` frame) `star` locks_invariant uses m0) m0)
      (ensures interp ((fp' `star` frame) `star` locks_invariant uses m1) m1 /\
               (forall (f_frame:Sem.fp_prop #(state_uses uses) frame). f_frame (core_mem m0) == f_frame (core_mem m1)))
      = interp_inv_unused i uses (fp `star` frame) m0;
        assert (interp ((p `star` (fp `star` frame)) `star` locks_invariant s m0) m0);
        let rewrite_4 (p1 p2 p3 p4:hprop) : Lemma
          (((p1 `star` (p2 `star` p3)) `star` p4) `equiv` (((p1 `star` p2) `star` p3) `star` p4))
          = star_associative p1 p2 p3;
            star_congruence (p1 `star` (p2 `star` p3)) p4 ((p1 `star` p2) `star` p3) p4
        in rewrite_4 p fp frame (locks_invariant s m0);
        assert (interp (((p `star` fp) `star` frame) `star` locks_invariant s m0) m0);
        assert (interp (((p `star` fp') `star` frame) `star` locks_invariant s m1) m1);
        rewrite_4 p fp' frame (locks_invariant s m1);
        interp_inv_unused i uses (fp' `star` frame) m1;
        assert (interp ((fp' `star` frame) `star` locks_invariant uses m1) m1);
        let aux' (f_frame:Sem.fp_prop #(state_uses uses) frame)
          : Lemma (f_frame (core_mem m0) == f_frame (core_mem m1))
          = let f':Sem.fp_prop #(state_uses s) frame = f_frame in
            assert (forall (f_frame':Sem.fp_prop #(state_uses s) frame).
              f_frame' (core_mem m0) == f_frame' (core_mem m1));
            assert (f' (core_mem m0) == f' (core_mem m1))
        in Classical.forall_intro aux'
    in Classical.forall_intro (Classical.move_requires aux)
#pop-options

#push-options "--fuel 0 --ifuel 1"
let with_invariant_aux
  (#a:Type) (#fp:hprop) (#fp':a -> hprop) (#uses:Set.set lock_addr) (#is_ghost:bool)
  (#p:hprop)
  (i:inv p{not (i `Set.mem` uses)})
  (f:atomic_repr a (Set.union (Set.singleton i) uses) is_ghost (p `star` fp) (fun x -> p `star` fp' x))
  : atomic_repr a uses is_ghost fp fp'
  = fun _ ->
      let m0 = RMST.get() in
      assume (inv_ok i m0);
      let s = Set.union (Set.singleton i) uses in
      interp_inv_unused i uses fp m0;
      let x = f () in
      let m1 = RMST.get() in
      assume (inv_ok i m1);
      interp_inv_unused i uses (fp' x) m1;
      lemma_sem_preserves fp (fp' x) m0 m1 uses i;
      x
#pop-options

let with_invariant0
  (#a:Type) (#fp:hprop) (#fp':a -> hprop) (#uses:Set.set lock_addr) (#is_ghost:bool)
  (#p:hprop)
  (i:inv p{not (i `Set.mem` uses)})
  (f:atomic_repr a (Set.union (Set.singleton i) uses) is_ghost (p `star` fp) (fun x -> p `star` fp' x))
  : SteelAtomic a uses is_ghost fp fp'
  = SteelAtomic?.reflect (with_invariant_aux i f)

let with_invariant_frame
  (#a:Type) (#fp:hprop) (#fp':a -> hprop) (#uses:Set.set lock_addr) (#is_ghost:bool)
  (#p:hprop)
  (i:inv p{not (i `Set.mem` uses)})
  (f:unit -> SteelAtomic a (Set.union (Set.singleton i) uses) is_ghost (p `star` fp) (fun x -> p `star` fp' x))
  : SteelAtomic a uses is_ghost fp fp'
  = with_invariant0 i (steelatomic_reify f)
