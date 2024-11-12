module PulseCore.IndirectionTheoryActions
module F = FStar.FunctionalExtensionality
module T = FStar.Tactics
module PM = PulseCore.MemoryAlt
module HST = PulseCore.HoareStateMonad
open PulseCore.IndirectionTheorySep

type action_kind =
| GHOST
| ATOMIC

let maybe_ghost_action (k:action_kind) (m0 m1:mem) = GHOST? k ==> is_ghost_action m0 m1

let _ACTION 
  (a:Type u#a)
  (ak:action_kind)
  (except:inames)
  (expects:slprop)
  (provides: a -> GTot slprop)
  (frame:slprop)
= HST.st #full_mem a
    (requires fun m0 ->
        inames_ok except m0 /\
        interp (expects `star` frame `star` mem_invariant except m0) m0)
    (ensures fun m0 x m1 ->
        maybe_ghost_action ak m0 m1 /\
        inames_ok except m1 /\
        interp (provides x `star` frame `star` mem_invariant except m1) m1 )

let _act_except 
    (a:Type u#a)
    (ak:action_kind)
    (except:inames)
    (expects:slprop)
    (provides: a -> GTot slprop)
 : Type u#(max a 4) 
 = frame:slprop -> _ACTION a ak except expects provides frame
let ghost_act a = _act_except a GHOST
let act a = _act_except a ATOMIC
let buy_act a = _act_except a ATOMIC

val lift_mem_action #a #mg #ex #pre #post
                   (_:PM._pst_action_except a mg (lower_inames ex) pre post)
: _act_except a (if mg then GHOST else ATOMIC) ex (lift pre) (fun x -> lift (post x))


val later_intro (e:inames) (p:slprop) 
: ghost_act unit e p (fun _ -> later p)

val later_elim (e:inames) (p:slprop) 
: ghost_act unit e (later p `star` later_credit 1) (fun _ -> p)

val buy (e:inames) (n:FStar.Ghost.erased nat)
: buy_act (FStar.Ghost.erased bool) e emp (fun b -> if b then later_credit n else emp)

val dup_inv (e:inames) (i:iref) (p:slprop)
: ghost_act unit e 
    (inv i p) 
    (fun _ -> inv i p `star` inv i p)

val fresh_invariant (e:inames) (p:slprop) (ctx:inames)
: ghost_act
   (i:iref{~(GhostSet.mem i ctx)})
   e
   (p `star` inames_live ctx)
   (fun i -> inv i p `star` inames_live ctx)

val new_invariant (e:inames) (p:slprop)
: ghost_act iref e p (fun i -> inv i p)

val inames_live_inv (e:inames) (i:iref) (p:slprop)
: ghost_act unit e (inv i p) (fun _ -> inv i p `star` inames_live (single i))

val with_invariant (#a:Type)
                   (#fp:slprop)
                   (#fp':a -> slprop)
                   (#opened_invariants:inames)
                   (#p:slprop)
                   (#ak:action_kind)
                   (i:iref{not (mem_inv opened_invariants i)})
                   (f:_act_except a ak
                        (add_inv opened_invariants i) 
                        (later p `star` fp)
                        (fun x -> later p `star` fp' x))
: _act_except a ak opened_invariants 
      (inv i p `star` fp)
      (fun x -> inv i p `star` fp' x)

val invariant_name_identifies_invariant  (e:inames) (i: iref) (p q: slprop)
: ghost_act unit e 
     (inv i p `star` inv i q)
     (fun _ -> inv i p `star` inv i q `star` later (equiv p q))

val frame (#a:Type)
          (#ak:action_kind)
          (#opened_invariants:inames)
          (#pre:slprop)
          (#post:a -> slprop)
          (frame:slprop)
          ($f:_act_except a ak opened_invariants pre post)
: _act_except a ak opened_invariants (pre `star` frame) (fun x -> post x `star` frame)

open FStar.Ghost
module U = FStar.Universe
val witness_exists (#opened_invariants:_) (#a:_) (p:a -> slprop)
: ghost_act (erased a) opened_invariants
           (op_exists_Star p)
           (fun x -> p x)

val intro_exists (#opened_invariants:_) (#a:_) (p:a -> slprop) (x:erased a)
: ghost_act unit opened_invariants
  (p x)
  (fun _ -> op_exists_Star p)

val raise_exists (#opened_invariants:_) (#a:Type u#a) (p:a -> slprop)
: ghost_act unit opened_invariants
    (op_exists_Star p)
    (fun _a -> op_exists_Star #(U.raise_t u#a u#b a) (U.lift_dom u#a u#_ u#b p))

val elim_pure (#opened_invariants:_) (p:prop)
: ghost_act (u:unit{p}) opened_invariants (pure p) (fun _ -> emp)

val intro_pure (#opened_invariants:_) (p:prop) (_:squash p)
: ghost_act unit opened_invariants emp (fun _ -> pure p)

val drop (#opened_invariants:_) (p:slprop)
: ghost_act unit opened_invariants p (fun _ -> emp)

val lift_ghost
      (#a:Type)
      #opened_invariants #p #q
      (ni_a:PulseCore.HeapSig.non_info a)
      (f:erased (ghost_act a opened_invariants p q))
: ghost_act a opened_invariants p q

val equiv_refl #opened_invariants (a:slprop)
: ghost_act unit opened_invariants emp (fun _ -> equiv a a)

val equiv_dup #opened_invariants (a b:slprop)
: ghost_act unit opened_invariants (equiv a b) (fun _ -> equiv a b `star` equiv a b)

val equiv_trans #opened_invariants (a b c:slprop)
: ghost_act unit opened_invariants (equiv a b `star` equiv b c) (fun _ -> equiv a c)

val equiv_elim #opened_invariants (a b:slprop)
: ghost_act unit opened_invariants (a `star` equiv a b) (fun _ -> b)

val slprop_ref_alloc #o (y: slprop)
: ghost_act slprop_ref o emp fun x -> slprop_ref_pts_to x y

val slprop_ref_share #o (x:slprop_ref) (y:slprop)
: ghost_act unit o (slprop_ref_pts_to x y) fun _ -> slprop_ref_pts_to x y `star` slprop_ref_pts_to x y

val slprop_ref_gather #o (x:slprop_ref) (y1 y2: slprop)
: ghost_act unit o (slprop_ref_pts_to x y1 `star` slprop_ref_pts_to x y2) fun _ -> slprop_ref_pts_to x y1 `star` later (equiv y1 y2)
