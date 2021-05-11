module Steel.SelDisposableInvariant

open FStar.Ghost
open Steel.Memory
open Steel.SelEffect.Atomic
open Steel.SelEffect
open Steel.FractionalPermission

#push-options "--ide_id_info_off"

[@@ erasable]
val inv (p:vprop) : Type0

val name (#p:_) (i:inv p) : Ghost.erased iname

val active (#p:_) ([@@@ smt_fallback] f:perm) (_:inv p) : vprop

val new_inv (#u:_) (p:vprop)
  : SteelSelGhostT (inv p) u
    p
    (fun i -> active full_perm i)

val share (#p:vprop) (#f:perm) (#u:_) (i:inv p)
  : SteelSelGhostT unit u
    (active f i)
    (fun _ -> active (half_perm f) i `star` active (half_perm f) i)

val gather (#p:vprop) (#f0 #f1:perm) (#u:_) (i:inv p)
  : SteelSelGhostT unit u
    (active f0 i `star` active f1 i)
    (fun _ -> active (sum_perm f0 f1) i)

let mem_inv (#p:vprop) (u:inames) (i:inv p) : GTot bool =
  Set.mem (reveal (name i)) (reveal u)

let add_inv (#p:vprop) (u:inames) (i:inv p) : inames =
  Set.union (Set.singleton (reveal (name i))) (reveal u)

val dispose (#p:vprop) (#u:inames) (i:inv p{not (mem_inv u i)})
  : SteelSelGhostT unit u
    (active full_perm i)
    (fun _ -> p)

val with_invariant (#a:Type)
                   (#fp:vprop)
                   (#fp':a -> vprop)
                   (#opened_invariants:inames)
                   (#p:vprop)
                   (#perm:_)
                   (i:inv p{not (mem_inv opened_invariants i)})
                   ($f:unit -> SteelSelAtomicT a (add_inv opened_invariants i)
                                             (p `star` fp)
                                             (fun x -> p `star` fp' x))
  : SteelSelAtomicT a opened_invariants (active perm i `star` fp) (fun x -> active perm i `star` fp' x)


val with_invariant_g (#a:Type)
                     (#fp:vprop)
                     (#fp':a -> vprop)
                     (#opened_invariants:inames)
                     (#p:vprop)
                     (#perm:_)
                     (i:inv p{not (mem_inv opened_invariants i)})
                     ($f:unit -> SteelSelGhostT a (add_inv opened_invariants i)
                                               (p `star` fp)
                                               (fun x -> p `star` fp' x))
  : SteelSelGhostT a opened_invariants (active perm i `star` fp) (fun x -> active perm i `star` fp' x)
