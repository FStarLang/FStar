module Steel.DisposableInvariant
open Steel.Effect
open Steel.Memory
open Steel.FractionalPermission
open Steel.Effect.Atomic
#push-options "--ide_id_info_off"

val inv (p:slprop u#1) : Type0

val name (#p:_) (i:inv p) : iname

val active (#p:_) ([@@@ smt_fallback] f:perm) (_:inv p) : slprop u#1

val new_inv (#u:_) (p:slprop)
  : SteelGhostT (inv p) u
    p
    (fun i -> active full_perm i)

val share (#p:slprop) (#f:perm) (#u:_) (i:inv p)
  : SteelGhostT unit u
    (active f i)
    (fun _ -> active (half_perm f) i `star` active (half_perm f) i)

val gather (#p:slprop) (#f0 #f1:perm) (#u:_) (i:inv p)
  : SteelGhostT unit u
    (active f0 i `star` active f1 i)
    (fun _ -> active (sum_perm f0 f1) i)

val dispose (#p:slprop) (#u:_) (i:inv p{not (name i `Set.mem` u)})
  : SteelGhostT unit u
    (active full_perm i)
    (fun _ -> p)

val with_invariant (#a:Type)
                   (#fp:slprop)
                   (#fp':a -> slprop)
                   (#opened_invariants:inames)
                   (#p:slprop)
                   (#perm:_)
                   (i:inv p{not (name i `Set.mem` opened_invariants)})
                   ($f:unit -> SteelAtomicT a (set_add (name i) opened_invariants)
                                             (p `star` fp)
                                             (fun x -> p `star` fp' x))
  : SteelAtomicT a opened_invariants (active perm i `star` fp) (fun x -> active perm i `star` fp' x)


val with_invariant_g (#a:Type)
                     (#fp:slprop)
                     (#fp':a -> slprop)
                     (#opened_invariants:inames)
                     (#p:slprop)
                     (#perm:_)
                     (i:inv p{not (name i `Set.mem` opened_invariants)})
                     ($f:unit -> SteelGhostT a (set_add (name i) opened_invariants)
                                               (p `star` fp)
                                               (fun x -> p `star` fp' x))
  : SteelGhostT a opened_invariants (active perm i `star` fp) (fun x -> active perm i `star` fp' x)
