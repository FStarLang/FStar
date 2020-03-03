module Steel.Reference

open Steel.Effect
open Steel.Effect.Atomic
open Steel.Memory
open FStar.Ghost
module U = FStar.Universe
module A = Steel.Actions

#set-options "--print_universes --print_implicits"

let perm = p:perm{readable p}
let full : perm = full_perm
let trivial_preorder #a : Preorder.preorder a = fun _ _ -> True
let ref (a:Type u#0) = reference (U.raise_t u#0 u#1 a) (Steel.HigherReference.trivial_preorder)
let ref_pre (a: Type u#0) (pre: Preorder.preorder a) = reference (U.raise_t u#0 u#1 a) (A.raise_preorder pre)
let is_ref (#a:Type u#0) (r:ref a) (p:perm) : hprop u#1 = ref_perm r p
let pts_to (#a:Type u#0) (r:ref a) (p:perm) (v:erased a) : hprop u#1 =
  pts_to_ref r p (U.raise_val (reveal v))
let pts_to_pre (#a:Type u#0) (#pre: Preorder.preorder a) (r:ref_pre a pre) (p:perm) (v:erased a) : hprop u#1 =
  pts_to_ref r p (U.raise_val (reveal v))
let h_exists (#a:Type u#0) (f: (a -> hprop u#1)) : hprop u#1 =
  h_exists #(U.raise_t u#0 u#1 a) (fun x -> f (U.downgrade_val x))


val alloc (#a:Type0) (x:a)
  : SteelT (ref a) emp (fun r -> pts_to r full x)

val read (#a:Type0) (#p:perm) (#v:erased a) (r:ref a)
  : SteelT a (pts_to r p v) (fun x -> pts_to r p x)

val read_refine (#a:Type0) (#p:perm) (q:a -> hprop) (r:ref a)
  : SteelT a (h_exists (fun (v:a) -> pts_to r p v `star` q v))
             (fun v -> pts_to r p v `star` q v)

val write (#a:Type0) (#v:erased a) (r:ref a) (x:a)
  : SteelT unit (pts_to r full v) (fun _ -> pts_to r full x)

val free (#a:Type0) (#v:erased a) (r:ref a)
  : SteelT unit (pts_to r full v) (fun _ -> emp)

val share (#a:Type0) (#p:perm) (#v:erased a) (r:ref a)
  : SteelT unit
    (pts_to r p v)
    (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)

val gather (#a:Type0) (#p0:perm) (#p1:perm) (#v0 #v1:erased a) (r:ref a)
  : SteelT unit
    (pts_to r p0 v0 `star` pts_to r p1 v1)
    (fun _ -> pts_to r (sum_perm p0 p1) v0)

val ghost_read (#a:Type0) (#uses:Set.set lock_addr) (#p:perm) (#v:Ghost.erased a) (r:ref a)
  : SteelAtomic a uses true
    (pts_to r p v)
    (fun x -> pts_to r p x)

val ghost_read_refine (#a:Type0) (#uses:Set.set lock_addr) (#p:perm) (r:ref a)
  (q:a -> hprop)
  : SteelAtomic a uses true
    (h_exists (fun (v:a) -> pts_to r p v `star` q v))
    (fun v -> pts_to r p v `star` q v)

module U = FStar.Universe

val cas
  (#t:eqtype)
  (#uses:Set.set lock_addr)
  (r:ref t)
  (v:Ghost.erased t)
  (v_old:t)
  (v_new:t)
  : SteelAtomic
    (b:bool{b <==> (Ghost.reveal v == v_old)})
    uses
    false
    (pts_to r full_perm v)
    (fun b -> if b then pts_to r full_perm v_new else pts_to r full_perm v)

////////////////////////////////////////////////////////////////////////////////

val alloc_monotonic_ref (#a:Type0) (p:Preorder.preorder a) (v:a)
  : SteelT (ref_pre a p) emp (fun r -> pts_to_pre r full v)

val read_monotonic_ref
  (#a:Type0)
  (#q:perm)
  (#p:Preorder.preorder a)
  (#frame:a -> hprop)
  (r:ref_pre a p)
  : SteelT a (h_exists (fun (v:a) ->
                pts_to_pre r q v `star` frame v))
             (fun v -> pts_to_pre r q v `star` frame v)

val write_monotonic_ref
  (#a:Type0)
  (#p:Preorder.preorder a)
  (#v:erased a)
  (r:ref_pre a p)
  (x:a{p v x})
  : SteelT unit
    (pts_to_pre r full v)
    (fun v -> pts_to_pre r full x)

val pure (p:prop) : hprop

let property (a:Type) = a -> prop

val witnessed
  (#a:Type0)
  (#p:Preorder.preorder a)
  (r:ref_pre a p)
  (fact:property a) : prop

let stable_property (#a:Type0) (p:Preorder.preorder a) = fact:property a { Preorder.stable fact p }

val witness
  (#a:Type0)
  (#q:perm)
  (#p:Preorder.preorder a)
  (r:ref_pre a p)
  (fact:stable_property p)
  (v:(Ghost.erased a))
  (_:squash (fact v))
  : SteelT unit
    (pts_to_pre r q v)
    (fun _ -> pts_to_pre r q v `star` pure (witnessed r fact))

val recall (#a:Type0) (#q:perm) (#p:Preorder.preorder a) (#fact:property a)
           (r:ref_pre a p) (v:(Ghost.erased a))
  : SteelT unit (pts_to_pre r q v `star` pure (witnessed r fact))
                (fun _ -> pts_to_pre r q v `star` pure (fact v))
