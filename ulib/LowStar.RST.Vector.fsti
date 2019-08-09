module LowStar.RST.Vector

open LowStar.RST
module A = LowStar.RST.Array
module P = LowStar.RST.Pointer
module U32 = FStar.UInt32
module Perm = LowStar.Permissions

module S = FStar.Seq

val vector (a: Type0) : Tot Type0

noeq type vector_view_t (a: Type0) = {
  v_capacity: U32.t;
  v_arr: S.seq a;
  v_perm: Ghost.erased Perm.permission;
}

val vector_view (#a:Type0)  (v:vector a) : Tot (view (vector_view_t a))

let vector_resource (#a:Type0) (v:vector a) : Tot resource =
   as_resource (vector_view v)

let get_capacity (#a: Type0) (v: vector a) (h: rmem (vector_resource v)): GTot U32.t =
   (h (vector_resource v)).v_capacity

let as_rseq (#a: Type0) (v: vector a) (h: rmem (vector_resource v)): GTot (S.seq a) =
   (h (vector_resource v)).v_arr

let get_perm (#a: Type0) (v: vector a) (h: rmem (vector_resource v)): GTot Perm.permission =
   Ghost.reveal (h (vector_resource v)).v_perm

val create: #a:Type0 -> init:a -> max:UInt32.t{U32.v max > 0} -> RST (vector a)
  empty_resource
  (fun v -> vector_resource v)
  (fun _ -> U32.v max > 0)
  (fun h0 v h1 -> let view = h1 (vector_resource v) in
   as_rseq v h1 `S.equal` S.empty /\
   get_capacity v h1 = max /\
   get_perm v h1 == FStar.Real.one
  )

val push: #a:Type0 -> v:vector a -> x:a -> RST unit
  (vector_resource v)
  (fun _ -> vector_resource v)
  (fun h -> Perm.allows_write (get_perm v h) /\ S.length (as_rseq v h) < UInt.max_int 32)
  (fun h0 _ h1 ->
    let v0 = h0 (vector_resource v)  in
    let v1 = h1 (vector_resource v) in
    v1 == {v0 with v_arr = S.snoc v0.v_arr x}
  )
