module LowStar.Array

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open FStar.HyperStack.ST
module U32 = FStar.UInt32
module P = LowStar.Permissions

include LowStar.Array.Defs
include LowStar.Array.Modifies

(*** Stateful operations implementing the ghost specifications ***)


val index (#a:Type) (b:array a) (i:U32.t{U32.v i < vlength b})
  : Stack a (requires fun h -> live h b)
            (ensures fun h0 y h1 -> h0 == h1 /\ y == get h0 b (U32.v i))

val upd (#a:Type) (b:array a) (i:U32.t{U32.v i < vlength b}) (v:a) : Stack unit
  (requires fun h -> writeable_cell h b (U32.v i) /\ live h b)
  (ensures fun h0 _ h1 ->  writeable_cell h1 b (U32.v i) /\
    modifies (loc_array b) h0 h1 /\
    as_seq h1 b == Seq.upd (as_seq h0 b) (U32.v i) v /\
    as_perm_seq h1 b == as_perm_seq h0 b
  )

val alloc (#a:Type0) (init:a) (len:U32.t)
  : ST (array a)
       (requires fun _ -> U32.v len > 0)
       (ensures fun h0 b h1 ->
         modifies loc_none h0 h1 /\
         fresh_loc (loc_array b) h0 h1 /\
         writeable h1 b /\
         freeable b /\
         as_seq h1 b == Seq.create (U32.v len) init)

val free (#a: Type) (b: array a) : HST.ST unit
  (requires (fun h0 -> writeable h0 b /\ live  h0 b /\ freeable b))
  (ensures (fun h0 _ h1 ->
    Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\
    (HS.get_tip h1) == (HS.get_tip h0) /\
    modifies (loc_array b) h0 h1 /\
    HS.live_region h1 (frameOf b)
  ))

val share (#a:Type0) (b:array a) : Stack (array a)
  (requires fun h0 -> live h0 b /\ vlength b > 0)
  (ensures fun h0 b' h1 ->
    modifies (loc_array b) h0 h1 /\
    live h1 b /\ live h1 b' /\
    loc_disjoint (loc_array b) (loc_array b') /\
    as_seq h0 b == as_seq h1 b /\ // The values of the initial array are not modified
    as_seq h1 b' == as_seq h1 b /\ // The values of the new array are the same as the initial array
    mergeable b b' /\
    fresh_loc (loc_array b') h0 h1 /\
    (forall (i:nat{i < vlength b}). {:pattern get_perm h1 b' i \/ get_perm h1 b i } // The permission gets split in two
      get_perm h1 b' i == P.half_permission (get_perm h0 b i) /\
      get_perm h1 b i == P.half_permission (get_perm h0 b i)
    ))

val merge:
  #a: Type ->
  b: array a ->
  b1: array a ->
  Stack unit (requires (fun h0 ->
    mergeable b b1 /\
    live h0 b /\ live h0 b1 /\
    (forall (i:nat{i < vlength b}). summable_permissions h0 b b1  )
  ))
  (ensures (fun h0 _ h1 ->
    live h1 b /\ (forall (i:nat{i < vlength b}). {:pattern (get_perm h1 b i)} // Permissions are summed into the first array
      get_perm h1 b i =  P.sum_permissions (get_perm h0 b i) (get_perm h0 b1 i)
    ) /\
    as_seq h1 b == as_seq h0 b /\ // The value of the array are not modifies
    modifies (loc_array b `loc_union` loc_array b1) h0 h1
  ))

val move:
  #a: Type ->
  b: array a ->
  Stack (array a) (requires (fun h0 ->
    live h0 b
  )) (ensures (fun h0 b' h1 ->
    live h1 b' /\ mergeable b b' /\ modifies (loc_array b) h0 h1 /\
    loc_disjoint (loc_array b) (loc_array b') /\
    fresh_loc (loc_array b') h0 h1 /\
    (freeable b ==> freeable b') /\
    (forall (b1: array a{mergeable b b1}). {:pattern mergeable b' b1} mergeable b b1) /\
    as_seq h0 b == as_seq h1 b' /\
    as_perm_seq h0 b == as_perm_seq h1 b'
  ))

val split:
  #a: Type ->
  b: array a ->
  idx: U32.t{ U32.v idx > 0 /\ U32.v idx < vlength b} ->
  Stack (array a & array a) (requires (fun h0 ->
    live h0 b
  )) (ensures (fun h0 (b1, b2) h1 ->
    glueable b1 b2 /\ live h1 b1 /\ live h1 b2 /\
    modifies (loc_array b) h0 h1 /\
    fresh_loc (loc_array b1) h0 h1 /\ fresh_loc (loc_array b2) h0 h1 /\
    loc_disjoint (loc_array b1) (loc_array b2) /\
    as_seq h0 b == Seq.append (as_seq h1 b1) (as_seq h1 b2) /\
    as_perm_seq h0 b == Seq.append (as_perm_seq h1 b1) (as_perm_seq h1 b2)
  ))

val glue:
  #a: Type ->
  b1: array a ->
  b2: array a ->
  Stack (array a)
    (requires (fun h0 ->
      live h0 b1 /\ live h0 b2 /\ glueable b1 b2
    )) (ensures (fun h0 b h1 ->
      live h1 b /\
      modifies (loc_array b1 `loc_union` loc_array b2) h0 h1 /\
      as_seq h1 b == Seq.append (as_seq h0 b1) (as_seq h0 b2) /\
      as_perm_seq h1 b == Seq.append (as_perm_seq h0 b1) (as_perm_seq h0 b2) /\
      fresh_loc (loc_array b) h0 h1
    ))
