module Pulse.Lib.Vec

open Pulse.Lib.Core

module A = Pulse.Lib.Array.Core

type vec a = A.array a
let length v = A.length v
let is_full_vec v = A.is_full_array v
let pts_to v #p s = A.pts_to v #p s
let pts_to_len v = A.pts_to_len v
let alloc x n = A.alloc x n
let op_Array_Access v i = A.op_Array_Access v i
let op_Array_Assignment v i x = A.op_Array_Assignment v i x
let free v = A.free v

let vec_to_array v = v
let to_array_pts_to v #p #s =
  rewrite (pts_to v #p s)
          (A.pts_to (vec_to_array v) #p s)
          (vprop_equiv_refl _)
let to_vec_pts_to v #p #s =
  rewrite (A.pts_to (vec_to_array v) #p s)
          (pts_to v #p s)
          (vprop_equiv_refl _)
