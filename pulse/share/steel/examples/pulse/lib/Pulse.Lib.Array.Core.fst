module Pulse.Lib.Array.Core
open Pulse.Lib.Core
open Steel.FractionalPermission
open FStar.Ghost
module SZ = FStar.SizeT
module Seq = FStar.Seq
module A = Steel.ST.Array
module S = Steel.ST.Util
friend Pulse.Lib.Core

let array = A.array
let length = A.length
let is_full_array = A.is_full_array

[@@"__reduce__"; "__steel_reduce__"]
let pts_to #a (r:array a) (#[exact (`full_perm)] p:perm) (v:FStar.Seq.seq a) = A.pts_to r p v

let alloc' (#elt:Type) (x:elt) (n:SZ.t)
  : stt (array elt) 
        (requires S.emp)
        (ensures fun a ->
            A.pts_to a (Seq.create (SZ.v n) x) `S.star`
            S.pure (A.length a == SZ.v n /\ A.is_full_array a))
  = fun _ -> 
        let v = A.alloc #elt x n in
        S.return v
let alloc = alloc'

let index
        (#t: Type)
        (a: array t)
        (i: SZ.t)
        (#p: perm)
        (#s: Ghost.erased (Seq.seq t){SZ.v i < Seq.length s})
  : stt t
        (requires
            pts_to a #p s)
        (ensures fun res ->
            pts_to a #p s `S.star`
            S.pure (res == Seq.index s (SZ.v i)))
  = fun _ -> 
        let v = A.read #t a i in
        S.return v
let op_Array_Access = index

let op_Array_Assignment #t a i v #s =
    fun _ -> A.write #t a i v; ()

let free'
        (#elt: Type)
        (a: array elt)
        (#s: Ghost.erased (Seq.seq elt))
  : stt unit
        (requires
            A.pts_to a s `S.star`
            S.pure (is_full_array a))
        (ensures fun _ ->
            S.emp)
   = fun _ ->
        S.intro_exists_erased s (A.pts_to a);
        S.elim_pure (is_full_array a);
        A.free a; ()
let free = free'
    
