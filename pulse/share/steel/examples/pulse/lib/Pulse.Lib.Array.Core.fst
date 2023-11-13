module Pulse.Lib.Array.Core
open Steel.ST.Util
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
let pts_to_len (#t:Type0) (a:array t) (#p:perm) (#x:Seq.seq t) = admit()

let alloc' (#elt:Type) (x:elt) (n:SZ.t)
  : stt (array elt) 
        (requires S.emp)
        (ensures fun a ->
            A.pts_to a full_perm (Seq.create (SZ.v n) x) `S.star`
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
            A.pts_to a full_perm s `S.star`
            S.pure (is_full_array a))
        (ensures fun _ ->
            S.emp)
   = fun _ ->
        S.intro_exists_erased s (A.pts_to a full_perm);
        S.elim_pure (is_full_array a);
        A.free a; ()
let free = free'
    
//[@@"__reduce__"; "__steel_reduce__"]
let pts_to_range #a (r:array a) (i j: nat) (#[exact (`full_perm)] p:perm) (v:FStar.Seq.seq a) = A.pts_to_range r i j p v

let pts_to_range_intro
  #elt a p s
= fun _ -> A.pts_to_range_intro a p s

let pts_to_range_elim
  #elt a p s
= fun _ -> A.pts_to_range_elim a p s

let pts_to_range_split
  #elt a i m j #p #s
= admit()
(*
= fun _ ->
    let _ = elim_pure _ in
    A.pts_to_range_split a i m j;
    noop ()
    *)

let pts_to_range_join
  a i m j #p #s1 #s2
= admit()
(*
= fun _ ->
    A.pts_to_range_join a i m j;
    noop ()
*)

let pts_to_range_index
  a i #l #r #s #p
= admit()
(*
= fun _ ->
    let res = A.pts_to_range_index a l i r in
    return res
*)

let pts_to_range_upd
  a i v #l #r
= admit()
(*
= fun _ ->
    let _ = A.pts_to_range_upd a l i r v in
    noop ()
*)

assume val admits (#a:Type) (#p:vprop) (#q:a -> vprop) (_:unit)
  : S.STF a p q True (fun _ -> False)

#set-options "--print_implicits"
let with_local'
  (#a:Type0)
  (init:a)
  (len:SZ.t)
  (#pre:vprop)
  (ret_t:Type)
  (#post:ret_t -> vprop)
  (body:(arr:array a) -> stt ret_t (pre `S.star`
                                    (pts_to arr (Seq.create (SZ.v len) init) `S.star`
                                     (pure (is_full_array arr) `S.star`
                                      pure (length arr == SZ.v len))))
                                   (fun r -> post r `S.star` S.exists_ (A.pts_to arr full_perm)))
  : stt ret_t pre post =

  fun _ ->
  let arr = A.alloc #a init len in
  S.intro_pure (is_full_array arr);
  S.intro_pure (length arr == SZ.v len);
  let r = body arr () in
  S.elim_pure (is_full_array arr);
  A.free arr;
  S.return r

let with_local
  (#a:Type0)
  (init:a)
  (len:SZ.t)
  (#pre:vprop)
  (ret_t:Type)
  (#post:ret_t -> vprop)
  (body:(arr:array a) -> stt ret_t (pre **
                                    (pts_to arr (Seq.create (SZ.v len) init) **
                                     (pure (is_full_array arr) **
                                      pure (length arr == SZ.v len))))
                                   (fun r -> post r ** exists_ (pts_to arr)))
  : stt ret_t pre post =

  let body (arr:array a) : stt ret_t (pre `S.star`
                                      (pts_to arr (Seq.create (SZ.v len) init) `S.star`
                                       (pure (is_full_array arr) `S.star`
                                        pure (length arr == SZ.v len))))
                                     (fun r -> post r `S.star` S.exists_ (A.pts_to arr full_perm)) =
    fun _ ->
    S.rewrite (pre `S.star`
              (pts_to arr (Seq.create (SZ.v len) init) `S.star`
               (pure (is_full_array arr) `S.star`
                pure (length arr == SZ.v len))))
             (pre **
              (pts_to arr (Seq.create (SZ.v len) init) **
               (pure (is_full_array arr) **
                pure (length arr == SZ.v len))));
    let r = body arr () in
    S.rewrite (post r ** exists_ (pts_to arr #full_perm))
              (post r `S.star` exists_ (pts_to arr #full_perm));
    let w = S.elim_exists () in
    S.rewrite (pts_to arr #full_perm w)
              (A.pts_to arr full_perm w);
    S.intro_exists_erased w (A.pts_to arr full_perm);
    S.return r
  in

  with_local' init len ret_t body
