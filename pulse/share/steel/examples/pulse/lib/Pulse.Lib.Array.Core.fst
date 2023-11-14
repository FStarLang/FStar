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

let pts_to_len' (#t:Type0) (a:array t) (#p:perm) (#x:Seq.seq t)
    : stt_ghost unit emp_inames
          (pts_to a #p x)
          (fun _ → pts_to a #p x `S.star` S.pure (length a == Seq.length x))
= 
  fun _ ->
    A.pts_to_length #_ #_ #p a x;
    noop ()
let pts_to_len = pts_to_len'

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

let pts_to_range_split'
  (#elt: Type0)
  (a: array elt)
  (i m j: nat)
  (#p: perm)
  (#s: Seq.seq elt)
: stt_ghost unit emp_inames
    (pts_to_range a i j #p s `S.star`
      S.pure (i <= m /\ m <= j)
    )
    (fun _ -> S.exists_ (fun s1 -> S.exists_ (fun s2 ->
      pts_to_range a i m #p s1 **
      pts_to_range a m j #p s2 **
      S.pure (
        i <= m /\ m <= j /\ j <= length a /\
        Seq.length s == j - i /\
        s1 == Seq.slice s 0 (m - i) /\
        s2 == Seq.slice s (m - i) (Seq.length s) /\
        s == Seq.append s1 s2
    ))))
= fun _ ->
    let _ = S.elim_pure _ in
    A.pts_to_range_split a i m j;
    noop ()

let pts_to_range_split = pts_to_range_split'

let pts_to_range_join'
  (#elt: Type0)
  (a: array elt)
  (i m j: nat)
  (#p: perm)
  (#s1 #s2: Seq.seq elt)
: stt_ghost unit emp_inames
    (pts_to_range a i m #p s1 `S.star` pts_to_range a m j #p s2)
    (fun _ -> pts_to_range a i j #p (s1 `Seq.append` s2))
= fun _ ->
    A.pts_to_range_join a i m j;
    noop ()

let pts_to_range_join = pts_to_range_join'

let pts_to_range_index'
  (#t: Type)
  (a: array t)
  (i: SZ.t)
  (#l: Ghost.erased nat{l <= SZ.v i})
  (#r: Ghost.erased nat{SZ.v i < r})
  (#s: Ghost.erased (Seq.seq t))
  (#p: perm)
: stt t
    (requires
      pts_to_range a l r #p s)
    (ensures fun res ->
      pts_to_range a l r #p s `S.star`
      S.pure (Seq.length s == r - l /\
            res == Seq.index s (SZ.v i - l)))
= fun _ ->
    let res = A.pts_to_range_index a l i r in
    S.return res

let pts_to_range_index = pts_to_range_index'

let pts_to_range_upd'
  (#t: Type)
  (a: array t)
  (i: SZ.t)
  (v: t)
  (#l: Ghost.erased nat{l <= SZ.v i})
  (#r: Ghost.erased nat{SZ.v i < r})
  (#s0: Ghost.erased (Seq.seq t))
: stt unit
    (requires pts_to_range a l r #full_perm s0)
    (ensures fun _ -> (S.exists_ (fun s -> pts_to_range a l r #full_perm s `S.star`
    S.pure(
      Seq.length s0 == r - l /\ s == Seq.upd s0 (SZ.v i - l) v
    ))))
= fun _ ->
    let _ = A.pts_to_range_upd a l i r v in
    noop ()

let pts_to_range_upd = pts_to_range_upd'

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
