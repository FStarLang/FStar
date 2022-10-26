(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Steel.ST.Array.Util

module G = FStar.Ghost
module US = FStar.SizeT

module R = Steel.ST.Reference
module A = Steel.ST.Array
module Loops = Steel.ST.Loops

open Steel.FractionalPermission
open Steel.ST.Effect
open Steel.ST.Util

/// Implementation of array_literal using a for loop


let array_literal_inv_pure
  (#a:Type0)
  (n:US.t)
  (f:(i:US.t{US.v i < US.v n} -> a))
  (i:Loops.nat_at_most n)
  (s:Seq.seq a)
  : prop
  = forall (j:nat).
      (j < i /\ j < Seq.length s) ==> Seq.index s j == f (US.uint_to_t j)

[@@ __reduce__]
let array_literal_inv
  (#a:Type0)
  (n:US.t)
  (arr:A.array a)
  (f:(i:US.t{US.v i < US.v n} -> a))
  (i:Loops.nat_at_most n)
  : Seq.seq a -> vprop
  = fun s ->
    A.pts_to arr full_perm s
      `star`
    pure (array_literal_inv_pure n f i s)

inline_for_extraction
let array_literal_loop_body
  (#a:Type0)
  (n:US.t)
  (arr:A.array a{A.length arr == US.v n})
  (f:(i:US.t{US.v i < US.v n} -> a))
  : i:Loops.u32_between 0sz n ->
    STT unit
        (exists_ (array_literal_inv n arr f (US.v i)))
        (fun _ -> exists_ (array_literal_inv n arr f (US.v i + 1)))
  = fun i ->
    let s = elim_exists () in
    A.pts_to_length arr s;
    elim_pure (array_literal_inv_pure n f (US.v i) s);

    A.write arr i (f i);

    intro_pure
      (array_literal_inv_pure n f (US.v i + 1) (Seq.upd s (US.v i) (f i)));
    intro_exists
      (Seq.upd s (US.v i) (f i))
      (array_literal_inv n arr f (US.v i + 1))

let array_literal #a n f =
  let arr = A.alloc (f 0sz) n in

  intro_pure
    (array_literal_inv_pure n f 1 (Seq.create (US.v n) (f 0sz)));
  intro_exists
    (Seq.create (US.v n) (f 0sz))
    (array_literal_inv n arr f 1);

  Loops.for_loop
    1sz
    n
    (fun i -> exists_ (array_literal_inv n arr f i))
    (array_literal_loop_body n arr f);

  let s = elim_exists #_ #_ #(array_literal_inv n arr f (US.v n)) () in
  A.pts_to_length arr s;
  elim_pure (array_literal_inv_pure n f (US.v n) s);
  assert (Seq.equal s (Seq.init (US.v n) (fun i -> f (US.uint_to_t i))));
  rewrite (A.pts_to arr full_perm s) _;
  return arr


/// Implementation of for_all using a while loop

let forall_pure_inv
  (#a:Type0)
  (n:US.t)
  (p:a -> bool)
  (s:Seq.seq a)
  (_:squash (Seq.length s == US.v n))
  (i:US.t)
  : prop
  = i `US.lte` n /\ (forall (j:nat). j < US.v i ==> p (Seq.index s j))

let forall_pure_inv_b
  (#a:Type0)
  (n:US.t)
  (p:a -> bool)
  (s:Seq.seq a)
  (_:squash (Seq.length s == US.v n))
  (i:US.t)
  (b:bool)
  : prop
  = b == (i `US.lt` n && p (Seq.index s (US.v i)))

[@@ __reduce__]
let forall_pred
  (#a:Type0)
  (n:US.t)
  (arr:A.array a)
  (p:a -> bool)
  (r:R.ref US.t)
  (perm:perm)
  (s:Seq.seq a)
  (_:squash (Seq.length s == US.v n))
  (b:bool)
  : US.t -> vprop
  = fun i ->
    A.pts_to arr perm s
      `star`
    R.pts_to r full_perm i
      `star`
    pure (forall_pure_inv n p s () i)
      `star`
    pure (forall_pure_inv_b n p s () i b)

[@@ __reduce__]
let forall_inv
  (#a:Type0)
  (n:US.t)
  (arr:A.array a)
  (p:a -> bool)
  (r:R.ref US.t)
  (perm:perm)
  (s:Seq.seq a)
  (_:squash (Seq.length s == US.v n))
  : bool -> vprop
  = fun b -> exists_ (forall_pred n arr p r perm s () b)

inline_for_extraction
let forall_cond
  (#a:Type0)
  (n:US.t)
  (arr:A.array a)
  (p:a -> bool)
  (r:R.ref US.t)
  (perm:perm)
  (s:G.erased (Seq.seq a))
  (_:squash (Seq.length s == US.v n))
  : unit ->
    STT bool
        (exists_ (forall_inv n arr p r perm s ()))
        (forall_inv n arr p r perm s ())
  = fun _ ->
    let _ = elim_exists () in
    let _ = elim_exists () in
    elim_pure _;
    elim_pure _;

    let i = R.read r in
    let b = i = n in
    let res =
      if b then return false
      else let elt = A.read arr i in
           return (p elt) in

    intro_pure (forall_pure_inv n p s () i);
    intro_pure (forall_pure_inv_b n p s () i res);
    intro_exists i (forall_pred n arr p r perm s () res);
    return res

inline_for_extraction
let forall_body
  (#a:Type0)
  (n:US.t)
  (arr:A.array a)
  (p:a -> bool)
  (r:R.ref US.t)
  (perm:perm)
  (s:G.erased (Seq.seq a))
  (_:squash (Seq.length s == US.v n))
  : unit ->
    STT unit
        (forall_inv n arr p r perm s () true)
        (fun _ -> exists_ (forall_inv n arr p r perm s ()))
  = fun _ ->
    let _ = elim_exists () in
    elim_pure _;
    elim_pure _;

    //atomic increment?
    let i = R.read r in
    R.write r (US.add i 1ul);

    intro_pure (forall_pure_inv n p s () (US.add i 1ul));
    intro_pure (forall_pure_inv_b n p s ()
      (US.add i 1ul)
      ((US.add i 1ul) `US.lt` n && p (Seq.index s (US.v (US.add i 1ul)))));
    intro_exists
      (US.add i 1ul)
      (forall_pred n arr p r perm s ()
         ((US.add i 1ul) `US.lt` n && p (Seq.index s (US.v (US.add i 1ul)))));
    intro_exists
      ((US.add i 1ul) `US.lt` n && p (Seq.index s (US.v (US.add i 1ul))))
      (forall_inv n arr p r perm s ())

let for_all #a #perm #s n arr p =
  A.pts_to_length arr s;

  let b = n = 0sz in

  if b then return true
  else begin
    //This could be stack allocated
    let r = R.alloc 0sz in

    intro_pure (forall_pure_inv n p s () 0sz);
    intro_pure
      (forall_pure_inv_b n p s () 0sz
         (0sz `US.lt` n && p (Seq.index s (US.v 0sz))));
    intro_exists 0sz
      (forall_pred n arr p r perm s ()
         (0sz `US.lt` n && p (Seq.index s (US.v 0sz))));
    intro_exists
      (0sz `US.lt` n && p (Seq.index s (US.v 0sz)))
      (forall_inv n arr p r perm s ());

    Loops.while_loop
      (forall_inv n arr p r perm s ())
      (forall_cond n arr p r perm s ())
      (forall_body n arr p r perm s ());

    let _ = elim_exists () in
    let _ = elim_pure _ in
    let _ = elim_pure _ in

    let i = R.read r in

    //This free would go away if we had stack allocations
    R.free r;

    return (i = n)
  end


/// Implementation of for_all2 using a while loop

let forall2_pure_inv
  (#a #b:Type0)
  (n:US.t)
  (p:a -> b -> bool)
  (s0:Seq.seq a)
  (s1:Seq.seq b)
  (_:squash (Seq.length s0 == US.v n /\ Seq.length s0 == Seq.length s1))
  (i:US.t)
  : prop
  = i `US.lte` n /\ (forall (j:nat). j < US.v i ==> p (Seq.index s0 j) (Seq.index s1 j))

let forall2_pure_inv_b
  (#a #b:Type0)
  (n:US.t)
  (p:a -> b -> bool)
  (s0:Seq.seq a)
  (s1:Seq.seq b)
  (_:squash (Seq.length s0 == US.v n /\ Seq.length s0 == Seq.length s1))
  (i:US.t)
  (g:bool)
  : prop
  = g == (i `US.lt` n && p (Seq.index s0 (US.v i)) (Seq.index s1 (US.v i)))

[@@ __reduce__]
let forall2_pred
  (#a #b:Type0)
  (n:US.t)
  (a0:A.array a)
  (a1:A.array b)
  (p:a -> b -> bool)
  (r:R.ref US.t)
  (p0 p1:perm)
  (s0:Seq.seq a)
  (s1:Seq.seq b)
  (_:squash (Seq.length s0 == US.v n /\ Seq.length s0 == Seq.length s1))
  (g:bool)
  : US.t -> vprop
  = fun i ->
    A.pts_to a0 p0 s0
      `star`
    A.pts_to a1 p1 s1
      `star`
    R.pts_to r full_perm i
      `star`
    pure (forall2_pure_inv n p s0 s1 () i)
      `star`
    pure (forall2_pure_inv_b n p s0 s1 () i g)

[@@ __reduce__]
let forall2_inv
  (#a #b:Type0)
  (n:US.t)
  (a0:A.array a)
  (a1:A.array b)
  (p:a -> b -> bool)
  (r:R.ref US.t)
  (p0 p1:perm)
  (s0:Seq.seq a)
  (s1:Seq.seq b)
  (_:squash (Seq.length s0 == US.v n /\ Seq.length s0 == Seq.length s1))
  : bool -> vprop
  = fun g -> exists_ (forall2_pred n a0 a1 p r p0 p1 s0 s1 () g)

inline_for_extraction
let forall2_cond
  (#a #b:Type0)
  (n:US.t)
  (a0:A.array a)
  (a1:A.array b)
  (p:a -> b -> bool)
  (r:R.ref US.t)
  (p0 p1:perm)
  (s0:G.erased (Seq.seq a))
  (s1:G.erased (Seq.seq b))
  (_:squash (Seq.length s0 == US.v n /\ Seq.length s0 == Seq.length s1))
  : unit ->
    STT bool
        (exists_ (forall2_inv n a0 a1 p r p0 p1 s0 s1 ()))
        (forall2_inv n a0 a1 p r p0 p1 s0 s1 ())
  = fun _ ->
    let _ = elim_exists () in
    let _ = elim_exists () in
    elim_pure _;
    elim_pure _;

    let i = R.read r in
    let b = i = n in
    let res =
      if b then return false
      else let elt0 = A.read a0 i in
           let elt1 = A.read a1 i in
           return (p elt0 elt1) in

    intro_pure (forall2_pure_inv n p s0 s1 () i);
    intro_pure (forall2_pure_inv_b n p s0 s1 () i res);
    intro_exists i (forall2_pred n a0 a1 p r p0 p1 s0 s1 () res);
    return res

inline_for_extraction
let forall2_body
  (#a #b:Type0)
  (n:US.t)
  (a0:A.array a)
  (a1:A.array b)
  (p:a -> b -> bool)
  (r:R.ref US.t)
  (p0 p1:perm)
  (s0:G.erased (Seq.seq a))
  (s1:G.erased (Seq.seq b))
  (_:squash (Seq.length s0 == US.v n /\ Seq.length s0 == Seq.length s1))
  : unit ->
    STT unit
        (forall2_inv n a0 a1 p r p0 p1 s0 s1 () true)
        (fun _ -> exists_ (forall2_inv n a0 a1 p r p0 p1 s0 s1 ()))
  = fun _ ->
    let _ = elim_exists () in
    elim_pure _;
    elim_pure _;

    //atomic increment?
    let i = R.read r in
    R.write r (US.add i 1ul);

    intro_pure (forall2_pure_inv n p s0 s1 () (US.add i 1ul));
    intro_pure (forall2_pure_inv_b n p s0 s1 ()
      (US.add i 1ul)
      ((US.add i 1ul) `US.lt` n && p (Seq.index s0 (US.v (US.add i 1ul)))
                                       (Seq.index s1 (US.v (US.add i 1ul)))));
    intro_exists
      (US.add i 1ul)
      (forall2_pred n a0 a1 p r p0 p1 s0 s1 ()
         ((US.add i 1ul) `US.lt` n && p (Seq.index s0 (US.v (US.add i 1ul)))
                                          (Seq.index s1 (US.v (US.add i 1ul)))));
    intro_exists
      ((US.add i 1ul) `US.lt` n && p (Seq.index s0 (US.v (US.add i 1ul)))
                                       (Seq.index s1 (US.v (US.add i 1ul))))
      (forall2_inv n a0 a1 p r p0 p1 s0 s1 ())

let for_all2 #a #b #p0 #p1 #s0 #s1 n a0 a1 p =
  A.pts_to_length a0 s0;
  A.pts_to_length a1 s1;

  let b = n = 0sz in

  if b then return true
  else begin
    //This could be stack allocated
    let r = R.alloc 0sz in

    intro_pure (forall2_pure_inv n p s0 s1 () 0sz);
    intro_pure
      (forall2_pure_inv_b n p s0 s1 () 0sz
         (0sz `US.lt` n && p (Seq.index s0 (US.v 0sz))
                              (Seq.index s1 (US.v 0sz))));
    intro_exists 0sz
      (forall2_pred n a0 a1 p r p0 p1 s0 s1 ()
         (0sz `US.lt` n && p (Seq.index s0 (US.v 0sz))
                              (Seq.index s1 (US.v 0sz))));
    intro_exists
      (0sz `US.lt` n && p (Seq.index s0 (US.v 0sz))
                           (Seq.index s1 (US.v 0sz)))
      (forall2_inv n a0 a1 p r p0 p1 s0 s1 ());

    Loops.while_loop
      (forall2_inv n a0 a1 p r p0 p1 s0 s1 ())
      (forall2_cond n a0 a1 p r p0 p1 s0 s1 ())
      (forall2_body n a0 a1 p r p0 p1 s0 s1 ());

    let _ = elim_exists () in
    let _ = elim_pure _ in
    let _ = elim_pure _ in

    let i = R.read r in

    //This free would go away if we had stack allocations
    R.free r;

    return (i = n)
  end
