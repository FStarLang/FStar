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
module U32 = FStar.UInt32

module R = Steel.ST.Reference
module A = Steel.ST.Array
module Loops = Steel.ST.Loops

open Steel.FractionalPermission
open Steel.ST.Effect
open Steel.ST.Util

/// Implementation of array_literal using a for loop


let array_literal_inv_pure
  (#a:Type0)
  (n:U32.t)
  (f:(i:U32.t{U32.v i < U32.v n} -> a))
  (i:Loops.nat_at_most n)
  (s:Seq.seq a)
  : prop
  = forall (j:nat).
      (j < i /\ j < Seq.length s) ==> Seq.index s j == f (U32.uint_to_t j)

[@@ __reduce__]
let array_literal_inv
  (#a:Type0)
  (n:U32.t)
  (arr:A.array a)
  (f:(i:U32.t{U32.v i < U32.v n} -> a))
  (i:Loops.nat_at_most n)
  : Seq.seq a -> vprop
  = fun s ->
    A.pts_to arr full_perm s
      `star`
    pure (array_literal_inv_pure n f i s)

//#set-options "--debug Steel.ST.Array.Util --debug_level Extreme,Rel,2635,2365,TacVerbose,SMTEncoding --print_full_names --print_bound_var_types --print_implicits --ugly"
//#set-options "--log_queries --fuel 2 --ifuel 2"
//#restart-solver
inline_for_extraction
let array_literal_loop_body
  (#a:Type0)
  (n:U32.t)
  (arr:A.array a{A.length arr == U32.v n})
  (f:(i:U32.t{U32.v i < U32.v n} -> a))
  : i:Loops.u32_between 0ul n ->
    STT unit
        (exists_ (array_literal_inv n arr f (U32.v i)))
        (fun _ -> exists_ (array_literal_inv n arr f (U32.v i + 1)))
  = fun i ->
    let s = elim_exists () in
    A.pts_to_length arr s;
    elim_pure (array_literal_inv_pure n f (U32.v i) s);

    A.write arr i (f i);

    intro_pure
      (array_literal_inv_pure n f (U32.v i + 1) (Seq.upd s (U32.v i) (f i)));
    intro_exists
      (Seq.upd s (U32.v i) (f i))
      (array_literal_inv n arr f (U32.v i + 1))

let array_literal #a n f =
  let arr = A.alloc (f 0ul) n in

  intro_pure
    (array_literal_inv_pure n f 1 (Seq.create (U32.v n) (f 0ul)));
  intro_exists
    (Seq.create (U32.v n) (f 0ul))
    (array_literal_inv n arr f 1);

  Loops.for_loop
    1ul
    n
    (fun i -> exists_ (array_literal_inv n arr f i))
    (array_literal_loop_body n arr f);

  let s = elim_exists () in
  A.pts_to_length arr s;
  elim_pure (array_literal_inv_pure n f (U32.v n) s);
  assert (Seq.equal s (Seq.init (U32.v n) (fun i -> f (U32.uint_to_t i))));
  rewrite (A.pts_to arr full_perm s) _;
  return arr


/// Implementation of for_all using a while loop

let forall_pure_inv
  (#a:Type0)
  (n:U32.t)
  (p:a -> bool)
  (s:Seq.seq a)
  (_:squash (Seq.length s == U32.v n))
  (i:U32.t)
  : prop
  = i `U32.lte` n /\ (forall (j:nat). j < U32.v i ==> p (Seq.index s j))

let forall_pure_inv_b
  (#a:Type0)
  (n:U32.t)
  (p:a -> bool)
  (s:Seq.seq a)
  (_:squash (Seq.length s == U32.v n))
  (i:U32.t)
  (b:bool)
  : prop
  = b == (i `U32.lt` n && p (Seq.index s (U32.v i)))

[@@ __reduce__]
let forall_pred
  (#a:Type0)
  (n:U32.t)
  (arr:A.array a)
  (p:a -> bool)
  (r:R.ref U32.t)
  (perm:perm)
  (s:Seq.seq a)
  (_:squash (Seq.length s == U32.v n))
  (b:bool)
  : U32.t -> vprop
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
  (n:U32.t)
  (arr:A.array a)
  (p:a -> bool)
  (r:R.ref U32.t)
  (perm:perm)
  (s:Seq.seq a)
  (_:squash (Seq.length s == U32.v n))
  : bool -> vprop
  = fun b -> exists_ (forall_pred n arr p r perm s () b)

inline_for_extraction
let forall_cond
  (#a:Type0)
  (n:U32.t)
  (arr:A.array a)
  (p:a -> bool)
  (r:R.ref U32.t)
  (perm:perm)
  (s:G.erased (Seq.seq a))
  (_:squash (Seq.length s == U32.v n))
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
  (n:U32.t)
  (arr:A.array a)
  (p:a -> bool)
  (r:R.ref U32.t)
  (perm:perm)
  (s:G.erased (Seq.seq a))
  (_:squash (Seq.length s == U32.v n))
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
    R.write r (U32.add i 1ul);

    intro_pure (forall_pure_inv n p s () (U32.add i 1ul));
    intro_pure (forall_pure_inv_b n p s ()
      (U32.add i 1ul)
      ((U32.add i 1ul) `U32.lt` n && p (Seq.index s (U32.v (U32.add i 1ul)))));
    intro_exists
      (U32.add i 1ul)
      (forall_pred n arr p r perm s ()
         ((U32.add i 1ul) `U32.lt` n && p (Seq.index s (U32.v (U32.add i 1ul)))));
    intro_exists
      ((U32.add i 1ul) `U32.lt` n && p (Seq.index s (U32.v (U32.add i 1ul))))
      (forall_inv n arr p r perm s ())

let for_all #a #perm #s n arr p =
  A.pts_to_length arr s;

  let b = n = 0ul in

  if b then return true
  else begin
    //This could be stack allocated
    let r = R.alloc 0ul in

    intro_pure (forall_pure_inv n p s () 0ul);
    intro_pure
      (forall_pure_inv_b n p s () 0ul
         (0ul `U32.lt` n && p (Seq.index s (U32.v 0ul))));
    intro_exists 0ul
      (forall_pred n arr p r perm s ()
         (0ul `U32.lt` n && p (Seq.index s (U32.v 0ul))));
    intro_exists
      (0ul `U32.lt` n && p (Seq.index s (U32.v 0ul)))
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
  (n:U32.t)
  (p:a -> b -> bool)
  (s0:Seq.seq a)
  (s1:Seq.seq b)
  (_:squash (Seq.length s0 == U32.v n /\ Seq.length s0 == Seq.length s1))
  (i:U32.t)
  : prop
  = i `U32.lte` n /\ (forall (j:nat). j < U32.v i ==> p (Seq.index s0 j) (Seq.index s1 j))

let forall2_pure_inv_b
  (#a #b:Type0)
  (n:U32.t)
  (p:a -> b -> bool)
  (s0:Seq.seq a)
  (s1:Seq.seq b)
  (_:squash (Seq.length s0 == U32.v n /\ Seq.length s0 == Seq.length s1))
  (i:U32.t)
  (g:bool)
  : prop
  = g == (i `U32.lt` n && p (Seq.index s0 (U32.v i)) (Seq.index s1 (U32.v i)))

[@@ __reduce__]
let forall2_pred
  (#a #b:Type0)
  (n:U32.t)
  (a0:A.array a)
  (a1:A.array b)
  (p:a -> b -> bool)
  (r:R.ref U32.t)
  (p0 p1:perm)
  (s0:Seq.seq a)
  (s1:Seq.seq b)
  (_:squash (Seq.length s0 == U32.v n /\ Seq.length s0 == Seq.length s1))
  (g:bool)
  : U32.t -> vprop
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
  (n:U32.t)
  (a0:A.array a)
  (a1:A.array b)
  (p:a -> b -> bool)
  (r:R.ref U32.t)
  (p0 p1:perm)
  (s0:Seq.seq a)
  (s1:Seq.seq b)
  (_:squash (Seq.length s0 == U32.v n /\ Seq.length s0 == Seq.length s1))
  : bool -> vprop
  = fun g -> exists_ (forall2_pred n a0 a1 p r p0 p1 s0 s1 () g)

inline_for_extraction
let forall2_cond
  (#a #b:Type0)
  (n:U32.t)
  (a0:A.array a)
  (a1:A.array b)
  (p:a -> b -> bool)
  (r:R.ref U32.t)
  (p0 p1:perm)
  (s0:G.erased (Seq.seq a))
  (s1:G.erased (Seq.seq b))
  (_:squash (Seq.length s0 == U32.v n /\ Seq.length s0 == Seq.length s1))
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
  (n:U32.t)
  (a0:A.array a)
  (a1:A.array b)
  (p:a -> b -> bool)
  (r:R.ref U32.t)
  (p0 p1:perm)
  (s0:G.erased (Seq.seq a))
  (s1:G.erased (Seq.seq b))
  (_:squash (Seq.length s0 == U32.v n /\ Seq.length s0 == Seq.length s1))
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
    R.write r (U32.add i 1ul);

    intro_pure (forall2_pure_inv n p s0 s1 () (U32.add i 1ul));
    intro_pure (forall2_pure_inv_b n p s0 s1 ()
      (U32.add i 1ul)
      ((U32.add i 1ul) `U32.lt` n && p (Seq.index s0 (U32.v (U32.add i 1ul)))
                                       (Seq.index s1 (U32.v (U32.add i 1ul)))));
    intro_exists
      (U32.add i 1ul)
      (forall2_pred n a0 a1 p r p0 p1 s0 s1 ()
         ((U32.add i 1ul) `U32.lt` n && p (Seq.index s0 (U32.v (U32.add i 1ul)))
                                          (Seq.index s1 (U32.v (U32.add i 1ul)))));
    intro_exists
      ((U32.add i 1ul) `U32.lt` n && p (Seq.index s0 (U32.v (U32.add i 1ul)))
                                       (Seq.index s1 (U32.v (U32.add i 1ul))))
      (forall2_inv n a0 a1 p r p0 p1 s0 s1 ())

let for_all2 #a #b #p0 #p1 #s0 #s1 n a0 a1 p =
  A.pts_to_length a0 s0;
  A.pts_to_length a1 s1;

  let b = n = 0ul in

  if b then return true
  else begin
    //This could be stack allocated
    let r = R.alloc 0ul in

    intro_pure (forall2_pure_inv n p s0 s1 () 0ul);
    intro_pure
      (forall2_pure_inv_b n p s0 s1 () 0ul
         (0ul `U32.lt` n && p (Seq.index s0 (U32.v 0ul))
                              (Seq.index s1 (U32.v 0ul))));
    intro_exists 0ul
      (forall2_pred n a0 a1 p r p0 p1 s0 s1 ()
         (0ul `U32.lt` n && p (Seq.index s0 (U32.v 0ul))
                              (Seq.index s1 (U32.v 0ul))));
    intro_exists
      (0ul `U32.lt` n && p (Seq.index s0 (U32.v 0ul))
                           (Seq.index s1 (U32.v 0ul)))
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
