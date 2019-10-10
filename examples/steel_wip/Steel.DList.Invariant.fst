(*
   Copyright 2008-2019 Microsoft Research

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
module Steel.DList.Invariant

open Steel.Liar
module L = FStar.List.Tot
module HS = FStar.HyperStack
module A = Steel.Array
module P = LowStar.Permissions
#push-options "--__no_positivity"
noeq
type t (a: Type0) =
  b:A.array (cell a){A.vlength b <= 1}

and cell (a: Type0) = {
  prev: t a;
  next: t a;
  data: a;
}
#pop-options

let prev (c:cell 'a) : t 'a = c.prev
let next (c:cell 'a) : t 'a = c.next
let data (c:cell 'a) : 'a = c.data
let mk_cell (p n: t 'a) (d:'a) = {
  prev = p;
  next = n;
  data = d
}
let hd l = Cons?.hd l
let tl l = Cons?.tl l

let null_dlist (#a:Type) = admit()
let ptr_eq (#a:Type) (x y:t a) = admit()

let pure (p:prop) : resource = hsrefine empty_resource (fun _ -> p)

let elim_pure (p:prop) (h:HS.mem)
  : Lemma (inv (pure p) h ==> p)
  = ()

let intro_pure (p:prop)
  : Steel unit
    (requires empty_resource)
    (ensures fun _ -> pure p)
    (requires fun _ -> p)
    (ensures fun _ _ _ -> True)
 = ()

let node_inv (#a:Type) (#ptr:t a) (s:rmem (A.array_resource ptr)) =
  P.allows_write (A.get_rperm ptr s) /\ A.vlength ptr == 1 /\ A.freeable ptr

let pts_to (#a:Type) (ptr:t a) (v:cell a) : resource =
  hsrefine (A.array_resource ptr) (fun (s:rmem (A.array_resource ptr)) ->
    node_inv s /\
    Seq.index (A.as_rseq ptr s) 0 == v)

let pts_to_injective (#a:_) (p:t a) (v1 v2: cell a) (h:HS.mem) = ()

let pts_to_non_null_lemma (#a:_) (p:t a) (v: cell a) (h:HS.mem)
  : Lemma
    (requires inv (pts_to p v) h)
    (ensures p =!= null_dlist)
  = admit()

let pts_to_non_null (#a:_) (p:t a) (v: cell a) =
  let h = FStar.HyperStack.ST.get () in
  pts_to_non_null_lemma p v h

let read_ptr (#a:_) (ptr:t a) (c:cell a)
  : Steel (cell a)
    (requires pts_to ptr c)
    (ensures fun _ -> pts_to ptr c)
    (requires fun _ -> True)
    (ensures fun _ c' _ -> c == c')
  = as_steel (fun () -> A.index ptr 0ul)


let write_ptr (#a:_) (ptr:t a) (c0 c1:cell a)
  = as_steel (fun () -> A.upd ptr 0ul c1)

let alloc_cell (#a:_) (c:cell a)
  : Steel (t a)
    (requires
      empty_resource)
    (ensures fun p ->
      pts_to p c)
    (requires fun _ ->
      True)
    (ensures fun _ p _ ->
      p =!= null_dlist)
  = let p = as_steel (fun () -> A.alloc c 1ul) in
    pts_to_non_null p c;
    p

////////////////////////////////////////////////////////////////////////////////
// Main dlist invariant
////////////////////////////////////////////////////////////////////////////////
let rec dlist' (#a:Type) (left:t a)
                        (ptr:t a)
                        (right:t a)
                        (l:list (cell a))
    : Tot resource
      (decreases l)
    =
    match l with
    | [] ->
      pure (right == ptr)

    | hd :: tl ->
      pure (right =!= ptr) <*>
      pts_to ptr hd <*>
      pure (prev hd == left) <*>
      dlist' ptr (next hd) right tl

let dlist = dlist'

let rec dlist_injective' #a (left ptr right : t a)
                           (l1 l2:list (cell a))
                           (h:HS.mem)
  : Lemma
    (requires
      inv (dlist left ptr right l1) h /\
      inv (dlist left ptr right l2) h)
    (ensures
      l1 == l2)
   (decreases l1)
  = match l1, l2 with
    | [], [] -> ()
    | hd1::tl1, hd2::tl2 ->
      pts_to_injective ptr hd1 hd2 h;
      assert (hd1 == hd2);
      dlist_injective' ptr hd1.next right tl1 tl2 h

    | [], hd::tl
    | hd::tl, [] ->
      elim_pure (right == ptr) h;
      elim_pure (right =!= ptr) h
let dlist_injective = dlist_injective'

let intro_dlist_nil (#a:Type) (left right:t a)
   : St unit
     (requires
       empty_resource)
     (ensures fun _ ->
       dlist left right right [])
   = ()

let elim_dlist_nil (#a:Type) (left ptr right:t a) = ()

let invert_dlist_nil_eq (#a:Type) (left ptr right:t a) (l:list (cell a)) = ()

assume
val assert_pure (r:resource) (p:prop) (q:prop)
  : Steel unit
    (requires r)
    (ensures fun _ ->
      r <*> (pure p <*> pure q))
    (requires fun _ ->
      p /\ q)
    (ensures fun _ _ _ ->
      True)

let intro_dlist_cons (#a:Type) (left:t a)
                               (ptr:t a)
                               (right:t a)
                               (hd: cell a)
                               (tl: list (cell a)) =
    reveal_rst_inv ();
    reveal_empty_resource();
    reveal_star();
    assert_pure (pts_to ptr hd <*> dlist ptr (next hd) right tl) (prev hd == left) (right =!= ptr);
//    resource_assertion (((pts_to ptr hd <*> dlist ptr (next hd) right tl)) <*> (pure (prev hd == left) <*>pure  (right =!= ptr)));
    resource_assertion (pure (right =!= ptr) <*>
                        pts_to ptr hd <*>
                        pure (prev hd == left) <*>
                        dlist ptr (next hd) right tl)


let elim_dlist_cons (#a:Type) (left:t a)
                              (ptr:t a)
                              (right:t a)
                              (hd:cell a)
                              (tl:list (cell a))
   =
    reveal_rst_inv ();
    reveal_empty_resource();
    reveal_star();
    let h = FStar.HyperStack.ST.get () in
    pts_to_non_null_lemma ptr hd h



let invert_dlist_cons_neq (#a:Type) (left ptr right:t a) (l:list (cell a))
    : Steel unit
     (requires
       dlist left ptr right l)
     (ensures fun _ ->
       dlist left ptr right l)
     (requires fun _ ->
       ptr =!= right)
     (ensures fun _ _ _ ->
       Cons? l)
   = reveal_empty_resource();
     reveal_star()
