(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.Unionfind

(* Persistent union-find implementation adapted from
   https://www.lri.fr/~filliatr/puf/ *)

open FStarC.Effect
open FStarC.SmallInt
module A = FStarC.Array

(* Persistent arrays *)
private noeq
type data (a:Type) =
  | PArray of A.array a
  | PDiff of t & a & ref (data a)

private
type pa_t (a:Type) = ref (data a)

private
let pa_create (#a:Type) (n:t) (v:a) : ML (pa_t a) = mk_ref (PArray (A.make n v))

(* In continuation-passing style, so that a long chain of diffs does not
   overflow the stack *)
private
let rec pa_rerootk (#a:Type) (p:pa_t a) (k:unit -> ML unit) : ML unit =
  match !p with
  | PArray _ -> k ()
  | PDiff (i, v, p') ->
    pa_rerootk p' (fun () ->
      (match !p' with
       | PArray arr ->
         let v' = A.get arr i in
         A.set arr i v;
         p := PArray arr;
         p' := PDiff (i, v', p)
       | PDiff _ -> failwith "Impossible");
      k ())

(* The underlying array, after rerooting *)
private
let pa_array (#a:Type) (p:pa_t a) : ML (A.array a) =
  pa_rerootk p (fun () -> ());
  match !p with
  | PArray arr -> arr
  | PDiff _ -> failwith "Impossible"

private
let pa_get (#a:Type) (p:pa_t a) (i:t) : ML a =
  match !p with
  | PArray arr -> A.get arr i
  | PDiff _ -> A.get (pa_array p) i

private
let pa_set (#a:Type) (p:pa_t a) (i:t) (v:a) : ML (pa_t a) =
  let arr = pa_array p in
  let old = A.get arr i in
  A.set arr i v;
  let res = mk_ref (PArray arr) in
  p := PDiff (i, old, res);
  res

(* Stores [x] at index [l], doubling the array if [l] is past its end *)
private
let pa_new (#a:Type) (p:pa_t a) (x:a) (l:t) (empty:a) : ML unit =
  let arr = pa_array p in
  if A.length arr = l then begin
    let tail = A.make l empty in
    A.set tail zero x;
    p := PArray (A.append arr tail)
  end else
    A.set arr l x

(* Union-find implementation based on persistent arrays *)
private noeq
type puf_rec (a:Type) = {
  (* array of parents of each node: either the parent's index or, for a
     root, its value.  A reference to allow path compression. *)
  parent : ref (pa_t (either t a));
  ranks : pa_t t;
  (* how many elements are allocated in the array *)
  count : ref t;
}

type puf (a:Type) = puf_rec a

private
type p_uvar_rec (a:Type) = | P of t

type p_uvar (a:Type) = p_uvar_rec a

let puf_empty () =
  { parent = mk_ref (pa_create (of_int 2) (Inl minus_one));
    ranks = pa_create (of_int 2) zero;
    count = mk_ref zero }

let puf_fresh h x =
  let count = !h.count in
  pa_new !h.parent (Inr x) count (Inl minus_one);
  pa_new h.ranks zero count zero;
  h.count := count + one;
  P count

(* implements path compression, returns new array *)
private
let rec puf_find_aux (#a:Type) (f:pa_t (either t a)) (i:t) : ML (pa_t (either t a) & a & t) =
  match pa_get f i with
  | Inl fi ->
    let f, r, id = puf_find_aux f fi in
    let f = pa_set f i (Inl id) in
    f, r, id
  | Inr x -> f, x, i

(* return both rep and previous version of parent array *)
private
let puf_find_i (#a:Type) (h:puf a) (x:p_uvar a) : ML (a & t) =
  let P x = x in
  let f, r, i = puf_find_aux !h.parent x in
  h.parent := f;
  r, i

(* only return the equivalence class *)
private
let puf_id' (#a:Type) (h:puf a) (x:p_uvar a) : ML t =
  snd (puf_find_i h x)

let puf_id h x = to_int (puf_id' h x)

let puf_fromid _ id = P (of_int id)

let puf_find h x = fst (puf_find_i h x)

let puf_union h x y =
  let ix = puf_id' h x in
  let iy = puf_id' h y in
  if ix <> iy then begin
    let rxc = pa_get h.ranks ix in
    let ryc = pa_get h.ranks iy in
    if rxc > ryc then
      { h with parent = mk_ref (pa_set !h.parent iy (Inl ix)) }
    else if rxc < ryc then
      { h with parent = mk_ref (pa_set !h.parent ix (Inl iy)) }
    else
      { h with parent = mk_ref (pa_set !h.parent iy (Inl ix));
               ranks = pa_set h.ranks ix (rxc + one) }
  end else
    h

let puf_equivalent h x y = puf_id' h x = puf_id' h y

let puf_change h x v =
  let i = puf_id' h x in
  { h with parent = mk_ref (pa_set !h.parent i (Inr v)) }

let puf_unique_id x = let P a = x in to_int a
