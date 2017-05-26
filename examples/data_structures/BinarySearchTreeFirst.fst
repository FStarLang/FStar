(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

(*
   Exercising:
    -- indexed types
    -- implicit value parameters
    -- dependent tuples
    -- and refinements, of course
 *)

module BinarySearchTreeFirst

open FStar.List.Tot

(* The type of a binary tree indexed by its max element *)
type tree (r:int) =
  | Node : #l   :int
        -> left :option (tree l)
        -> n    :int
        -> right:option (tree r){l <= n
                                 /\ n <= r
                                 /\ (None? right <==> n=r)
                                 /\ (None? left <==> n=l)}
        -> tree r

(* Need to supply #i for the empty sub-trees, since it can't be inferred by unification *)
let leaf i : tree i = Node #i #i None i None

let max i j = if i < j then j else i

val insert: #k:int -> t:tree k -> i:int -> Tot (tree (max k i)) (decreases t)
let rec insert (#k:int) (Node left n right) i =
  if i = n
  then Node left n right (* no duplicates *)
  else if i < n
  then match left with
       | None ->
          Node (Some (leaf i)) n right
       | Some left ->
          Node (Some (insert left i)) n right
  else match right with
       | None ->
          Node left n (Some (leaf i))
       | Some right ->
          Node left n (Some (insert right i))

val contains: #k:int -> t:tree k -> key:int -> Tot bool (decreases t)
let rec contains (#k:int) t key =
  if key > k
  then false
  else let Node left i right = t in
       i=k
       || (key < i && Some? left && contains (Some?.v left) key)
       || (Some? right && contains (Some?.v right) key)

val in_order_opt: #k:int -> t:option (tree k) -> Tot (list int) (decreases t)
let rec in_order_opt (#k:int) t = match t with
  | None -> []
  | Some (Node left i right) ->
     in_order_opt left@[i]@in_order_opt right

val index_is_max : #max:int
                -> t:option (tree max)
                -> x:int
                -> Lemma (ensures (List.Tot.mem x (in_order_opt t) ==> x <= max))
                         (decreases t)
let rec index_is_max (#max:int) t x = admit()
(* CH: 2016-07-28 This started failing recently with:
  ./BinarySearchTreeFirst.fst(91,23-91,24): Subtyping check failed;
  expected type (x#105346:Prims.int{(Prims.precedes (Prims.LexCons left
  Prims.LexTop) (Prims.LexCons t Prims.LexTop))}); got type Prims.int
CH: this is very strange since it is reported on x, which has no decreases clause
  match t with
  | None -> ()
  | Some (Node left i right) ->
     List.Tot.append_mem (in_order_opt left @ [i]) (in_order_opt right) x;
     List.Tot.append_mem (in_order_opt left) [i] x;
     index_is_max left x;
     index_is_max right x
*)

val index_is_max2 : #max:int
                -> t:option (tree max)
                -> x:int
                -> Lemma (ensures (List.Tot.mem x (in_order_opt t) ==> x <= max))
                         (decreases t)
let rec index_is_max2 (#max:int) t x = admit()
(* CH: 2016-07-28 This started failing recently
  match t with
  | None -> ()
  | Some (Node #l left i #r right) -> (* You can also writing the implicit arguments explicitly ... just testing it *)
     List.Tot.append_mem (in_order_opt #l left @ [i]) (in_order_opt #r right) x;
     List.Tot.append_mem (in_order_opt #l left) [i] x;
     index_is_max2 #l left x;
     index_is_max2 #r right x
*)

type t = (l:int & tree l)
val ins : lt:t -> n:int -> Tot t
let ins (| m, tt |) n = (| max m n, insert tt n |) (* open the dependent pair by matching it; repackage it, using the expected type t from the annotation *)
