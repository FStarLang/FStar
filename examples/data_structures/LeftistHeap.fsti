(*
   Copyright 2023 Microsoft Research
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

module LeftistHeap

class ordered (a:eqtype) =
{
  leq : a -> a -> bool;
  [@@@FStar.Tactics.Typeclasses.no_method]
  properties : squash (
    (forall x. leq x x) /\ // reflexivity
    (forall a b c. (leq a b /\ leq b c) ==> leq a c) /\ // transivitive
    (forall a b. (leq a b /\ leq b a) ==> a = b) /\ // antisymmetry
    (forall a b. leq a b \/ leq b a) // total
  )
}

let rec merge #t {| _: ordered t |} (a: list t) (b: list t): GTot (list t) =
  match a, b with
  | [], _ -> b
  | _, [] -> a
  | ta::qa, tb::qb -> if (leq ta tb) then ta :: (merge qa b) else tb :: (merge a qb)
  
let rec sorted #t {| _: ordered t|} (l: list t): GTot bool =
  match l with
  | x::y::q -> if leq x y then sorted (y::q) else false
  | _ -> true

val leftist (a: eqtype) {| _ : ordered a |}: eqtype

val to_list (#a: eqtype) {| _: ordered a|} (t:leftist a):
  GTot (l:list a{sorted l})

val empty (#a: eqtype) {| _: ordered a |}:
  (t:leftist a{ to_list t = [] })

val isEmpty (#a: eqtype) {| _: ordered a |} (t:leftist a):
  (b:bool{ b <==> to_list t = [] })

val singleton (#a: eqtype) {| _: ordered a |} (k:a):
  (s:leftist a{to_list s = [k]})

val merge_heaps (#a: eqtype) {| _: ordered a |}  (t1 t2:leftist a):
  (t:leftist a{ to_list t = merge (to_list t1) (to_list t2) })

val insert (#a: eqtype) {| _: ordered a |}  (x:a) (t:leftist a):
  (t':leftist a{ to_list t' = merge [x] (to_list t) })

val get_min (#a: eqtype) {| _: ordered a |}  (t:leftist a{ ~(isEmpty t) }):
  (x:a{ x = Cons?.hd (to_list t) })

val delete_min (#a: eqtype) {| _: ordered a |}  (t: leftist a{~(isEmpty t)}):
  (t':leftist a{to_list t' = Cons?.tl (to_list t) })