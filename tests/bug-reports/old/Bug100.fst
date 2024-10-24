(*
   Copyright 2008-2018 Microsoft Research

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
module Bug100

(* run this with ../../bin/fstar.exe ../../lib/FStar.List.fst bug100.fst  *)

open List

(* this works *)
val append_length' :
  l1:list 'a -> l2:list 'a ->
  Lemma
    (requires True)
    (ensures (length (append l1 l2) = length l1 + length l2))
let rec append_length' l1 l2 =
  match l1 with
  | []    -> ()
  | _::xs -> append_length' xs l2

(* but this doesn't *)
val append_length :
  l1:list 'a -> l2:list 'a ->
  Lemma
    (requires True)
    (ensures (length (append l1 l2) = length l1 + length l2))
let rec append_length l1 l2 = by_induction_on l1 append_length
