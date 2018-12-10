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
module Ex04c
//mem

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

// BEGIN: Mem
val mem: #a:eqtype -> a -> list a -> Tot bool
let rec mem #a x xs =
  match xs with
  | [] -> false
  | hd :: tl -> hd = x || mem x tl
// END: Mem

// BEGIN: AppendMem
val append_mem:  #a:eqtype -> l1:list a -> l2:list a -> x:a
        -> Lemma (mem x (append l1 l2) <==> mem x l1 || mem x l2)
// END: AppendMem
let rec append_mem #a l1 l2 x = admit() //replace admit() by proof
