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
   TODO: Termination checking is not yet implemented. 
   A let rec with an explicitly annotated "Tot" effect is admitted. 
   Without such an annotation, the inferred effect is "All" 
*)

module Recursion
open Prims.PURE

(* An elaborate way of computing zero *)
type z = i:int{i==0}
val zero: list 'a -> Tot z
let rec zero l = match l with
  | [] -> 0
  | hd::tl -> zero tl

(* Using a refinement type to prove a property of a function as it is being defined, 
   i.e., an intrinsic proof about length being non-negative *)
val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | hd::tl -> 1 + length tl

(* Similar to length, although there's no interesting refinement here. *)
val mem: 'a -> list 'a -> Tot bool
let rec mem a l = match l with
  | [] -> false
  | hd::tl -> hd=a || mem a tl

(* Prove a property about the length of appended lists intrinsically.
   Notice the use of the pure function length in the spec. 

For contrast, in old F*/F7, you'd have to write:

   logic function Length: 'a -> list 'a -> nat
   assume Length_nil: ...
   assume Length_cons: ...
   val length: l:list 'a -> (n:nat{n=Length l})
   let rec length l = ... 

   val append: l1:list 'a -> l2:list 'a -> (l3:list 'a{Length l3 = Length l1 + Length l2})
   let rec append = ...
*)
val append: l1:list 'a -> l2:list 'a -> Tot (l3:list 'a{length l3 == length l1 + length l2})
let rec append l1 l2 =  match l1 with
  | [] -> l2
  | hd::tl -> hd::append tl l2

(* You can also prove lemmas about pure functions "after the fact", i.e., extrinsically. 
   Here's an inductive proofs relating append and mem. 
   
   Such an extrinsic proof would have been impossible in old F*/F7. You'd have to
   prove the relation between mem and append intrinsically.

   Alternatively, you could 
     1. define a logic function Append and Mem (like Length above), 
     2. intrinsically prove the connection between append and Append, mem and Mem
     3. extrinsically try to use induction to prove relate Append and Mem

        generally, 3 is not possible, since you couldn't write total
        functions easily. So, you'd have to resort to an external
        proof (in Coq, say) and then admit it to the SMT solver.
 *)
val append_mem:  l1:list 'a
              -> l2:list 'a
              -> a:'a
              -> Lemma (mem a (append l1 l2) <==>  mem a l1 \/ mem a l2)
let rec append_mem l1 l2 a = match l1 with
  | [] -> ()
  | hd::tl -> 
    if hd=a
    then ()
    else append_mem tl l2 a
  
