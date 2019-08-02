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
module TestHeapST

open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST

(*  let x () : STNull unit = () *)

(* let chose (h0 : heap) (r:(ref int)) (_:unit{h0 `contains_a_well_typed` r}) = *)
(*   let h1 = normalize_term (snd (reify (write r 42) h0)) in *)
(*   assert (h1 == upd h0 r 42) *)

(* let truc (h0 : heap) (r:(ref int)) (_:unit{h0 `contains_a_well_typed` r}) = *)
(*   let h = normalize_term (snd (reify (let x = read r in write r x) h0)) in *)
(*   assert_norm (h == upd h0 r (sel h0 r)) *)

let rec loop (n:nat) : STNull unit (decreases n) = loop n

(* let machin (h0 : heap) (r:(ref int)) (_:unit{h0 `contains_a_well_typed` r}) (x:int) = *)
(*   let res = normalize_term (reify (let () = write r x in read r) h0) in *)
(*   assert_norm (res == (x, upd h0 r x)) ; *)
(*   res *)



(* assume val h0 : heap *)
(* assume val r : ref int *)
(* assume val r2 : ref int *)
(* assume val r1 : ref int *)

(* assume WellDefinedR : h0 `contains_a_well_typed` r *)
(* assume WellDefinedR1 : h0 `contains_a_well_typed` r1 *)
(* assume WellDefinedR2 : h0 `contains_a_well_typed` r2 *)

(* let h1 = snd (reify (write r 42) h0) *)

(* let h2 = snd (reify (let x = read r in write r x) h0) *)

(* assume val x : int *)
(* let res = normalize_term (reify (let () = write r x in read r) h0) *)
