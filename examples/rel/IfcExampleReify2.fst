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
module IfcExampleReify2

open WhileReify
open IfcRulesReify
open IfcTypechecker
open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.Exceptions

let hi : id = to_id 0
let lo : id = to_id 1
let c : id = to_id 2

let env var =
  if var = hi then High
  else if var = lo then Low
    else if var = c then Low
      else High

(*
  While c > 0{
    hi := lo + 1
    lo := hi + 1
    c := c - 1
  }
*)

let c_1 body = While (AVar c) body (AVar c)
let c_2 = Assign hi (AOp Plus (AVar lo) (AInt 1))
let c_3 = Assign lo (AOp Plus (AVar hi) (AInt 1))
let c_4 = Assign c (AOp Minus (AVar c) (AInt 1))
let c_body =  Seq (Seq c_2 c_3) c_4

let c_1_4 = c_1 c_body

#set-options "--z3rlimit 30"
let c_2_3_ni () : Lemma (requires True) (ensures ni_com env (Seq c_2 c_3) Low) = ()


val cmd_ni : unit ->
  Exn label (requires True) (ensures fun ol -> Inl? ol ==> ni_com env c_1_4 (Inl?.v ol))
let cmd_ni () = tc_com_hybrid env c_1_4 [Seq c_2 c_3, Low]

(* let tc_c_4 () : Lemma (reify (tc_com env c_4) () == Inl Low) = () *)
(* let tc_hybrid_c_4 () : Lemma (reify (tc_com_hybrid env c_4 [Seq c_2 c_3, Low]) () == Inl Low) = () *)

(* let tc_cmd_low () : Lemma (Inl? (reify (tc_com_hybrid env cmd [Seq c_2 c_3, Low]) ())) *)
(* = *)
(*   assert (reify (tc_com_hybrid env (Seq c_2 c_3) [Seq c_2 c_3, Low]) () == Inl Low) ; *)
(*   tc_hybrid_c_4 () ; *)
(*   assert (reify (tc_com_hybrid env c_4 [Seq c_2 c_3, Low]) () == Inl Low) ; *)
(*   assert (reify (tc_com_hybrid env c_body [Seq c_2 c_3, Low]) () == Inl Low) ; *)
(*   assert (reify (tc_com_hybrid env cmd [Seq c_2 c_3, Low]) () == Inl Low) *)

(*
 * AR: 06/03/18: this lemma crucially relies on abstraction leaks in DM4F.Heap.IntStorefixed
 *               e.g. https://github.com/FStarLang/FStar/commit/d35b38915094276d2e4c2d01fe7e6b3dd5114a63
 *                    commit fixes the leaks, and if we revert those changes, the lemma goes through
 *               adding admit
 *)
let c_1_4_ni' () : Lemma (ensures ni_com env c_1_4 Low) = admit ();
  c_2_3_ni(); match (reify (tc_com_hybrid env c_1_4 [Seq c_2 c_3, Low]) ()) with | Inl l -> ()
