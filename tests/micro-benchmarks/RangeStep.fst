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
module RangeStep

(* Checking that prims_to_fstar_range doesn't kill typing,
 * we previously got a "Patterns are incomplete" error. *)

assume new type proofstate

assume val set_proofstate_range : proofstate -> FStar.Range.range -> proofstate

noeq type result a =
    | Success of a * proofstate
    | Failed  of string * proofstate

let tac (a:Type) = proofstate -> M (result a)

let bind (a:Type) (b:Type) (r1 r2:range) (t1:tac a) (t2:a -> tac b) : tac b =
    fun ps ->
        let ps = set_proofstate_range ps (FStar.Range.prims_to_fstar_range r1) in
        let r = t1 ps in
        match r with
        | Success(a, ps')  ->
            t2 a ps'
        | Failed(msg, ps') -> Failed(msg, ps')
