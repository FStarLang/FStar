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
module Label


(* CH: Everything specialized to 2-point lattice *)
type label =
| Low
| High

val op_Less : label -> label -> Tot bool
let op_Less l1 l2 =
  match l1, l2 with
  | Low,High -> true
  | _, _ -> false

val op_Less_Equals : label -> label -> Tot bool
let op_Less_Equals l1 l2 =
  match l1, l2 with
  | High,Low -> false
  | _, _ -> true

val join : label -> label -> Tot label
let join l1 l2 =
  match l1, l2 with
  | Low,Low -> Low
  | _, _ -> High

val meet : label -> label -> Tot label
let meet l1 l2 =
  match l1, l2 with
  | High, High -> High
  | _, _ -> Low

let universal_property_meet l l1 l2
  : Lemma (requires (l <= l1 /\ l <= l2)) (ensures (l <= meet l1 l2))
= ()
