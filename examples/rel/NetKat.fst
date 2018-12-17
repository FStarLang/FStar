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
module NetKat

(* This is a simplified F* version of the NetKat example found in Section 2 of
   the paper "NetKat: Semantic Foundations for Networks" (POPL'14) *)

module S = FStar.Set
module L = FStar.List.Tot

(* "Syntax", from Figure 2. Deeply embedded in F*. *)
type packet =
  list (field * value)

and field =
  string

and value =
  int

and history =
  h:list packet{ L.length h > 0 }

and predicate =
  | PrTrue: predicate
  | PrFalse: predicate
  | PrFieldEq: f:field -> v:value -> predicate
  | PrOr: p1:predicate -> p2:predicate -> predicate
  | PrAnd: p1:predicate -> p2:predicate -> predicate
  | PrNot: p:predicate -> predicate

and policy =
  | PoFilter: p:predicate -> policy
  | PoMod: f:field -> v:value -> policy
  | PoUnion: p1:policy -> p2:policy -> policy
  | PoSeq: p1:policy -> p2:policy -> policy
  | PoStar: p:policy -> policy
  | PoDup: policy
