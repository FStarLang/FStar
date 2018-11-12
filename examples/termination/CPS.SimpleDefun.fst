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
(** It is easy to defunctionalize it **)
module CPS.SimpleDefun
open FStar.List.Tot

type cont =
  | C0 : cont
  | C1 : cont -> int -> cont

val apply : cont -> int -> Tot int
let rec apply k r = match k with
  | C0 -> r
  | C1 k hd -> apply k (hd + r)

val add_cps : list int -> cont -> Tot int
let rec add_cps l k = match l with
  | [] -> apply k 0
  | hd::tl -> add_cps tl (C1 k hd)

val add : list int -> Tot int
let add l = add_cps l C0
