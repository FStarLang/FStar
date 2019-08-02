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
(** Second implementation with λ-lifting **)
module CPS.SimpleLambdaLifting
open FStar.List.Tot

val add_cps_intern : (int -> Tot 'a) -> int -> int -> Tot 'a
let add_cps_intern k x y = k (x + y)

val add_cps : list int -> (int -> Tot 'a) -> Tot 'a
let rec add_cps l k = match l with
  | [] -> k 0
  | hd::tl -> add_cps tl (add_cps_intern k hd)

val add : list int -> Tot int
let add l = add_cps l (fun x -> x)
