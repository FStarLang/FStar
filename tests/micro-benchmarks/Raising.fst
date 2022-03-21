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
module Raising

(* Taken from #1370, due to Wolfram Kahl *)

open FStar.Pervasives
open FStar.Exn

effect Raises (a:Type) (ex:exn) =
    Exn a (requires True)
        (ensures (function
                | V _ -> True
                | E e -> e == ex
                | _ -> False
        ))

exception Bad

val u : nat -> Raises nat Bad
let u i = if i > 10
    then i
    else raise Bad
