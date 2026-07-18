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
module Bug046

(* having this type abbreviation seems crucial for reproducing this *)
type env = int -> Tot (option int)

val empty : env
let empty _ = None

assume val xxx : g:env -> Lemma (ensures (Some? (g 45)))

val yyy : unit -> Tot unit
let yyy () =
 match 42 with
 _ -> xxx empty
