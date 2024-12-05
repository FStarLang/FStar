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
module Bug417

assume val f: unit -> GTot bool

assume val coerce: $g:(unit -> GTot unit) -> unit -> Tot unit

let ok =
  let g : unit -> GTot unit = fun _ -> let _ = f () in () in
  coerce g

//this used to fail, because the inferred type is not **equal** to (unit -> GTot unit), although it can be subsumed to that type
//Until the change described in https://github.com/FStarLang/FStar/wiki/Minimizing-verification-conditions-by-omitting-redundant-equality-hypotheses
//infers it to have (unit -> GTot unit)
let no_longer_fails =
  coerce (fun _ -> let _ = f () in ())
