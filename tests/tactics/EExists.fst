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
module EExists

open FStar.Tactics.V2
open FStar.Reflection.Const

let pack_fv' (n:name) : Tac term = pack (Tv_FVar (pack_fv n))

// Test existential introduction using `witness` tactic
let f1 =
  assert (exists x. x == 42 ==> x + 1 == 43)
      by (witness (`42);
          let b = implies_intro() in
          norm [primops]; trefl())

let f2 = assert (exists x. x == 42 ==> x + 1 == 43)
      by (witness (`42);
          let b = implies_intro() in
          norm [primops]; trefl())
