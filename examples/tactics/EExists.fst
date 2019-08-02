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

open FStar.Tactics
open FStar.Classical
open FStar.Squash

let pack_fv' (n:name) : Tac term = pack (Tv_FVar (pack_fv n))

let eexists (a:Type) (t:unit -> Tac a) : Tac a =
  apply_lemma (`exists_intro); later(); norm[];
  fst (divide (ngoals()-1) t dismiss)

let f1 =
  assert (exists x. x == 42 ==> x + 1 == 43)
      by (eexists unit (fun _ ->
          let b = implies_intro() in
          let _ = tcut (mk_e_app (pack_fv' squash_qn) [type_of_binder b]) in
          flip();
          trefl();
          norm [primops]; trefl()))

// inlining this tactic below causes the end of the world
let foo () : Tac unit =
            eexists unit (fun _ ->
            let b = implies_intro() in
            (match term_as_formula' (type_of_binder b) with
            | Comp (Eq (Some t)) x y ->
              (match inspect x, inspect y with
              | Tv_Uvar _ _, _ | _, Tv_Uvar _ _ ->
                if unify x y then (norm [primops]; trefl())
                             else fail "unexpected1"
              | _, _ -> fail "unexpected2")
            | _ -> fail "unexpected3"))

let f2 = assert (exists x. x == 42 ==> x + 1 == 43) by foo ()
