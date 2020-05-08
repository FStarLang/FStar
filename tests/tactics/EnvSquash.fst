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
module EnvSquash

open FStar.Tactics

assume val p : int -> prop

(* Testing that the binders introduced into the context when
 * splitting a VC do not have their types squashed, which causes
 * a less efficient SMT encoding, and is unneeded anyhow. *)

let test () =
    let tau () : Tac unit =
      let bs = binders_of_env (cur_env ()) in
      guard (Cons? (List.Tot.rev bs));
      let b = List.Tot.hd (List.Tot.rev bs) in
      match term_as_formula' (type_of_binder b) with
      | Exists _ _ -> ()
      | _ -> fail ("unexpected type for last binder: " ^ term_to_string (type_of_binder b))
    in
    assume (exists x. p x);
    assert True by tau ()
