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
module Bug1299

open FStar.Tactics

let id () : Tac unit = ()

let failing () : Tac unit = fail "Uh oh"

let should_fail (t : unit -> Tac 'a) : Tac unit =
    match trytac t  with
    | None -> ()
    | Some _ -> fail "did not fail"

let make_term () : Tac term =
  let tt_tm = `() in
  let id_tm = `id in
  let failing_tm = `failing in
  let unit_tm = `unit in
  let binder = fresh_binder unit_tm in
  pack (Tv_Abs binder (mk_app id_tm [(mk_app failing_tm [(tt_tm, Q_Explicit)], Q_Explicit)]))

let test : unit =
  assert True
      by (should_fail (fun () -> let tm = make_term () in
                                 let normalized_tm = norm_term [delta] tm in
                                 debug ("n = " ^ term_to_string normalized_tm);
                                 let t = unquote #(unit -> Tac unit) normalized_tm in
                                 t ()))
