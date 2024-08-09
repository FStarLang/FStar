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
module Bug1271

open FStar.Tactics.V2

let test =
  assert (True ==> True)
      by (let b = implies_intro () in
          let qb = quote b in
          let qf = quote (fun (b: binding) () -> print "f") in // f: tactic unit
          let q_fofb = mk_app qf [(qb, Q_Explicit)] in
          print ("::: " ^ term_to_string q_fofb);
          let tac = unquote #(unit -> Tac unit) q_fofb in
          tac ();
          trivial ())
