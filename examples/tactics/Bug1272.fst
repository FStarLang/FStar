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
module Bug1272

open FStar.Tactics

#set-options "--admit_smt_queries true"

let unsquash #a : a -> squash a =
  fun _ -> ()

let broken (a: Type0) =
  assert_by_tactic a (fun () ->
                        apply (quote (unsquash #a));
                        let xx : a = admit () in
                        exact (quote xx))

let yy : (Type0 -> unit) =
  synth_by_tactic (fun () -> exact (norm_term [] (quote broken)))

let _ =
  assert_by_tactic True
                   (fun () ->
                     admit ();
                     let x = quote 1 in
                     debug (term_to_string (norm_term [] x)))
