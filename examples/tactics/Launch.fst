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
module Launch

open FStar.Tactics

(* This file will only work if run with --unsafe_tactic_exec.
 * It CANNOT be set with #(re)set-options either
 *)

let _ =
    assert_by_tactic True
        (fun () -> let s = launch_process "date" "" "" in
                   debug ("The date is: <" ^ s ^ ">"))

let _ =
    assert_by_tactic True
        (fun () -> let s = launch_process "echo" "Hello F*!" "" in
                   debug ("Greeting: <" ^ s ^ ">"))

let _ =
    assert_by_tactic True
        (fun () -> let s = launch_process "cat" "" "input" in
                   debug ("Testing input: <" ^ s ^ ">"))
