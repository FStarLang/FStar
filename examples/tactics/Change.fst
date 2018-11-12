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
module Change

open FStar.Tactics

let id #a (x:a) : a = x

let dump msg =
    if false
    then Tactics.dump msg
    else ()

let _ = assert_by_tactic (id 5 == 5)
            (fun () -> dump "0";
                       change_sq (`(eq2 #int (id #int 5) 5));
                       dump "1")

let _ = assert_by_tactic (id 5 == 5)
            (fun () -> dump "0";
                       change_sq (`(id 5 == 5));
                       dump "1")

let _ = assert_by_tactic (id 5 == 5)
            (fun () -> dump "0";
                       change_sq (`(5 == 5));
                       dump "1")
