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

// [@plugin]
// let tau1 = fun () -> dump "0";
//                        change_sq (`(eq2 #int (id #int 5) 5));
//                        dump "1"
// let _ = assert (id 5 == 5) by tau1 ()

let rec is_five (x: nat) =
  match x with
  | 5 -> fst ((snd (false, true), false))
  | _ -> is_five (x - 1)

[@plugin]
let tau2 = fun () -> dump "0";
                       change_sq (`(id 5 == (match (is_five 5) with | true -> 5 | false -> 4)));
                       dump "1"
let _ = assert (id 5 == 5) by tau2

// [@plugin]
// let tau3 = fun () -> dump "0";
//                        change_sq (`(5 == 5));
//                        dump "1"
// let _ = assert (id 5 == 5) by tau3
