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
module Bug1485

open FStar.All

assume val err_exn : 'a -> ML unit

let catch_errors (f : unit -> 'a) : ML unit =
    try ()
    with | ex -> err_exn ex

let catch_errors' (f : unit -> 'a) : ML (option 'a) =
    try let r = f () in Some r
    with | ex -> err_exn ex; None

let aux (b:bool) : ML int =
    try 0
    with | _ -> if b
                then 1
                else 2

let aux2 (b:bool) : ML exn =
    try failwith ""
    with | e -> if b
                then e
                else e
