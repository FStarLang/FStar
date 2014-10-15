(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module Global
(* Global constants and functions *)

let debug_bool = ref true

let debug modul msg =
  if !debug_bool then begin
      print_string ("["^modul^"] ");
      print_string msg ;
      print_newline ();
      flush stdout
    end
  else ()

let keyexch = ref true
let encrypting = ref true
let macing = ref true
let caching = ref false

let test b m =
  if b then ()
  else failwith m   

let assume = function e -> ()

type 'a rel = Before of  'a * 'a

let test_eq i j m =
  if i = j then ()
  else failwith m   

let test_inf i j m =
  if i < j then ()
  else failwith m   

let ssl = ref false

