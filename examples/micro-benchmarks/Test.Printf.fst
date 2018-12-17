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
module Test.Printf

open FStar.Printf

let test_sprintf () = sprintf "%d: Hello %s, sprintf %s %ul" 0 "#fstar-hackery" "works!" 0ul

type something =
  | This
  | That

let something_to_string =
  function
    | This -> "this"
    | That -> "that"

let parse_something : extension_parser =
  function
    | 'S' :: rest -> Some (MkExtension something_to_string, rest)
    | _ -> None

inline_for_extraction
let my_sprintf = ext_sprintf parse_something

let test_ext () = my_sprintf "%d: Hello %s, sprintf %s %ul, with %XS or %XS extensions"
                  0 "#fstar-hackery" "works!" 0ul This That
