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
module Bug1361

open FStar.List.Tot

let rec f (is:list int)
: Tot(list int)
           (decreases %[List.length is])
  =
match is with
| [] -> []
| i::is -> []

let f1 (is:list int) = f is

let f2 (is:list int) =
  let rec localf (is:list int)
    : Tot(list int)
           (decreases %[List.length is])
      =
    match is with
    | [] -> []
    | i::is -> []
  in
    localf is
