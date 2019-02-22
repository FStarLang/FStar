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
module Simple
[@ plugin]
let id (x:int{x >= 0}) =
  let rec countdown (y:nat) =
    if y=0 then x
    else countdown (y - 1)
  in
  countdown x

[@ plugin]
let poly_id (#a:Type) (x:int{x >= 0}) (r:a) : a =
  let rec countdown (y:nat) =
    if y=0 then r
    else countdown (y - 1)
  in
  countdown x

[@ plugin]
let mk_n_list (#a:Type) (n:nat) (x:a) : list a =
  let rec aux (n:nat) out =
    if n = 0 then out
    else aux (n - 1) (x :: out)
  in
  aux n []

[@ plugin]
let poly_list_id (#a:Type) (l:list a) =
  let rec aux (l:list a) (out:list a) =
      match l with
      | [] -> List.Tot.rev out
      | hd::tl -> aux tl (hd::out)
  in
  aux l []

[@ plugin]
let rec eq_int_list (l m :list int) : Tot bool (decreases l) =
  match l, m with
  | [], [] -> true
  | l::ls, m::ms -> l = m && eq_int_list ls ms
  | _ -> false
