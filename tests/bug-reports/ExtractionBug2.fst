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
module ExtractionBug2

type list (a: Type) =
  | Nil
  | Cons of a * (list a)

let rec app_my_lists (#a: Type) (l1: list a) (l2: list a): list a =
  match l1 with
  | Nil -> l2
  | Cons (x, xs) -> Cons (x, app_my_lists xs l2)

let rec app l1 l2 =
  match l1 with
  | [] -> l2
  | x::xs -> x :: (app xs l2)
