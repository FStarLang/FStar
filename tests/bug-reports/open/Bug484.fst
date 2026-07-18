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
module Bug484

open FStar.All

(* With "Tot", works fine *)
val ok : #a:Type
         -> p:(a -> GTot bool)
         -> f:(d:a -> Tot (r:a{p d ==> p r}))
         -> l:list a
         -> acc:a
         -> Tot a
let rec ok #a p f l acc =
    match l with
        | [] -> acc
        | _::xs -> f (ok #a p f xs acc)


(* Changing the effect to ML works when binding the result of the recursive call *)
(* VD: This example now fails with "Bound term variable not found (after unmangling)" *)
val also_ok : #a:Type
         -> p:(a -> GTot bool)
         -> f:(d:a -> Tot (r:a{p d ==> p r}))
         -> l:list a
         -> acc:a
         -> ML a
let rec also_ok #a p f l acc =
    match l with
        | [] -> acc
        | _::xs -> let u = also_ok #a p f xs acc in f u


(* But it doesn't work otherwise *)
val bug : #a:Type
         -> p:(a -> GTot bool)
         -> f:(d:a -> Tot (r:a{p d ==> p r}))
         -> l:list a
         -> acc:a
         -> ML a
let rec bug #a p f l acc =
    match l with
        | [] -> acc
        | _::xs -> f (bug #a p f xs acc)
