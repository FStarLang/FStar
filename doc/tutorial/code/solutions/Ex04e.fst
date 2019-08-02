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
module Ex04e
//find

type option 'a =  
   | None : option 'a
   | Some : v:'a -> option 'a

(* The intrinsic style is more convenient in this case *)
val find : f:('a -> Tot bool) -> list 'a -> Tot (option (x:'a{f x}))
let rec find f l = match l with
  | [] -> None
  | hd :: tl -> if f hd then Some hd else find f tl

(* Extrinsically things are more verbose, since we are basically duplicating
   the structure of find in find_some. It's still not too bad. *)

val find' : #t:Type -> f:(t -> Tot bool) -> list t -> Tot (option t)
let rec find' #t f l = match l with
  | [] -> None
  | hd :: tl -> if f hd then Some hd else find' f tl

val find_some : f:('a -> Tot bool) -> xs:(list 'a) ->
    Lemma (None? (find' f xs) || f (Some?.v (find' f xs)))
let rec find_some f xs =
    match xs with
    | [] -> ()
    | x :: xs' -> find_some f xs'

(* [Some?.v] and [None?] are convenient ways to manipulate options.  They are
   described later in the tutorial.  Here's a more verbose way to achieve the
   same thing: *)

val find_some' : f:('a -> Tot bool) -> xs:(list 'a) ->
    Lemma (match find f xs with
           | None -> true
           | Some v -> f v)
let rec find_some' f xs =
    match xs with
    | [] -> ()
    | x :: xs' -> find_some' f xs'
