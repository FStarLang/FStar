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
module Bug442

open FStar.List

type dList1 't =
    | Nil : dList1 't
    | Unit : 't -> dList1 't
    | Join : dList1 't -> dList1 't -> nat -> dList1 't

val isCorrectJoined : l : dList1 't -> Tot bool
let rec isCorrectJoined l =
    match l with
    | Nil -> true
    | Unit x -> true
    | Join Nil _ _ -> false
    | Join x y l -> isCorrectJoined x && isCorrectJoined y

//unverifieble
type dList 't = l:(dList1 't){isCorrectJoined l}

//verifieble
//type dList 't = l:dList1 't

val ld: l:dList 't -> Tot (v:nat)
let rec ld t =
    match t with
    | Nil -> 1
    | Unit x -> 1
    | Join x y _ -> 1 + ld x + ld y

val lt: l:list(dList 't) -> Tot (v:nat)
let rec lt l = 
    match l with 
    | [] -> 0
    | hd :: tl -> ld hd + lt tl

val finish : #a:Type0 -> #t:Type0 -> rights : list (dList t) -> xs : a -> f : (a -> t -> a)
-> Tot a  (decreases %[lt rights; 1])
val walk : #a:Type0 -> #t:Type0 -> rights : list (dList t)  -> l : dList t -> xs : a -> f : (a -> t -> Tot a) 
-> Tot a (decreases %[ld l + lt rights; 0])

let rec walk #a #t rights l xs f =
    match l with
    | Nil         -> finish #a #t rights xs f
    | Unit x      -> finish rights (f xs x) f
    | Join x y _  -> walk (y::rights) x xs f
and finish #a #t rights xs f =
    match rights with
    | []     -> xs
    | hd::tl -> walk tl hd xs f



val walk_alt : #a:Type u#a -> #t:Type u#t -> rights : list (dList t)  -> l : dList t -> xs : a -> f : (a -> t -> Tot a) 
-> Tot a (decreases %[ld l + lt rights; 0])


val fold : #a:Type0 -> #t:Type0 -> (a -> t -> Tot a) -> st : a -> l : dList t -> Tot (v : a)
let fold #a #t f state l = walk [] l state f

(**** A universe-polymorphic version *)

let rec walk_alt #a #t rights l xs f =
  let finish (rights':list (dList t){rights' == rights \/ Cons? rights' /\ Cons?.tl rights' == rights}) (xs:a) (f:a -> t -> a) 
    = match rights with
      | []     -> xs
      | hd::tl -> walk_alt tl hd xs f
  in      
  match l with
  | Nil         -> finish rights xs f
  | Unit x      -> finish rights (f xs x) f
  | Join x y _  -> walk_alt (y::rights) x xs f

val fold_alt : #a:Type u#a -> #t:Type u#t -> (a -> t -> Tot a) -> st : a -> l : dList t -> Tot (v : a)
let fold_alt #a #t f state l = walk_alt [] l state f
