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


module Vector

type vector 'a : nat -> Type =
  | VNil : vector 'a 0 
  | VCons : 'a -> n:nat -> vector 'a n -> vector 'a (n + 1) 

val head: n:pos -> vector 'a n -> 'a
let head n v = match v with
  | VCons x m xs -> x

val nth : n:nat -> m:(m:nat{m > n}) -> vector 'a m -> 'a
let rec nth n m v =
  match v with
    | VCons x m' xs -> if n = 0 then x else nth (n-1) m' xs
