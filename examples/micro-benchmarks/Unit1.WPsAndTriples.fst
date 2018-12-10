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
module Unit1.WPsAndTriples
unfold let as_requires (#a:Type) (wp:pure_wp a) = wp (fun x -> True)
unfold let as_ensures  (#a:Type) (wp:pure_wp a) (x:a) = ~ (wp (fun y -> ~(y==x)))
assume val as_Pure: #a:Type -> #b:(a -> Type)
          -> #wp:(x:a -> GTot (pure_wp (b x)))
          -> $f:(x:a -> PURE (b x) (wp x))
          -> x:a -> Pure (b x) (as_requires (wp x))
                             (as_ensures (wp x))

val f : x:int -> PURE int (fun 'p -> x > 0 /\ 'p (x + 1)) 
let f x = assert (x > 0); x + 1

val h : #req:(int -> Type) -> #ens:(int -> int -> Type) -> $f:(x:int -> Pure int (req x) (ens x)) -> y:int -> Pure int (req y) (ens y)
let h #req #ens f x = f x

val g : x:int -> Pure int (b2t (x > 0)) (fun y -> y == x + 1)
let g = h (as_Pure f)
