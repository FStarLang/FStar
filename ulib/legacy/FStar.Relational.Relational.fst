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
module FStar.Relational.Relational
open FStar.Heap

(* Relational Type constructor (Equivalent to pairs) *)
type rel (a:Type) (b:Type) : Type =
  | R : l:a -> r:b -> rel a b

(* Some frequently used abbreviations *)
type double (t:Type) = rel t t
type eq (t:Type) = p:(double t){R?.l p == R?.r p}

let twice x = R x x
let tu = twice ()

(* functions to lift normal functions to Relational functions *)
val rel_map1T : ('a -> Tot 'b) -> (double 'a) -> Tot (double 'b)
let rel_map1T f (R x1 x2)  = R (f x1) (f x2)

val rel_map2Teq : #a:eqtype -> #b:eqtype -> #c:Type -> (a -> b -> Tot c) -> (double a) -> (double b) -> Tot (double c)
let rel_map2Teq #a #b #c f (R x1 x2) (R y1 y2) = R (f x1 y1) (f x2 y2)

val rel_map2T : ('a -> 'b -> Tot 'c) -> (double 'a) -> (double 'b) -> Tot (double 'c)
let rel_map2T f (R x1 x2) (R y1 y2) = R (f x1 y1) (f x2 y2)

val rel_map2G : ('a -> 'b -> GTot 'c) -> (double 'a) -> (double 'b) -> GTot (double 'c)
let rel_map2G f (R x1 x2) (R y1 y2) = R (f x1 y1) (f x2 y2)

val rel_map3T : ('a -> 'b -> 'c -> Tot 'd) -> (double 'a) -> (double 'b) -> (double 'c) -> Tot (double 'd)
let rel_map3T f (R x1 x2) (R y1 y2) (R z1 z2) = R (f x1 y1 z1) (f x2 y2 z2)

val rel_map3G : ('a -> 'b -> 'c -> GTot 'd) -> (double 'a) -> (double 'b) -> (double 'c) -> GTot (double 'd)
let rel_map3G f (R x1 x2) (R y1 y2) (R z1 z2) = R (f x1 y1 z1) (f x2 y2 z2)

(* Some convenient arithmetic functions *)
let op_Hat_Plus = rel_map2T (fun x y -> x + y)
let op_Hat_Minus = rel_map2T (fun x y -> x - y)
let op_Hat_Star = rel_map2T (fun x y -> op_Multiply x y)
let op_Hat_Slash = rel_map2T (fun x y -> x / y)

(* Some convenient list functions *)
val tl_rel: #a:Type -> l:double (list a){Cons? (R?.l l) /\ Cons? (R?.r l)}-> Tot (double (list a))
let tl_rel #a (R (_::xs) (_::ys)) = R xs ys
let cons_rel (R x y) (R xs ys) = R (x::xs) (y::ys)
(* Some convenient tuple functions *)
let pair_rel (R a b) (R c d) = R (a,c) (b,d)
let triple_rel (R a b) (R c d) (R e f) = R (a,c,e) (b,d,f)
let fst_rel = rel_map1T fst 
let snd_rel = rel_map1T snd 
 
(* Some convenient boolean functions *)
let and_rel = rel_map2T (fun x y -> x && y)
let or_rel = rel_map2T (fun x y -> x || y)
let eq_rel = rel_map2Teq (fun (x y:bool) -> x = y)

(* Some convenient functions combining left and right side (for specification only) *)
let and_irel (R a b) = a && b
let or_irel (R a b) = a || b
let eq_irel (#t:eqtype) (x:(rel t t)) = match x with
  | R a b -> a = b

(* Some convenient functions on heap (for specification) *)
let sel_rel1 (#a:Type) (h:double heap) (r:ref a)  = rel_map2G sel h (twice r)
//let sel_rel2 = rel_map2G sel
//let upd_rel = rel_map3G upd
