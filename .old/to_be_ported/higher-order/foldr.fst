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
(* Folding over a vector of numbers to compute a 
   scalar product and an exponential product. 

   Completely (and very tediously) explicit about all type abstraction
   and applications.  See examples/fs2js etc. for more realistic
   codings of higher-order functions.  
*)

module FoldR2

(* F# type of foldr2:  ('b1 -> 'b2 -> 'a -> 'a) -> 'b1 list -> 'b2 list -> 'a -> 'a *)
val foldr2: 'a::* -> 'b1::* -> 'b2::* 
         -> 'PreF  :: ('b1 => 'b2 => 'a => E)
         -> 'PostF :: ('b1 => 'b2 => 'a => 'a => E) 
         -> 'Inv   :: (list 'b1 => list 'b2 => 'a => E)
         -> 'Post  :: (list 'b1 => list 'b2 => 'a => 'a => E)
         -> f:(b1:'b1 -> b2:'b2 -> a:'a{'PreF b1 b2 a} -> (aout:'a{'PostF b1 b2 a aout})) 
         -> l1:list 'b1
         -> l2:list 'b2
         -> a:'a{ ('Inv l1 l2 a) && 
                   ('Inv Nil Nil a => 'Post Nil Nil a a) &&
                   (forall (a:'a) (b1:'b1) (b2:'b2) (tl1:list 'b1) (tl2:list 'b2). 
                      ('Inv (Cons b1 tl1) (Cons b2 tl2) a) => ('Inv tl1 tl2 a)) &&
                   (forall (b1:'b1) (tl1:list 'b1) (b2:'b2) (tl2:list 'b2) (a1:'a) (aout:'a). 
                      ('Inv (Cons b1 tl1) (Cons b2 tl2) a && 'Post tl1 tl2 a a1 => 'PreF b1 b2 a1)) &&
                   (forall (b1:'b1) (tl1:list 'b1) (b2:'b2) (tl2:list 'b2) (a1:'a) (aout:'a). 
                      ('Inv (Cons b1 tl1) (Cons b2 tl2) a && 'Post tl1 tl2 a a1 && 'PostF b1 b2 a1 aout) => 
                          'Post (Cons b1 tl1) (Cons b2 tl2) a aout)}
         -> (aout:'a{'Post l1 l2 a aout})
let rec foldr2 f l1 l2 a = match l1, l2 with
  | [], [] -> a
  | (b1::tl1), (b2::tl2) -> f b1 b2 (foldr2<'a,'b1,'b2,'PreF,'PostF,'Inv,'Post> f tl1 tl2 a)

end

module Vector
open FoldR2
(* scalar products;
   I am using exp as an alias of int for exponentials
   doing them polymorphically would be quite good already *)

(* some abstract arithmetic type, e.g., BigInt *)
logic data type arith = 
  | Zero: arith
  | One: arith

type exp = arith
type vec = list arith

type Readings :: vec => E
type Rates :: vec => E
assume forall (x:arith) (xn:vec). Readings (Cons x xn) => Readings xn
assume forall (x:arith) (xn:vec). Rates (Cons x xn) => Rates xn
type Sum  :: arith => arith => arith => E
type Prod :: arith => arith => arith => E
type Exp  :: arith => arith => arith => E

type ScalarProd :: vec => vec => arith => E
assume Scalar_prod_nil: forall (a:arith). ScalarProd Nil Nil a <=> (a=Zero)
assume Scalar_prod_cons: forall (x:arith) (xn:vec) (p:arith) (pn:vec) (s:arith) (ds:arith) (s0:arith).
          (ScalarProd (Cons x xn) (Cons p pn) s) <=> (Prod x p ds && ScalarProd xn pn s0 && Sum ds s0 s)

type PostF :: _ = fun (b1:arith) (b2:arith) (ain:arith) (aout:arith) => 
    (exists (p:arith). (Prod b1 b2 p) && Sum p ain aout)
type Inv :: _ = fun (b1:list arith) (b2:list arith) (a:arith) => ScalarProd Nil Nil a
type Post :: _ = fun (b1:list arith) (b2:list arith) (a:arith) (aout:arith) => ScalarProd b1 b2 aout

val f: a:arith 
    -> b:arith 
    -> accum:arith
    -> (aout:arith{ PostF a b accum aout })
(* f a b s = a*b + s 
   impl of f in terms of mult and sum left out *)

val dot : cn:list exp 
       -> pn:list arith 
       -> (x:arith{ScalarProd cn pn x}) 
let dot cn pn = 
  assert (Inv cn pn Zero); 
  assert (Inv Nil Nil Zero => Post Nil Nil Zero Zero);
  assert (forall (a:exp) (b1:arith) (b2:arith) (tl1:list arith) (tl2:list arith).
                       (Inv (Cons b1 tl1) (Cons b2 tl2) a) => (Inv tl1 tl2 a));
  assert (forall (b1:arith) (tl1:list arith) (b2:arith) (tl2:list arith) (a1:exp) (aout:exp).
                      (Inv (Cons b1 tl1) (Cons b2 tl2) Zero && Post tl1 tl2 Zero a1 => True));
  assert (forall (b1:arith) (tl1:list arith) (b2:arith) (tl2:list arith) (a1:exp) (aout:exp).
                      (Inv (Cons b1 tl1) (Cons b2 tl2) Zero && Post tl1 tl2 Zero a1 && PostF b1 b2 a1 aout) =>
                          Post (Cons b1 tl1) (Cons b2 tl2) Zero aout);
  foldr2<exp, arith, arith, (fun (b1:arith) (b2:arith) (accum:arith) => True),
         PostF, Inv, Post> f cn pn Zero



type ExpProd :: vec => vec => arith => P
assume forall (a:arith). ExpProd Nil Nil a <=> (a=One)
assume forall (x:arith) (xn:vec) (p:arith) (pn:vec) (s:arith) (ds:arith) (s0:arith).
          (ExpProd (Cons x xn) (Cons p pn) s) <=> (Exp x p ds && ExpProd xn pn s0 && Prod ds s0 s)

val g: a:arith
    -> b:arith
    -> accum:arith
    -> (aout:arith{ exists (p:arith). Exp a b p && Prod p accum aout })

val expdot : cn:list exp
          -> pn:list arith
          -> (x:arith{ExpProd cn pn x})
let expdot cn pn =
  foldr2<exp, arith, arith,
                     (fun (b1:arith) (b2:arith) (accum:arith) => True),
                     (fun (b1:arith) (b2:arith) (ain:arith) (aout:arith) => (exists (p:arith). (Exp b1 b2 p) && Prod p ain aout)),
                     (fun (b1:list arith) (b2:list arith) (a:arith) => ExpProd Nil Nil a),
                     (fun (b1:list arith) (b2:list arith) (a:arith) (aout:arith) => ExpProd b1 b2 aout) >
                  g cn pn One

