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
module Prims

(* logical connectives *)
type l_and :: E => E => P
type l_or  :: E => E => P
type l_not :: E => P
type l_iff :: E => E => P
type l_implies :: E => E => P
type Forall :: 'a::* => ('a => E) => E
type Exists :: 'a::* => ('a => E) => E
type ForallA :: 'a::A => ('a => E) => E
type ExistsA :: 'a::A => ('a => E) => E
type True :: P
type False :: P

type Eq :: 'a::* => 'a => 'a => P
type Eq2 :: 'a::* => 'b::* => 'a => 'b => P
type EqA :: 'a::A => 'a => 'a => E
type TypeOf :: 'a::* => 'a => E

type NTuple =
  | Tuple_UU : 'a -> 'b -> ('a * 'b)
  | Tuple_UA : 'a::* -> 'b::A -> 'a -> 'b -> ('a * 'b) 
  | Tuple_AU : 'a::A -> 'b::* -> 'a -> 'b -> ('a * 'b)
  | Tuple_AA : 'a::A -> 'b::A -> 'a -> 'b -> ('a * 'b)

type pf  :: E => P  =
  | T                : pf True

type object
type bool
type unit
type int
type string
type bytes
type float
val op_Equality : x:'a -> y:'a -> z:bool {z=true <=> x=y}
(* Primitive functions with trusted specs for concrete refinements *)
logic val Add : int -> int -> int
logic val Sub : int -> int -> int
logic val Mul : int -> int -> int
logic val Div : int -> int -> int
logic val Minus : int -> int
logic val Modulo : int -> int -> int

type LT :: int => int => E
type GT :: int => int => E
type LTE :: int => int => E
type GTE :: int => int => E

logic data type exn =
  | Exception : string -> exn

type result :: * => * =
  | V : 'a -> result 'a
  | E : exn -> result 'a
  | Err : result 'a

val _dummy_op_AmpAmp             : x:bool -> y:bool -> z:bool { z=true =>  x=true &&  y=true}
val _dummy_op_BarBar             : x:bool -> y:bool -> z:bool { (z=true => x=true ||  y=true) && 
                                                                (z=false => x=false && y=false)}
val _dummy_op_Multiply           : int -> int -> int
val _dummy_op_Division           : int -> int -> int
val _dummy_op_Subtraction        : x:int -> y:int -> z:int{z=(Sub x y)}
val _dummy_op_Addition           : x:int -> y:int -> z:int{z=(Add x y)}
val _dummy_op_GreaterThanOrEqual : int -> int -> bool
val _dummy_op_GreaterThan        : x:int -> y:int -> b:bool{b=true <=> GT x y}
val _dummy_op_Negation           : x:bool -> y:bool { (y=true => x=false) && (y=false => x=true)}
val _dummy_op_Modulus		 : int -> int -> int



extern reference Runtime { language = "F#";
                           dll="runtime";
                           namespace="Microsoft.FStar.Runtime";
                           classname="Pickler"}

type ref :: * => *
type locations::*
logic val Empty : locations
logic val Singleton : ref 'a -> locations
logic val Union : locations -> locations -> locations
logic val Mem : ref 'a -> locations -> bool
assume forall (r:ref 'a). ((Mem r (Singleton r)) = true)
assume forall (l1:locations) (l2:locations) (r:ref 'a). (Mem r (Union l1 l2)) = ((Mem r l1) || (Mem r l2))
assume forall (r:ref 'a). (Mem r Empty) = false

type heap::*
logic val Select : ref 'a -> heap -> 'a
logic val Update : ref 'a -> 'a -> heap -> heap 
logic val Domain : heap -> locations
assume forall (h:heap) (x:ref 'a) (v:'a). (Select x (Update x v h)) = v
assume forall (h:heap) (x:ref 'a) (y:ref 'b) (v:'a). (not (Eq2 x y)) => (Select y (Update x v h)) = (Select y h)
assume forall (h:heap) (x:ref 'a) (v:'a). Domain (Update x v h) = (Union (Domain h) (Singleton x))

type ST :: _ =
         (fun ('Pre::heap => E) ('a::*) ('Post::'a => heap => E) => h:heap{'Pre h} -> (x:'a * (h':heap{'Post x h'})))
val bind_st : 'Pre::(heap => E) 
           -> 'a::* 
           -> 'Post1::('a => heap => E) 
           -> 'b::* 
           -> 'Post::('b => heap => E) 
           -> ST 'Pre 'a 'Post1
           -> (x:'a -> ST ('Post1 x) 'b 'Post)
           -> ST 'Pre 'b 'Post
let bind_st c1 c2 = fun heap ->
  let x, heap' = c1 heap in
    c2 x heap'

val return_refined_st : 'a::*
             -> 'R::('a => E)
             -> 'Post::('a => heap => E)
             -> x:'a{'R x}
             -> ST (fun (h:heap) => ((Forall 'a (fun x => (('R x) => ('Post x h)))))) 'a 'Post
let return_refined_st x = fun h -> (x, h)

val return_st : 'a::*
             -> 'Post::('a => heap => E)
             -> x:'a
             -> ST ('Post x) 'a 'Post
let return_st x = fun h -> (x, h)

type DST :: _ = fun ('a::*) ('Tx::('a => heap => E) => heap => E) => 
    ('Post::('a => heap => E) -> ST ('Tx 'Post) 'a 'Post)
type returnDST :: _ = (fun ('a::*) (x:'a) ('Post::'a => heap => E) => 
    'Post x)
type composeDST :: _ = (fun ('a::*) ('b::*) 
                          ('Tx1::('a => heap => E) => heap => E) 
                          ('Tx2::'a => ('b => heap => E) => heap => E)
                          ('Post::'b => heap => E) => 
    'Tx1 (fun (x:'a) => 'Tx2 x 'Post))

extern Runtime val read : 'a::*
                       -> x:ref 'a 
                       -> DST 'a (fun ('Post::'a => heap => E) (h:heap) => (forall (y:'a). y=(Select x h) => 'Post y h))

extern Runtime val write : 'a::*
                        -> x:ref 'a
                        -> v:'a
                        -> DST unit (fun ('Post::unit => heap => E) (h:heap) => (forall (h':heap). h'=(Update x v h) => 'Post () h'))

extern Runtime val ref : 'a::* 
                      -> x:'a 
                      -> DST (ref 'a) (fun ('Post::ref 'a => heap => E) (h:heap) => (forall (h':heap) (y:ref 'a). (h'=(Update y x h)) && (Mem y (Domain h)=false) => 'Post y h'))

extern Runtime val raise: 'a::* 
                       -> string 
                       -> DST 'a (fun ('Post::'a => heap => E) (h:heap) => True)

extern Runtime val Assert : 'P::(heap => E)
                         -> unit
                         -> DST unit (fun ('Post::unit => heap => E) (h:heap) => (('P h) && ('Post () h)))

extern Runtime val Assume : 'P :: (heap => E)
                         -> unit
                         -> DST unit (fun ('Post::unit => heap => E) (h:heap) => (('P h) => ('Post () h)))

type option :: * => * =
  | None : option 'a
  | Some : 'a -> option 'a

type list :: * => * =
  | Nil : list 'a
  | Cons : 'a -> list 'a -> list 'a

