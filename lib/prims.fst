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

type l_and : E => E => P
type l_or  : E => E => P
type l_not : E => P
type l_iff : E => E => P
type l_implies : E => E => P
type Forall : 'a:S => ('a => E) => E
type Exists : 'a:S => ('a => E) => E
type Relational : E => E
type DoubleSided : E => E
type SPEC_ONLY : E => E
type True : P
type False : P
type EqTyp : E => E => E
type Eq : 'a:S => 'a => 'a => P
type Eq2 : 'a:S => 'b:S => 'a => 'b => P
type TypeOf : 'a:S => 'a => E
logic tfun type AsE : 'a:S => 'a => E
type neq2 : _ = fun ('a:S) ('b:S) (x:'a) (y:'b) => x<>y
type neq : _ = fun ('a:S) (x:'a) (y:'a) => x<>y
type KindOf : E => E
type Not : _ = fun ('P:E) => (l_not 'P)
type XOR : _ = fun ('P:E) ('Q:E) => (l_and (l_or 'P 'Q) (Not(l_and 'P 'Q)))
type ITE : _ = fun ('P:E) ('Q:E) ('R:E) => ('P ==> 'Q) /\ ((l_not 'P) ==> 'R)
type object
type bool
type unit
assume Unit_id: forall (x:unit). x=()
type int
type char
type byte
type int32
type int64
type double
type string
type ref : S => S
type LBL : string => E => E
type bytes

logic data type Tuple2: 'a:S 
          => 'b:('a => S)
          => S = 
  | MkTuple2: 'a:S 
           -> 'b:('a => S) 
           -> fst:'a 
           -> snd:'b fst 
           -> Tuple2 'a 'b

logic data type Tuple3: 'a:S 
          => 'b:('a => S) 
          => 'c:(x:'a => 'b x => S) 
          => S = 
  | MkTuple3: 'a:S 
           -> 'b:('a => S) 
           -> 'c:(x:'a => 'b x => S)
           -> fst:'a 
           -> snd:'b fst 
           -> _3:'c fst snd 
           -> Tuple3 'a 'b 'c

logic data type Tuple4: 'a:S 
          => 'b:(x:'a => S)
          => 'c:(x:'a => 'b x => S) 
          => 'd:(x:'a => y:'b x => z:'c x y => S) 
          => S = 
  | MkTuple4: 'a:S 
           -> 'b:('a => S) 
           -> 'c:(x:'a => 'b x => S)
           -> 'd:(x:'a => y:'b x => z:'c x y => S) 
           -> fst:'a 
           -> snd:'b fst 
           -> _3:'c fst snd 
           -> _4:'d fst snd _3
           -> Tuple4 'a 'b 'c 'd

logic data type Tuple5: 'a:S 
          => 'b:('a => S)
          => 'c:(x:'a => 'b x => S) 
          => 'd:(x:'a => y:'b x => z:'c x y => S) 
          => 'e:(x:'a => y:'b x => z:'c x y => w:'d x y z => S) 
          => S = 
  | MkTuple5: 'a:S 
           -> 'b:('a => S) 
           -> 'c:(x:'a => 'b x => S)
           -> 'd:(x:'a => y:'b x => z:'c x y => S) 
           -> 'e:(x:'a => y:'b x => z:'c x y => w:'d x y z => S) 
           -> fst:'a 
           -> snd:'b fst 
           -> _3:'c fst snd 
           -> _4:'d fst snd _3
           -> _5:'e fst snd _3 _4
           -> Tuple4 'a 'b 'c 'd 'e

type exn
type float
type result : S => S =
  | V : 'a:S -> v:'a -> result 'a
  | E : 'a:S -> e:exn -> result 'a
  | Err : 'a:S -> result 'a
logic val L : 'a -> 'a
logic val R : 'a -> 'a

(* Primitive (structural) equality.
   What about for function types? *)
val op_Equality : 'a:S -> 'b:S -> x:'a -> y:'b -> z:bool {(z=true <==> x=y) /\ (z=false <==> (x<>y))}
type IfThenElse : 'P:E => (u:unit{'P} => E) => (u:unit{not 'P} => E) => E
(* Integer arithmetic *)
logic val Add : int -> int -> int
logic val Sub : int -> int -> int
logic val Mul : int -> int -> int
logic val Div : int -> int -> int
logic val Minus : int -> int
logic val Modulo : int -> int -> int

type LT : int => int => E
type GT : int => int => E
type LTE : int => int => E
type GTE : int => int => E
type nat = i:int{i >= 0}
type pos = n:nat{n > 0}

logic data type option 'a =
  | None : option 'a
  | Some : v:'a -> option 'a

type either 'a 'b =
  | Inl : v:'a -> either 'a 'b
  | Inr : v:'b -> either 'a 'b

logic data type list 'a =
  | Nil : list 'a
  | Cons : hd:'a -> tl:list 'a -> list 'a

val Assume: 'P:E -> unit -> (y:unit{'P})
val Assert : 'P:E -> x:unit{'P} -> y:unit{'P}
val lemma : 'P:E -> x:unit{'P} -> z:unit{'P}
val unreachable : x:unit{LBL "unreachable" False} -> 'a

(* Primitive functions with trusted specs  *)
val _dummy_op_ColonEquals: ref 'a -> 'a -> unit
val _dummy_op_Dereference: ref 'a -> 'a
val _dummy_op_AmpAmp             : x:bool -> y:bool -> z:bool { z=true ==>  x=true /\  y=true}
val _dummy_op_BarBar             : x:bool -> y:bool -> z:bool { (z=true ==> x=true \/  y=true) /\
                                                                (z=false ==> x=false /\ y=false) }
val _dummy_op_Negation           : x:bool -> y:bool { (y=true ==> x=false) /\ (y=false ==> x=true) }

val _dummy_op_Multiply           : x:int -> y:int -> z:int{z=x*y}
val _dummy_op_Division           : x:int -> y:int{y<>0} -> z:int{z=x/y}
val _dummy_op_Subtraction        : x:int -> y:int -> z:int{z=x-y}
val _dummy_op_Addition           : x:int -> y:int -> z:int{z=x+y}
val _dummy_op_Minus              : x:int -> y:int{y=Minus x}
val _dummy_op_Modulus            : x:int -> y:int -> z:int{z=x%y}

val _dummy_op_LessThanOrEqual : x:int -> y:int -> z:bool{(z=true ==> x <= y) /\ (z=false ==> x > y)}
val _dummy_op_GreaterThan : x:int -> y:int -> z:bool{(z=true ==> x > y) /\ (z=false ==> x <= y)}

(* TODO: >= in operators clashes with t<..> notation. Fix *)
(* val _dummy_op_GreaterThanOrEqual : x:int -> y:int -> z:bool{(z=true ==> x >= y) /\ (z=false ==> x < y) } *)
(* val _dummy_op_LessThan : x:int -> y:int -> z:bool{(z=true ==> x < y) /\ (z=false ==> x >= y)} *)
