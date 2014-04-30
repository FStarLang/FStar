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

type l_and : Type => Type => Type
type l_or  : Type => Type => Type
type l_not : Type => Type
type l_iff : Type => Type => Type
type l_imp : Type => Type => Type
type Forall : #'a:Type => ('a => Type) => Type
type Exists : #'a:Type => ('a => Type) => Type
type ForallTyp : (Type => Type) => Type
type ExistsTyp : (Type => Type) => Type
type True : Type
type False : Type
type EqTyp : Type => Type => Type
type Eq : #'a:Type => 'a => 'a => Type
type Eq2 : #'a:Type => #'b:Type => 'a => 'b => Type
type TypeOf : #'a:Type => 'a => Type
type KindOf : Type => Type
type Not = fun ('P:Type) => (l_not 'P)
type XOR = fun ('P:Type) ('Q:Type) => (l_and (l_or 'P 'Q) (Not(l_and 'P 'Q)))
type ITE = fun ('P:Type) ('Q:Type) ('R:Type) => ('P ==> 'Q) /\ ((l_not 'P) ==> 'R)
type object
type bool
type unit
assume Unit_id: forall (x:unit). x=()

type int
type char
type byte
type uint16
type int32
type int64
type double
type string
type array : Type => Type
type ref : Type => Type
type LBL : string => Type => Type
type bytes

logic data type Tuple2: 'a:Type
          => 'b:('a => Type)
          => Type =
  | MkTuple2: 'a:Type
           -> 'b:('a => Type)
           -> _1:'a
           -> _2:'b _1
           -> Tuple2 'a 'b

logic data type Tuple3: 'a:Type
          => 'b:('a => Type)
          => 'c:(x:'a => 'b x => Type)
          => Type =
  | MkTuple3: 'a:Type
           -> 'b:('a => Type)
           -> 'c:(x:'a => 'b x => Type)
           -> _1:'a
           -> _2:'b _1
           -> _3:'c _1 _2
           -> Tuple3 'a 'b 'c

logic data type Tuple4: 'a:Type
          => 'b:(x:'a => Type)
          => 'c:(x:'a => 'b x => Type)
          => 'd:(x:'a => y:'b x => z:'c x y => Type)
          => Type =
  | MkTuple4: 'a:Type
           -> 'b:('a => Type)
           -> 'c:(x:'a => 'b x => Type)
           -> 'd:(x:'a => y:'b x => z:'c x y => Type)
           -> _1:'a
           -> _2:'b _1
           -> _3:'c _1 _2
           -> _4:'d _1 _2 _3
           -> Tuple4 'a 'b 'c 'd

logic data type Tuple5: 'a:Type
          => 'b:('a => Type)
          => 'c:(x:'a => 'b x => Type)
          => 'd:(x:'a => y:'b x => z:'c x y => Type)
          => 'e:(x:'a => y:'b x => z:'c x y => w:'d x y z => Type)
          => Type =
  | MkTuple5: 'a:Type
           -> 'b:('a => Type)
           -> 'c:(x:'a => 'b x => Type)
           -> 'd:(x:'a => y:'b x => z:'c x y => Type)
           -> 'e:(x:'a => y:'b x => z:'c x y => w:'d x y z => Type)
           -> _1:'a
           -> _2:'b _1
           -> _3:'c _1 _2
           -> _4:'d _1 _2 _3
           -> _5:'e _1 _2 _3 _4
           -> Tuple5 'a 'b 'c 'd 'e

logic data type Tuple6: 'a:Type
          => 'b:('a => Type)
          => 'c:(x:'a => 'b x => Type)
          => 'd:(x:'a => y:'b x => z:'c x y => Type)
          => 'e:(x:'a => y:'b x => z:'c x y => w:'d x y z => Type)
          => 'f:(x:'a => y:'b x => z:'c x y => w:'d x y z => u:'e x y z w => Type)
          => Type =
  | MkTuple6: 'a:Type
           -> 'b:('a => Type)
           -> 'c:(x:'a => 'b x => Type)
           -> 'd:(x:'a => y:'b x => z:'c x y => Type)
           -> 'e:(x:'a => y:'b x => z:'c x y => w:'d x y z => Type)
           -> 'f:(x:'a => y:'b x => z:'c x y => w:'d x y z => v:'e x y z w => Type)
           -> _1:'a
           -> _2:'b _1
           -> _3:'c _1 _2
           -> _4:'d _1 _2 _3
           -> _5:'e _1 _2 _3 _4
           -> _6:'f _1 _2 _3 _4 _5
           -> Tuple6 'a 'b 'c 'd 'e 'f

type exn
type float
logic data type result : Type => Type =
  | V : 'a:Type -> v:'a -> result 'a
  | E : 'a:Type -> e:exn -> result 'a
  | Err : 'a:Type -> result 'a
logic val L : 'a -> 'a
logic val R : 'a -> 'a

(* Primitive (structural) equality.
   What about for function types? *)
assume val op_Equality : 'a:Type -> 'b:Type -> x:'a -> y:'b -> z:bool {(z=true <==> x=y) /\ (z=false <==> (x<>y))}
logic type IfThenElse : 'P:Type => (u:unit{'P} => Type) => (u:unit{not 'P} => Type) => Type

logic val Add : int -> int -> int
logic val Sub : int -> int -> int
logic val Mul : int -> int -> int
logic val Div : int -> int -> int
logic val Minus : int -> int
logic val Modulo : int -> int -> int

type LT : int => int => Type
type GT : int => int => Type
type LTE : int => int => Type
type GTE : int => int => Type
type nat = i:int{i >= 0}
type pos = n:nat{n > 0}

logic data type option 'a =
  | None : option 'a
  | Some : v:'a -> option 'a

logic data type either 'a 'b =
  | Inl : v:'a -> either 'a 'b
  | Inr : v:'b -> either 'a 'b

logic data type list 'a =
  | Nil : list 'a
  | Cons : hd:'a -> tl:list 'a -> list 'a

assume val fst : ('a * 'b) -> 'a
assume val snd : ('a * 'b) -> 'b
assume val Assume: 'P:Type -> unit -> (y:unit{'P})
assume val Assert : 'P:Type -> x:unit{'P} -> y:unit{'P}
assume val lemma : 'P:Type -> x:unit{'P} -> z:unit{'P}
assume val unreachable : x:unit{LBL "unreachable" False} -> 'a
assume val failwith: string -> 'a (* TODO: refine with a monadic type *)
assume val raise: exn -> 'a (* TODO: refine with a monadic type *)
assume val pipe_right: 'a -> ('a -> 'b) -> 'b
assume val pipe_left: ('a -> 'b) -> 'a -> 'b
assume val ignore: 'a -> unit
assume val exit: int -> unit
assume val try_with: (unit -> 'a) -> (exn -> 'a) -> 'a

(* Primitive functions with trusted specs  *)
assume val op_ColonEquals: ref 'a -> 'a -> unit
assume val op_Dereference: ref 'a -> 'a
assume val op_AmpAmp             : x:bool -> y:bool -> z:bool { z=true ==>  x=true /\  y=true}
assume val op_BarBar             : x:bool -> y:bool -> z:bool { (z=true ==> x=true \/  y=true) /\
                                                                (z=false ==> x=false /\ y=false) }
assume val op_Negation           : x:bool -> y:bool { (y=true ==> x=false) /\ (y=false ==> x=true) }

assume val op_Multiply           : x:int -> y:int -> z:int{z=x*y}
assume val op_Division           : x:int -> y:int{y<>0} -> z:int{z=x/y}
assume val op_Subtraction        : x:int -> y:int -> z:int{z=x-y}
assume val op_Addition           : x:int -> y:int -> z:int{z=x+y}
assume val op_Minus              : x:int -> y:int{y=Minus x}
assume val op_Modulus            : x:int -> y:int -> z:int{z=x%y}
assume val op_LessThanOrEqual : x:int -> y:int -> z:bool{(z=true ==> x <= y) /\ (z=false ==> x > y)}
assume val op_GreaterThan : x:int -> y:int -> z:bool{(z=true ==> x > y) /\ (z=false ==> x <= y)}

(* TODO: < in operators clashes with t<..> notation. Fix *)
(* val op_GreaterThanOrEqual : x:int -> y:int -> z:bool{(z=true ==> x >= y) /\ (z=false ==> x < y) } *)
(* val op_LessThan : x:int -> y:int -> z:bool{(z=true ==> x < y) /\ (z=false ==> x >= y)} *)
    
