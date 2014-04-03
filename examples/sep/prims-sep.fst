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
type ForallP :: 'a::P => ('a => E) => E
type ExistsP :: 'a::P => ('a => E) => E
type Forall :: 'a::* => ('a => E) => E
type Exists :: 'a::* => ('a => E) => E
type ForallA :: 'a::A => ('a => E) => E
type ExistsA :: 'a::A => ('a => E) => E
type ExistsTyp :: (E => E) => E
type Relational :: E => E
type DoubleSided :: E => E
type SPEC_ONLY :: E => E
type True :: P
type False :: P
type EqTyp :: E => E => E
type Eq :: 'a::* => 'a => 'a => P
type Eq2 :: 'a::* => 'b::* => 'a => 'b => P
type EqA :: 'a::A => 'a => 'a => E
type TypeOf :: 'a::* => 'a => E
type KindOf :: E => E
logic tfun type AsE :: 'a::* => 'a => E
type neq :: _ = (fun ('a::*) (x:'a) (y:'a) => l_not (Eq 'a x y))
type Not :: _ = fun ('P::E) => (l_not 'P)
type XOR :: _ = fun ('P::E) ('Q::E) => (l_and (l_or 'P 'Q) (Not(l_and 'P 'Q)))

type NTuple =
  | Tuple_UU : 'a -> 'b -> ('a * 'b)
  | Tuple_UA : 'a::* -> 'b::A -> 'a -> 'b -> ('a * 'b) 
  | Tuple_AU : 'a::A -> 'b::* -> 'a -> 'b -> ('a * 'b)
  | Tuple_AA : 'a::A -> 'b::A -> 'a -> 'b -> ('a * 'b)
  | Tuple_UP : 'a::* -> 'b::P -> 'a -> 'b -> ('a * 'b) 
  | Tuple_PU : 'a::P -> 'b::* -> 'a -> 'b -> ('a * 'b)
  | Tuple_PP : 'a::P -> 'b::P -> 'a -> 'b -> ('a * 'b)
  | Tuple_PA : 'a::P -> 'b::A -> 'a -> 'b -> ('a * 'b) 
  | Tuple_AP : 'a::A -> 'b::P -> 'a -> 'b -> ('a * 'b)

type pf  :: E => P  =
  | T                : pf True

type ITE :: _ = fun ('P::E) ('Q::E) ('R::E) =>  
    (('P ==> 'Q) && (not 'P) ==> 'R)
type object
type bool
type unit
(* assume Unit_id: forall (x:unit). x=() *)
type int
type string
type LBL :: string => E => E
type bytes
type ref :: * => *
logic data type exn =
  | Exception : string -> exn
type float
type result :: * => * =
  | V : 'a -> result 'a
  | E : exn -> result 'a
  | Err : result 'a
type undef 
type nul 
logic val L : 'a -> 'a
logic val R : 'a -> 'a
(* Primitive (structural) equality. 
   What about for function types? *)
val op_Equality : x:'a -> y:'a -> z:bool {(z=true <==> x=y) && (z=false <==> (x<>y))}
type IfThenElse :: 'P::E => (u:unit{'P} => E) => (u:unit{not 'P} => E) => E
(* Integer arithmetic *)
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

type nat = i:int{i >= 0}
type pos = n:nat{n > 0}
val id : 'a::* -> 'a -> 'a
let id x = x

val idprop : 'a::P -> 'a -> 'a
let idprop x = x

val apply: ('a -> 'b) -> 'a -> 'b
let apply f x = f x

val idint: int -> int
let idint x = id x

logic data type option 'a =
  | None : option 'a
  | Some : 'a -> option 'a

type optionP ('a::P) =
  | NoneP : optionP 'a
  | SomeP : 'a -> optionP 'a

type either 'a 'b =
  | Inl : 'a -> either 'a 'b
  | Inr : 'b -> either 'a 'b

val bind_opt: ('a -> 'b) -> option 'a -> option 'b
let bind_opt f x = match x with
  | None -> None
  | Some x -> Some (f x)
  
logic data type list 'a =
  | Nil : list 'a
  | Cons : 'a -> list 'a -> list 'a

type In :: 'a::* => 'a => list 'a => E
type ListUnion :: 'a::* => list 'a => list 'a => list 'a => E
assume In_hd: forall (hd:'a) (tl:list 'a). (In hd (Cons hd tl))
assume In_tl: forall (hd:'a) (x:'a) (tl:list 'a). (In x tl) => (In x (Cons hd tl))
assume notinNil: forall (x:'a). not (In x Nil)
assume notinCons: forall (x:'a) (y:'a) (tl:list 'a). ((not (In x tl)) && (not (x=y))) => not (In x (Cons y tl))

val mem: x:'a -> l:list 'a -> b:bool{b=true <==> In x l}
let rec mem x = function 
  | [] -> false
  | hd::tl -> if hd = x then true else mem x tl

val map: ('a -> 'b) -> list 'a -> list 'b
let rec map f x = match x with 
  | Nil -> Nil
  | Cons a tl -> Cons (f a) (map f tl)

val fold_left: ('a -> 'b -> 'a) -> 'a -> list 'b -> 'a
let rec fold_left f x y = match y with 
  | Nil -> x
  | Cons hd tl -> fold_left f (f x hd) tl

val fold_right: ('a -> 'b -> 'b) -> list 'a -> 'b -> 'b
let rec fold_right f l x = match l with
  | Nil -> x
  | Cons hd tl -> fold_right f tl (f hd x)

val iterate: ('a -> unit) -> list 'a -> unit
let rec iterate f x = match x with
  | Nil -> ()
  | Cons a tl -> let _ = f a in iterate f tl
                                  
val fold_left_A: 'a::A -> 'b::* -> ('a -> 'b >> 'a) -> 'a -> list 'b >> 'a
let rec fold_left_A f a l = match l with
  | Nil -> a
  | Cons hd tl -> fold_left_A f (f a hd) tl
 
val assoc: 'a -> list ('a*'b) -> option 'b
let rec assoc a x = match x with
  | Nil -> None
  | Cons (a', b) tl -> if a=a' then Some b else assoc a tl

(* val append: x:list 'a -> y:list 'a -> z:list 'a { forall (a:'a). In a z <=> (In a x || In a y)} *)
(* let rec append x y = match x with *)
(*   | Nil -> y *)
(*   | Cons a tl -> Cons a (append tl y) *)

(* val concatMap: ('a -> list 'b) -> list 'a -> list 'b *)
(* let rec concatMap f = function *)
(*   | [] -> [] *)
(*   | a::tl -> append (f a) (concatMap f tl) *)

extern reference String {language="C#";
                         dll="mscorlib";
                         namespace="System";
                         classname="String"}

extern String val Concat: string -> string -> string


(* Some library functions *)
extern reference SysConvert {language="C#";
                             dll="mscorlib";
                             namespace="System";
                             classname="Convert"}
extern SysConvert val ToBase64String : bytes -> string
extern SysConvert val FromBase64String : string -> bytes

extern reference Runtime { language = "F#";
                           dll="runtime";
                           namespace="Microsoft.FStar.Runtime";
                           classname="Pickler"}

type Serialized :: 'a::* => 'a => bytes => E

logic val ReprInt: int -> string
logic val Strcat : string -> string -> string
extern Runtime type punit :: P
extern Runtime val freshname : bool -> string
extern Runtime val debug_println : string -> bool
extern Runtime val println : string -> bool
extern Runtime val printfile: string -> string -> bool
extern Runtime val printfileNoLn: string -> string -> bool
extern Runtime val print_stderr : string -> bool
extern Runtime val print_string : string -> bool
extern Runtime val string_of_any : 'a -> string
extern Runtime val string_of_any_for_coq : 'a -> string
extern Runtime val string_of_any_for_coq_afn : 'a -> string
extern Runtime val string_of_any_for_coq_p : 'a -> string
extern Runtime val writeToFile : string -> 'a -> string
extern Runtime val writeCertToFile : string -> 'a -> string
extern Runtime val print_int : int -> bool
extern Runtime val strcat : string -> string -> string
extern Runtime val strStartsWith: string -> string -> bool
extern Runtime val intToString: n:int -> s:string{s=(ReprInt n)}
extern Runtime val stringToInt: s:string -> n:int{s=(ReprInt n)}
extern Runtime val strRmPfx: s:string -> pfx:string -> r:string{s=(Strcat pfx r)}
extern Runtime val intCheckRange: int -> int -> int -> bool

extern Runtime val strSplitByDelimiter: s:string -> d:string -> (r1:string*r2:string{(Strcat r1 r2)=s})
extern Runtime val createComm: int -> ((bool -> bytes) * (bytes -> bool))
extern Runtime val stopAllServers: bool -> bool
extern Runtime val keyGen: bool -> (string * string)

extern Runtime val boxToObject: 'a -> object
extern Runtime val addBindings: object -> string -> bool
extern Runtime val lookupBindings: object -> option string
extern Runtime val clearBindings: bool -> bool

extern Runtime val Assume: 'P::E -> unit -> (y:unit{'P})
extern Runtime val Assert : 'P::E -> x:unit{'P} -> y:unit{'P}
extern Runtime val lemma : 'P::E -> x:unit{'P} -> z:unit{'P}
extern Runtime val unreachable : x:unit{LBL "unreachable" False} -> 'a
extern Runtime val pickle: x:'a -> (b:bytes{Serialized x b})
extern Runtime val unpickle: b:bytes -> (x:'a{Serialized x b})
extern Runtime val throw: string -> 'a 

(* Primitive functions with trusted specs  *)
val _dummy_op_ColonEquals: ref 'a -> 'a -> unit
val _dummy_op_Dereference: ref 'a -> 'a
val _dummy_op_AmpAmp             : x:bool -> y:bool -> z:bool { z=true =>  x=true &&  y=true}
val _dummy_op_BarBar             : x:bool -> y:bool -> z:bool { (z=true => x=true ||  y=true) && 
                                                                 (z=false => x=false && y=false)}
val _dummy_op_Negation           : x:bool -> y:bool { (y=true => x=false) && (y=false => x=true)}

val _dummy_op_Multiply           : x:int -> y:int -> (z:int{z=(x * y)})
val _dummy_op_Division           : x:int -> y:int{y<>0} -> (z:int{z=(x / y)})
val _dummy_op_Subtraction        : x:int -> y:int -> (z:int{z=(x - y)})
val _dummy_op_Addition           : x:int -> y:int -> (z:int{z=(x + y)})
val _dummy_op_Minus              : x:int -> y:int{y=(Minus x)}
val _dummy_op_Modulus            : x:int -> y:int -> z:int{z=(Modulo x y)}

val _dummy_op_GreaterThanOrEqual : x:int -> y:int -> z:bool{((z=true) ==> (x >= y)) && ((z=false) ==> (x < y))}
val _dummy_op_LessThanOrEqual : x:int -> y:int -> z:bool{((z=true) ==> (x <= y)) && ((z=false) ==> (x > y))}
val _dummy_op_GreaterThan : x:int -> y:int -> z:bool{((z=true) ==> (x > y)) && ((z=false) ==> (x <= y))}
val _dummy_op_LessThan : x:int -> y:int -> z:bool{((z=true) ==> (x < y)) && ((z=false) ==> (x >= y))}
