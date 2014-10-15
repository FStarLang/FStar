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
val op_Equality : x:'a -> y:'a -> z:bool { z=true <=> x=y}

extern reference Runtime { language = "F#";
                           dll="runtime";
                           namespace="Microsoft.FStar.Runtime";
                           classname="Pickler"}

extern Runtime type heap

type ST 'a = heap -> ('a * heap)
val bind_st : ST 'a -> ('a -> ST 'b) -> ST 'b
let bind_st c1 c2 = fun heap ->
  let x, heap' = c1 heap in
    c2 x heap'

val return_st : 'a -> ST 'a
let return_st x = fun h -> (x, h)

extern Runtime type ref :: * => *
extern Runtime val ref : 'a -> ST (ref 'a)
extern Runtime val read : ref 'a -> ST 'a
extern Runtime val write : ref 'a -> ST ('a -> ST unit)

val id : 'a::* -> 'a -> ST 'a
val idprop : 'a::P -> ST ('a -> ST 'a)
val apply: ('a -> ST 'b) -> ST 'a -> ST 'b
val idint: int -> ST int

type option :: * => * =
  | None : option 'a
  | Some : 'a -> option 'a

val bind_opt: ('a -> ST 'b) -> ST (option 'a -> ST (option 'b))
  
type list :: * => * =
  | Nil : list 'a
  | Cons : 'a -> list 'a -> list 'a

val map: ('a -> ST 'b) -> ST (list 'a ->  ST (list 'b))
val fold_left: ('a -> ST ('b -> ST 'a)) -> ST ('a -> ST (list 'b -> 'a))
val fold_right: ('a -> ST ('b -> ST 'b)) -> ST (list 'a -> ST ('b -> ST 'b))
val iterate: ('a -> ST unit) -> ST (list 'a -> ST unit)

(* val assoc: 'a -> list ('a*'b) -> option 'b *)
(* val append: x:list 'a -> y:list 'a -> z:list 'a { forall (a:'a). In a z <=> (In a x || In a y)} *)
(* val concatMap: ('a -> list 'b) -> list 'a -> list 'b *)

extern reference String {language="C#";
                         dll="mscorlib";
                         namespace="System";
                         classname="String"}

(* extern String val Concat: string -> string -> string *)

(* val ConcatList: string -> list string -> string *)
(* let rec ConcatList sep l = match l with  *)
(*   | [] -> "" *)
(*   | hd::tl ->  *)
(*       let tl = ConcatList sep tl in *)
(*         if tl="" then hd *)
(*         else Concat (Concat hd sep) tl *)


extern reference SysConvert {language="C#";
                             dll="mscorlib";
                             namespace="System";
                             classname="Convert"}
(* extern SysConvert val ToBase64String : bytes -> string *)
(* extern SysConvert val FromBase64String : string -> bytes *)


(* type Serialized :: 'a::* => 'a => bytes => E *)

(* extern Runtime type punit :: P *)
(* extern Runtime val freshname : bool -> string *)
(* extern Runtime val debug_println : string -> bool *)
(* extern Runtime val println : string -> bool *)
(* extern Runtime val printfile: string -> string -> bool *)
(* extern Runtime val printfileNoLn: string -> string -> bool *)
(* extern Runtime val print_stderr : string -> bool *)
(* extern Runtime val print_string : string -> bool *)
(* extern Runtime val string_of_any : 'a -> string *)
(* extern Runtime val string_of_any_for_coq : 'a -> string *)
(* extern Runtime val string_of_any_for_coq_afn : 'a -> string *)
(* extern Runtime val writeToFile : string -> 'a -> string *)
(* extern Runtime val writeCertToFile : string -> 'a -> string *)
(* extern Runtime val print_int : int -> bool *)
(* extern Runtime val strcat : string -> string -> string *)

(* extern Runtime val boxToObject: 'a -> object *)
(* extern Runtime val addBindings: object -> string -> bool *)
(* extern Runtime val lookupBindings: object -> option string *)
(* extern Runtime val clearBindings: bool -> bool *)

(* extern Runtime val Assume: 'P::E -> unit -> (y:unit{'P}) *)
(* extern Runtime val PAssume: 'P::E -> int -> (y:punit{'P}) *)
(* extern Runtime val pickle: x:'a -> (b:bytes{Serialized x b}) *)
(* extern Runtime val unpickle: b:bytes -> (x:'a{Serialized x b}) *)
(* extern Runtime val assert : 'P::E -> x:unit{'P} -> (y:unit{'P}) *)
(* extern Runtime val throw: string -> 'a  *)

(* val loop : unit -> 'a *)
(* let rec loop x = loop x *)

val raise: string -> ST 'a
(* let raise s =  *)
(*   println "Exception!"; *)
(*   throw s *)



(* Primitive functions with trusted specs for concrete refinements *)
val _dummy_op_AmpAmp             : x:bool -> y:bool -> z:bool { z=true =>  x=true &&  y=true}
val _dummy_op_BarBar             : x:bool -> y:bool -> z:bool { (z=true => x=true ||  y=true) && 
                                                                (z=false => x=false && y=false)}
val _dummy_op_Multiply           : int -> int -> int
val _dummy_op_Division           : int -> int -> int
val _dummy_op_Subtraction        : int -> int -> int
val _dummy_op_Addition           : int -> int -> int
val _dummy_op_GreaterThanOrEqual : int -> int -> bool
val _dummy_op_GreaterThan        : int -> int -> bool
val _dummy_op_Negation           : x:bool -> y:bool { (y=true => x=false) && (y=false => x=true)}
val _dummy_op_Modulus		 : int -> int -> int
