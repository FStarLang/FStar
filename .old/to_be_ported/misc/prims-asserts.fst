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
  | LiftPf           : 'P::P -> pf 'P
  | BindPf           : 'P::P -> 'Q::P -> pf 'P  -> ('P -> pf 'Q) -> pf 'Q
  | Reflexivity      : x:'a -> pf (Eq 'a x x)
  | Symmetry         : x:'a -> y:'a -> pf (Eq 'a x y) -> pf (Eq 'a y x)
  | Transitivity     : x:'a -> y:'a -> z:'a -> pf (Eq 'a x y) -> pf (Eq 'a y z) -> pf (Eq 'a x z)
  | MonoProp         : 'c::* -> 'P::('c => P) -> x:'c -> y:'c -> pf (Eq 'c x y) -> pf (l_iff (pf ('P x)) (pf ('P y)))
  | ExcMiddle        : 'P::P -> pf (l_or (pf (l_not (pf 'P))) (pf 'P))
  | DestructFalse    : 'P::P -> pf False -> pf 'P
  | OrIntro1         : 'P::P -> 'Q::P -> pf 'P -> pf (l_or (pf 'P) (pf 'Q))
  | OrIntro2         : 'P::P -> 'Q::P -> pf 'Q -> pf (l_or (pf 'P) (pf 'Q))
  | OrElim           : 'P::P -> 'Q::P -> 'R::P 
                         -> pf (l_or (pf 'P) (pf 'Q))
                         -> pf (l_implies (pf 'P) (pf 'R))
                         -> pf (l_implies (pf 'Q) (pf 'R))
                         -> pf 'R
  | AndIntro         : 'P::P -> 'Q::P -> pf 'P -> pf 'Q -> pf (l_and (pf 'P) (pf 'Q))
  | AndElim1         : 'P::P -> 'Q::P -> pf (l_and (pf 'P) (pf 'Q)) -> pf 'P
  | AndElim2         : 'P::P -> 'Q::P -> pf (l_and (pf 'P) (pf 'Q)) -> pf 'Q
  | ImpliesIntro     : 'P::P -> 'Q::P -> (pf 'P -> pf 'Q) -> pf (l_implies (pf 'P) (pf 'Q))
  | ModusPonens      : 'P::P -> 'Q::P -> pf 'P -> pf (l_implies (pf 'P) (pf 'Q)) -> pf 'Q
  | IffIntro         : 'P::P -> 'Q::P -> pf (l_implies (pf 'P) (pf 'Q)) -> pf (l_implies (pf 'Q) (pf 'P)) -> pf (l_iff (pf 'P) (pf 'Q))
  | IffElim1         : 'P::P -> 'Q::P -> pf (l_iff (pf 'P) (pf 'Q)) -> pf (l_implies (pf 'P) (pf 'Q))
  | IffElim2         : 'P::P -> 'Q::P -> pf (l_iff (pf 'P) (pf 'Q)) -> pf (l_implies (pf 'Q) (pf 'P))
  | NotAll_existsNot : 'a::* -> 'P::('a => P) -> pf (l_iff 
                                                       (pf (l_not (pf (Exists 'a (fun (x:'a) => pf ('P x)))))) 
                                                       (pf (Exists 'a (fun (x:'a) => pf (l_not (pf ('P x)))))))
  | DblNotElim       : 'P::P -> pf (l_not (pf (l_not (pf 'P)))) -> pf 'P
  | DblNotElimRev    : 'P::P -> pf 'P -> pf (l_not (pf (l_not (pf 'P))))
  (* why are these next four already promoted into pf? *)
  | TupleProj1       : pf (x:'a -> pf (y:'b -> pf (Eq 'a ((x,y).One) x)))    (* TODO: generalize this to dependent tuples? 'b::'a => * *)
  | TupleProj2       : pf (x:'a -> pf (y:'b -> pf (Eq 'b ((x,y).Two) y)))
  | TupleEq1         : pf (x:('a*'b) -> pf (y:('a*'b) -> pf (l_implies (pf (Eq ('a*'b) x y)) (pf (Eq 'a (x.One) (y.One))))))
  | TupleEq2         : pf (x:('a*'b) -> pf (y:('a*'b) -> pf (l_implies (pf (Eq ('a*'b) x y)) (pf (Eq 'b (x.Two) (y.Two))))))
  | TupleMonoEq      : x1:'a -> x2:'a -> y1:'b -> y2:'b -> pf (Eq 'a x1 x2) -> pf (Eq 'b y1 y2) -> pf (Eq ('a*'b) (x1,y1) (x2,y2))
  (* TODO: All the rest should be derivable *)
  | PullQuantAnd     : 'a::* -> 'P::P -> 'Q::('a => P) -> pf (l_and (pf 'P) (pf (x:'a -> pf ('Q x)))) -> pf (x:'a -> pf (l_and (pf 'P) (pf ('Q x))))
  | PullQuantOr      : 'a::* -> 'P::P -> 'Q::('a => P) -> pf (l_or (pf 'P) (pf (x:'a -> pf ('Q x)))) -> pf (x:'a -> pf (l_or (pf 'P) (pf ('Q x))))
  | ElimUnused       : 'a::* -> 'P::P -> pf (l_iff (pf (x:'a -> pf 'P)) (pf 'P))
  | PullQuantAndE    : 'a::* -> 'P::P -> 'Q::('a => P) 
                     -> pf (l_and (pf 'P) 
                                  (pf (Exists 'a (fun (x:'a) => (pf ('Q x))))))
                     -> pf (Exists 'a (fun (x:'a) => pf (l_and (pf 'P) (pf ('Q x)))))
  | PullQuantOrE     : 'a::* -> 'P::P -> 'Q::('a => P) 
                     -> pf (l_or (pf 'P) (pf (Exists 'a (fun (x:'a) => (pf ('Q x))))))
                     -> pf (Exists 'a (fun (x:'a) => pf (l_or (pf 'P) (pf ('Q x)))))
  | EqIff            : x:'a -> y:'a -> pf (l_iff (pf (Eq 'a x y)) (pf (Eq 'a y x)))
  | EqMono           : x1:'a -> y1:'a -> x2:'a -> y2:'a -> pf (Eq 'a x1 y1) -> pf (Eq 'a x2 y2) -> pf (l_iff (pf (Eq 'a x1 x2)) (pf (Eq 'a y1 y2)))
  | AndTrue          : 'P::P -> pf (l_iff (pf (l_and (pf 'P) (pf True)))  (pf 'P))
  | OrFalse          : 'P::P -> pf (l_or  (pf 'P) (pf False)) -> pf 'P
  | OrFalseRev       : 'P::P -> pf 'P -> pf (l_or (pf False) (pf 'P))
  | Contra           : 'P::P -> pf (l_and (pf 'P) (pf (l_not (pf 'P)))) -> pf False
  | DeMorganNotAnd   : 'P::P -> 'Q::P -> pf (l_not (pf (l_and (pf 'P) (pf 'Q)))) -> pf (l_or (pf (l_not (pf 'P))) (pf (l_not (pf 'Q))))
  | DeMorganOr       : 'P::P -> 'Q::P -> pf (l_or (pf 'P) (pf 'Q)) -> pf (l_not (pf (l_and (pf (l_not (pf 'P))) (pf (l_not (pf 'Q))))))
  | DeMorganNotOr    : 'P::P -> 'Q::P -> pf (l_not (pf (l_or (pf 'P) (pf 'Q)))) -> pf (l_and (pf (l_not (pf 'P))) (pf (l_not (pf 'Q))))
  | DeMorganAnd      : 'P::P -> 'Q::P -> pf (l_and (pf 'P) (pf 'Q)) -> pf (l_not (pf (l_or (pf (l_not (pf 'P))) (pf (l_not (pf 'Q))))))
  | Distribute       : 'P::P -> 'Q::P -> 'R::P 
                         -> pf (l_and (pf (l_or (pf 'P) (pf 'Q))) (pf 'R))
                         -> pf (l_or  (pf (l_and (pf 'P) (pf 'R))) (pf (l_and (pf 'Q) (pf 'R))))
  | IdImplies        : 'P::P -> 'Q::P -> pf (l_implies (pf 'P) (pf 'Q)) -> pf (l_or (pf (l_not (pf 'P))) (pf 'Q))
  | IdImpliesRev     : 'P::P -> 'Q::P -> pf (l_or (pf 'P) (pf 'Q)) -> pf (l_implies (pf (l_not (pf 'P))) (pf 'Q))
  | MonoNot          : 'P::P -> 'Q::P -> pf (l_not (pf 'P)) -> pf (l_implies (pf 'P) (pf 'Q)) -> pf (l_not (pf 'Q))
  | MonoAnd          : 'P1::P -> 'Q1::P -> 'P2::P -> 'Q2::P 
                         -> pf (l_and (pf 'P1) (pf 'Q1))
                         -> pf (l_implies (pf 'P1) (pf 'P2))
                         -> pf (l_implies (pf 'Q1) (pf 'Q2))
                         -> pf (l_and (pf 'P2) (pf 'Q2))
  | MonoOr           : 'P1::P -> 'Q1::P -> 'P2::P -> 'Q2::P 
                         -> pf (l_or (pf 'P1) (pf 'Q1))
                         -> pf (l_implies (pf 'P1) (pf 'P2))
                         -> pf (l_implies (pf 'Q1) (pf 'Q2))
                         -> pf (l_or (pf 'P2) (pf 'Q2))
  | MonoOrIff        : 'P1::P -> 'P2::P -> 'P::P 
                         -> pf (l_iff (pf 'P1) (pf 'P2))
                         -> pf (l_iff (pf (l_or (pf 'P) (pf 'P1)))
                                      (pf (l_or (pf 'P) (pf 'P2))))
  | MonoImplies      : 'P1::P -> 'Q1::P -> 'P2::P -> 'Q2::P 
                         -> pf (l_implies (pf 'P1) (pf 'Q1))
                         -> pf (l_implies (pf 'P1) (pf 'P2))
                         -> pf (l_implies (pf 'Q1) (pf 'Q2))
                         -> pf (l_implies (pf 'P2) (pf 'Q2))
type object
type bool
type unit
type int
type string
type bytes
val op_Equality : x:'a -> y:'a -> z:bool { z=true <=> x=y}

val id : 'a::* -> 'a -> 'a
let id x = x

val idprop : 'a::P -> 'a -> 'a
let idprop x = x

val apply: ('a -> 'b) -> 'a -> 'b
let apply f x = f x

val idint: int -> int
let idint x = id x

type option :: * => * =
  | None : option 'a
  | Some : 'a -> option 'a

val bind_opt: ('a -> 'b) -> option 'a -> option 'b
let bind_opt f x = match x with
  | None -> None
  | Some x -> Some (f x)
  
type list :: * => * =
  | Nil : list 'a
  | Cons : 'a -> list 'a -> list 'a

type In :: 'a::* => 'a => list 'a => P
type ListUnion :: 'a::* => list 'a => list 'a => list 'a => P
(* type SetEq :: 'a::* => list 'a => list 'a => P *)
(* assume seqEqDef:forall (l1:list 'a) (l2:list 'a). (forall x. In x l1 <=> In x l2) => SetEq l1 l2 *)
assume In_hd: forall (hd:'a) (tl:list 'a). (In hd (Cons hd tl))
assume In_tl: forall (hd:'a) (x:'a) (tl:list 'a). (In x tl) => (In x (Cons hd tl))
assume notinNil: forall (x:'a). not (In x Nil)
assume notinCons: forall (x:'a) (y:'a) (tl:list 'a). ((not (In x tl)) && (not (x=y))) => not (In x (Cons y tl))


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

val append: x:list 'a -> y:list 'a -> z:list 'a { forall (a:'a). In a z <=> (In a x || In a y)}
let rec append x y = match x with
  | Nil -> y
  | Cons a tl -> Cons a (append tl y)

val concatMap: ('a -> list 'b) -> list 'a -> list 'b
let rec concatMap f = function
  | [] -> []
  | a::tl -> append (f a) (concatMap f tl)

extern reference String {language="C#";
                         dll="mscorlib";
                         namespace="System";
                         classname="String"}

extern String val Concat: string -> string -> string

val ConcatList: string -> list string -> string
let rec ConcatList sep l = match l with 
  | [] -> ""
  | hd::tl -> 
      let tl = ConcatList sep tl in
        if tl="" then hd
        else Concat (Concat hd sep) tl


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
extern Runtime val writeToFile : string -> 'a -> string
extern Runtime val writeCertToFile : string -> 'a -> string
extern Runtime val print_int : int -> bool
extern Runtime val strcat : string -> string -> string

extern Runtime val boxToObject: 'a -> object
extern Runtime val addBindings: object -> string -> bool
extern Runtime val lookupBindings: object -> option string
extern Runtime val clearBindings: bool -> bool

extern Runtime val Assume: 'P::E -> unit -> (y:bool{'P})
extern Runtime val PAssume: 'P::E -> int -> (y:punit{'P})
extern Runtime val Assert : 'P::E -> x:unit{'P} -> (y:bool{'P})
extern Runtime val pickle: x:'a -> (b:bytes{Serialized x b})
extern Runtime val unpickle: b:bytes -> (x:'a{Serialized x b})
extern Runtime val throw: string -> 'a 

val loop : unit -> 'a
let rec loop x = loop x

val raise: string -> 'a
let raise s = 
  println "Exception!";
  throw s

type ref :: * => *
val ref : v:'a -> ref 'a
val read : r:ref 'a -> 'a
val write : r:ref 'a -> v:'a -> unit

(* Primitive functions with trusted specs for concrete refinements *)
val _dummy_op_AmpAmp             : x:bool -> y:bool -> z:bool { z=true =>  x=true &&  y=true}
val _dummy_op_BarBar             : x:bool -> y:bool -> z:bool { (z=true => x=true ||  y=true) && 
                                                                 (z=false => x=false && y=false)}
val _dummy_op_Multiply           : int -> int -> int
val _dummy_op_Division           : int -> x:int{x<>0} -> int
val _dummy_op_Subtraction        : int -> int -> int
val _dummy_op_Addition           : int -> int -> int
val _dummy_op_GreaterThanOrEqual : int -> int -> bool
val _dummy_op_Negation           : x:bool -> y:bool { (y=true => x=false) && (y=false => x=true)}
