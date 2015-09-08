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
type Unfold :: E => E
logic tfun type AsE :: 'a::* => 'a => E
type neq :: _ = (fun ('a::*) (x:'a) (y:'a) => l_not (Eq 'a x y))

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
assume Unit_id: forall (x:unit). x=()
type int
type string
type LBL :: string => E => E
type bytes
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
extern Runtime val Assert : 'P::E -> x:unit{'P} -> unit
extern Runtime val lemma : 'P::E -> x:unit{'P} -> z:unit{'P}
extern Runtime val unreachable : x:unit{False} -> 'a
extern Runtime val pickle: x:'a -> (b:bytes{Serialized x b})
extern Runtime val unpickle: b:bytes -> (x:'a{Serialized x b})
extern Runtime val throw: string -> 'a 

(* -------------------------------------------------------------------------------- *)
(* The Dijkstra state monad *)
(* -------------------------------------------------------------------------------- *)
(* The primitive heap of references is modeled using a Select/Update theory *)
type ref :: * => *
logic array(SelHeap, UpdHeap, EmpHeap, InHeap) type heap (* = list (loc * obj) *)
logic val SelHeap : 'a::* -> heap -> ref 'a -> 'a
logic val UpdHeap : 'a::* -> heap -> ref 'a -> 'a -> heap    
logic val EmpHeap : heap
type InHeap :: 'a::* => heap => ref 'a => E
type ST :: _ = fun ('Pre::heap => E) ('a::*) ('Post::result 'a => heap => E) => 
    (h:heap{'Pre h} -> (x:'a * (h':heap{'Post (V x) h'})))
type DST :: _ = fun ('a::*) ('Tx::(result 'a => heap => E) => heap => E) => 
    ('Post::(result 'a => heap => E)
     -> (ST ('Tx 'Post) 'a 'Post))

type UNW :: _ = (fun ('a::*) 
                   ('U::(result 'a => heap => E) => heap => E)
                   ('N::heap => E)
                   ('W::heap => E)
                   ('Post::result 'a => heap => E)
                   (h0:heap) => 
    (not ('W h0) && ('N h0 ==> 'U 'Post h0)))

type returnTX :: _ = 
    fun ('a::*) (x:'a) ('Post::result 'a => heap => E) => 'Post (V x)
type bindTX :: _ = 
    fun ('a::*) ('b::*) 
      ('Tx1::(result 'a => heap => E) => heap => E)
      ('Tx2::'a => (result 'b => heap => E) => heap => E)
      ('Post::result 'b => heap => E) => 
      ('Tx1 (fun (x:result 'a) (h:heap) =>
           (* (forall (e:exn). (x=E e) ==> 'Post (E e) h) && (\* Tx1 raises an exceptions *\) *)
           (* ((x=Err) ==> 'Post Err h) &&                   (\* Tx1 has a fatal error *\) *)
           (forall (v:'a). (x=V v) ==> 'Tx2 v 'Post h)))  (* Tx1 returns normally *)

type returnTX_UNW :: _ = 
    (fun ('a::*) (x:'a) => 
        (UNW 'a 
           (fun ('Post::result 'a => heap => E) (h0:heap) => ('Post (V x) h0))
           (fun (h0:heap) => True)
           (fun (h0:heap) => False)))
       
type bindTX_UNW :: _ = 
    fun ('a::*) ('b::*)
      ('U1::(result 'a => heap => E) => heap => E)
      ('N1::heap => E)
      ('W1::heap => E)
      ('U2::'a => (result 'b => heap => E) => heap => E)
      ('N2::'a => heap => E)
      ('W2::'a => heap => E) => 
    (UNW 'b
       (fun ('P::result 'b => heap => E) =>
           ('U1 (fun (x:result 'a) (h1:heap) => (forall (v:'a). (x=V v) ==> 'U2 v 'P h1))))
       (fun (h0:heap) => ('N1 h0 && ('U1 (fun (x:result 'a) (h1:heap) => (forall (v:'a). (x=V v) ==> 'N2 v h1)) h0)))
       (fun (h0:heap) => ('W1 h0 || ('N1 h0 && ('U1 (fun (x:result 'a) (h1:heap) => ((exists e. x=(E e)) ||
                                                                                     (forall (v:'a). (x=V v) ==> 'W2 v h1))) h0)))))
type Tx2E :: 'a::* => ((result 'a => heap => E) => heap => E) => E
type HeapInv :: heap => E
type DeltaHeap :: heap => heap => E
assume DeltaHeap_trans: forall h1 h2 h3. (DeltaHeap h1 h2 && DeltaHeap h2 h3) ==> DeltaHeap h1 h3
type WithInv :: _ = fun ('a::*) ('Tx::(result 'a => heap => E) => heap => E) ('Post::result 'a => heap => E) (hin:heap) => 
    (HeapInv hin && 'Tx (fun (r:result 'a) (hout:heap) => (HeapInv hout && DeltaHeap hin hout) ==> 'Post r hout) hin)
type iDST :: _ = fun ('a::*) ('Tx::(result 'a => heap => E) => heap => E) => 
    DST 'a (WithInv 'a 'Tx) 
    
type Witness :: heap => E
val get: unit 
  -> DST heap (fun ('Post::result heap => heap => E) h => 'Post (V h) h)
val witness:
     unit
  -> iDST heap (fun ('Post::result heap => heap => E) h => 
      (Witness h ==> 'Post (V h) h))
val recall: 
     unit
  -> iDST unit (fun ('Post::result unit => heap => E) h =>
      (forall (hold:heap). Witness hold ==> DeltaHeap hold h)
      ==> 'Post (V ()) h)
type ResultIs :: _ = fun ('a::*) (r:result 'a) ('T::'a => E) => 
    (forall (x:'a). r=(V x) ==> 'T x)
val ref:
     'a::*
  ->  v:'a
  -> DST (ref 'a) (fun ('Post::result (ref 'a) => heap => E) h => 
      (forall (x:ref 'a). not (InHeap h x)
       ==> 'Post (V x) (UpdHeap h x v)))

val read: 'a::*
  -> r:ref 'a
  -> DST 'a (fun ('Post::result 'a => heap => E) h => 
      'Post (V (SelHeap h r)) h)

val write: 'a::*
  -> r:ref 'a
  -> v:'a 
  -> DST unit (fun ('Post::result unit => heap => E) h => 
      'Post (V ()) (UpdHeap h r v))

val fatal_error: unit -> DST 'a (fun ('Post::result 'a => heap => E) h => 
    'Post Err h)

val raise : e:exn -> DST 'a (fun ('Post::result 'a => heap => E) h => 
    'Post (E e) h)

type WithFinally :: _ = (fun ('a::*)
                           ('Tx2::(result unit => heap => E) => heap => E)
                           ('Post::result 'a => heap => E)
                           (r1:result 'a) (hpre2:heap) =>
    ((r1=Err ==> 'Post r1 hpre2)
     && (r1<>Err ==> ('Tx2 (fun (r2:result unit) (hfinal:heap) =>
                                ((r2=V() ==> 'Post r1 hfinal)
                                 && (forall e. (r2=E e ==> 'Post (E e) hfinal))
                                 && (r2=Err ==> 'Post Err hfinal)))
                              hpre2))))

type TryFinally :: _ = (fun ('a::*) 
                          ('Tx1::(result 'a => heap => E) => heap => E)
                          ('Tx2::(result unit => heap => E) => heap => E)
                          ('Post::result 'a => heap => E) 
                          (hinit:heap) =>
    ('Tx1 (WithFinally 'a 'Tx2 'Post) hinit))
    
val try_finally: 'a::*
  -> 'Tx1::(unit => (result 'a => heap => E) => heap => E)
  -> 'Tx2::(unit => (result unit => heap => E) => heap => E)
  -> (x:unit -> DST 'a ('Tx1 x))
  -> (y:unit -> DST unit ('Tx2 y))
  -> iDST 'a (TryFinally 'a ('Tx1 ()) ('Tx2 ()))
  
val assert_lemma: 'T::E 
  -> unit
  -> DST unit (fun ('Post::result unit => heap => E) h => 
      (LBL "assert_lemma" 'T && ('T ==> 'Post (V ()) h)))

val assume_lemma: 'T::E 
  -> unit
  -> DST unit (fun ('Post::result unit => heap => E) h => 
      ('T ==> 'Post (V ()) h))

val annot_refinement: 'a::*
  -> 'T::('a => E)
  -> x:'a 
  -> DST (x:'a{'T x}) (fun ('Post::result (x:'a{'T x}) => heap => E) h => 
      ('T x && (forall (y:(x:'a{'T x})). Eq x y ==> 'Post (V y) h)))

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


