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

type EqTyp :: E => E => E
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
val op_Equality : x:'a -> y:'a -> z:bool {z=true <=> x=y}

type option :: * => * =
  | None : option 'a
  | Some : 'a -> option 'a

type list :: * => * =
  | Nil : list 'a
  | Cons : 'a -> list 'a -> list 'a

val assert_false : 'a::* -> u:unit{False} -> 'a

extern reference Runtime { language = "F#";
                           dll="runtime";
                           namespace="Microsoft.FStar.Runtime";
                           classname="Pickler"}
extern Runtime val Assume: 'P::E -> unit -> (y:unit{'P})
extern Runtime val Assert : 'P::E -> x:unit{'P} -> (y:unit{'P})

(* -------------------------------------------------------------------------------- *)

type fieldname = string
type obj
type undef
type heap

type dyn = 
  | Undef : d:dyn{EqTyp (GetType d) undef}

  | Str   : string -> d:dyn{EqTyp (GetType d) string}

  | Int   : int -> d:dyn{EqTyp (GetType d) int}

  | Obj   : obj -> d:dyn{EqTyp (GetType d) obj}

  | Fun   : 'Pre::(dyn => dyn => (dyn => heap => E) => heap => E)
         -> (this:dyn -> args:dyn  
         -> ('Post::(dyn => heap => E) -> h:heap{'Pre this args 'Post h} -> (x:dyn * (h':heap{'Post x h'}))))
         -> d:dyn{EqTyp (GetType d) (Function 'Pre)}

and GetType :: dyn => E 

(* and heap = *)
(*   | MkHeap : list (obj * list (fieldname * heapcell)) -> heap *)

and heapcell = 
  | MkCell : 'a::E -> d:dyn{EqTyp (GetType d) 'a} -> heapcell

and Function :: (dyn => dyn => (dyn => heap => E) => heap => E) => E

type fields = list (fieldname * heapcell)
type ST :: _ = (fun ('Pre::heap => E) ('a::*) ('Post::'a => heap => E) => h:heap{'Pre h} -> (x:'a * (h':heap{'Post x h'})))

type PST :: _ = fun ('a::*) ('Tx::('a => heap => E) => heap => E) => ('Post::('a => heap => E) -> ST ('Tx 'Post) 'a 'Post)


type dobj = d:dyn{EqTyp (GetType d) obj}

type tri = 
  | NoObj : tri
  | NoField : tri
  | Val : heapcell -> tri 

logic function SelectTT : heap -> dyn -> fieldname -> tri
val selecttt : h:heap -> d:dobj -> f:fieldname -> c:tri{c=(SelectTT h d f)}

logic function Select : heap -> dyn -> fieldname -> dyn 
assume forall ('a::E) h d f v.  ((SelectTT h d f)=(Val (MkCell<'a> v)))=> ((Select h d f)=v)

logic function Allocd : heap -> dyn -> fieldname -> bool 
assume forall ('a :: E) h d f v.  ((SelectTT h d f)=(Val (MkCell<'a> v)) => ((Allocd h d f)=true))

type SelectTyp :: heap => dyn => fieldname => E
assume forall ('a::E) h d f v. ((SelectTT h d f)=(Val (MkCell<'a> v)) => (EqTyp (SelectTyp h d f) 'a))

type InDomain :: heap => dyn => E
type HasField :: _ = (fun h d f => ((Allocd h d f)=true))
type Typed :: _ = (fun o ('a::E) => (EqTyp (GetType o) 'a))
type IsObject :: _ = (fun h o => ((Typed o object) && InDomain h o))

logic function Update : 'a::E -> heap -> dyn -> fieldname -> dyn -> heap
val updatefun : 'a::E -> h1:heap -> o:dyn{InDomain h1 o} -> f:fieldname -> v:dyn -> h2:heap{h2=(Update<'a> h1 o f v)}

val mkInt : i:int -> d:dyn{(EqTyp (GetType d) int) && (d=(Int i))}
val global : obj

(* ******************************************************************************** *)

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

end

module PrimsImpl

type updateTX :: _ = fun o f v ('Post::dyn => heap => E) h => 
    ((IsObject h o) && 
     (forall h'. (h'=(Update<(GetType v)> h o f v)) => 'Post Undef h'))
val update: o:dyn
         -> f:string 
         -> v:dyn
         -> PST dyn (updateTX o f v)
let update o f v =
  let impl 'Post::dyn=>heap=>E (h:heap{updateTX o f v 'Post h}) : (d:dyn * h:heap{'Post d h}) =
    match v with 
      | Undef -> let h' = updatefun<undef> h o f v in (Undef, h')
      | Str _ -> let h' = updatefun<string> h o f v in (Undef, h')
      | Int _ -> let h' = updatefun<int> h o f v in (Undef, h')
      | Obj _ -> let h' = updatefun<obj> h o f v in (Undef, h')
      | Fun 'Pre _ -> let h' = updatefun<Function 'Pre> h o f v in (Undef, h') in
  impl
          
type selectTX :: _ = fun o f ('Post::dyn => heap => E) h => 
    ((Typed o obj) && 
     (HasField h o f) &&                                                           
     (forall r. ((r=(Select h o f)) && (Typed r (SelectTyp h o f))) => 'Post r h))
val select: o:dyn
         -> f:string 
         -> PST dyn (selectTX o f)
let select o f = 
  let impl 'Post::dyn => heap => E (h:heap{selectTX o f 'Post h}) : (d:dyn * h:heap{'Post d h}) =
    match o with 
      | Obj _ -> 
          (match selecttt h o f with 
             | Val c -> (match c with | MkCell 'T v -> assume ('Post v h); (* Z3 proves from the command line, but fails from the API :( *)(v, h))
             | NoObj -> assert_false () (* since we have HasField h o f*)
             | NoField -> assert_false ())
      | Undef -> assert_false() (* since we have (Typed o obj) *)
      | Str _ -> assert_false() 
      | Int _ -> assert_false()
      | Fun _ -> assert_false() in 
    impl
    
type existsTx :: ((dyn => dyn => (dyn => heap => E) => heap => E) => E) => E 

type applyTX :: _ = 
    fun f this args ('Post::dyn => heap => E) h => 
      (existsTx (fun ('PreF::(dyn => dyn => (dyn => heap => E) => heap => E)) =>
       ((Typed f (Function 'PreF)) && ('PreF args this 'Post h))))
val apply:  f:dyn
         -> this:dyn 
         -> args:dyn 
         -> PST dyn (fun ('Post::dyn => heap => E) h => 
             (existsTx (fun ('Tx::(dyn => dyn => (dyn => heap => E) => heap => E)) => 
                  (Typed f (Function 'Tx) && ('Tx args this 'Post h)))))
let apply f this args = 
  let impl 'Post::dyn => heap => E (h:heap{applyTX f this args 'Post h}) : (d:dyn * h:heap{'Post d h}) =
    match f with 
      | Fun 'Pre fn -> (*     existsTx 'Tx. (GetType f)=(Function 'Tx) /\ 
                                            'Tx ...
                          /\  Typed f (Function 'Pre)
                         ---------------------------------------------
                              'Pre ... 
                       *)
          assume ('Pre args this 'Post h);
          let g = fn this args in 
            g<'Post> h
      | Obj _ -> assert_false ()
      | Str _ -> assert_false ()
      | Int _ -> assert_false ()
      | Undef -> assert_false () in 
    impl
          
end
