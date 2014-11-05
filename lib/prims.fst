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

kind Unop  = Type -> Type           (* simple kind abbreviation *)
kind Binop = Type -> Type -> Type   

(* Primitive logical connectives *)
logic type l_not : Unop  (* prefix unary '~' *)
logic type l_and : Binop (* infix binary '/\' *)
logic type l_or  : Binop (* infix binary '\/' *)
logic type l_iff : Binop (* infix binary '<==>' *)
logic type l_imp : Binop (* infix binary '==>' *)
logic type Forall : #'a:Type -> ('a -> Type) -> Type 
logic type Exists : #'a:Type -> ('a -> Type) -> Type 
logic type ForallTyp : (Type -> Type) -> Type (* Handled specially to support quantification over types of arbitrary kinds *)
logic type ExistsTyp : (Type -> Type) -> Type (* Handled specially to support quantification over types of arbitrary kinds *)
logic type True 
logic type False
logic type EqTyp : Type -> Type -> Type                    (* infix binary '==' *)
logic type Eq2 : #'a:Type -> #'b:Type -> 'a -> 'b -> Type  (* infix binary '==' *)
logic type XOR 'P 'Q = ('P \/ 'Q) /\ ~('P /\ 'Q)
logic type ITE : Type -> Type -> Type -> Type (* written if/then/else in concrete syntax *)
logic type Precedes : #'a:Type -> #'b:Type -> 'a -> 'b -> Type  (* a built-in well-founded partial order over all terms *)

monad_lattice { (* The definition of the PURE effect is fixed; no user should ever change this *)
  PURE::
             terminating
             kind Pre = Type
             kind Post ('a:Type) = 'a -> Type
             kind WP ('a:Type) = Post 'a -> Pre
             type return ('a:Type) (x:'a) ('p:Post 'a) = 'p x
             type bind_wp  ('a:Type) ('b:Type) ('wp1:WP 'a) ('wlp1:WP 'a) 
                                               ('wp2: 'a -> WP 'b) ('wlp2:'a -> WP 'b) 
                                               ('p:Post 'b) = 'wp1 (fun a -> 'wp2 a 'p)
             type bind_wlp ('a:Type) ('b:Type) ('wlp1:WP 'a) 
                                               ('wlp2:'a -> WP 'b) 
                                               ('p:Post 'b) = 'wlp1 (fun a -> 'wlp2 a 'p)
             type if_then_else ('a:Type) ('p:Type) ('wp_then:WP 'a) ('wp_else:WP 'a) ('post:Post 'a) = 
                 (if 'p 
                  then 'wp_then 'post
                  else 'wp_else 'post)
             type ite_wlp ('a:Type) ('wlp_cases:WP 'a) ('post:Post 'a) =
                 (forall (a:'a). 'wlp_cases (fun a' -> a=!=a') \/ 'post a)
             type ite_wp ('a:Type) ('wlp_cases:WP 'a) ('wp_cases:WP 'a) ('post:Post 'a) =
                 (forall (a:'a). 'wlp_cases (fun a' -> a=!=a') \/ 'post a)
                 /\ ('wp_cases (fun a -> True))
             type wp_binop ('a:Type) ('wp1:WP 'a) ('op:Type -> Type -> Type) ('wp2:WP 'a) ('p:Post 'a) =
                 'op ('wp1 'p) ('wp2 'p)
             type wp_as_type ('a:Type) ('wp:WP 'a) = (forall ('p:Post 'a). 'wp 'p)
             type close_wp ('a:Type) ('b:Type) ('wp:'b -> WP 'a) ('p:Post 'a) = (forall (b:'b). 'wp b 'p)
             type close_wp_t ('a:Type) ('wp:Type -> WP 'a) ('p:Post 'a) = (forall ('b:Type). 'wp 'b 'p)
             type assert_p ('a:Type) ('P:Type) ('wp:WP 'a) ('p:Post 'a) = ('P /\ 'wp 'p)
             type assume_p ('a:Type) ('P:Type) ('wp:WP 'a) ('p:Post 'a) = ('P ==> 'wp 'p)
             type null_wp ('a:Type) ('p:Post 'a) = (forall (x:'a). 'p x)
             type trivial ('a:Type) ('wp:WP 'a) = 'wp (fun x -> True)
             with Pure ('a:Type) ('pre:Pre) ('post:Post 'a) =
                 PURE 'a
                   (fun ('p:Post 'a) -> 'pre /\ (forall a. 'post a ==> 'p a)) (* WP *)
                   (fun ('p:Post 'a) -> forall a. 'pre /\ 'post a ==> 'p a)   (* WLP *)
             and Fact ('res:Type) ('p:Type) = Pure 'res True (fun r -> 'p)
             (* and PURE ('a:Type) ('wp:WP 'a) ('wlp:WP 'a) =  *)
             (*     Pure 'a ('wp (fun a -> True)) (fun a -> 'wlp (fun a' -> a==a')) *)
             and Tot ('a:Type) =
                 PURE 'a (fun 'p -> (forall (x:'a). 'p x)) (fun 'p -> (forall (x:'a). 'p x))
}
open Prims.PURE
assume type bool
assume type unit
assume type int
assume type char
assume type byte
assume type uint16
assume type int64
assume type float
assume type string
assume type array : Type -> Type
assume type ref : Type -> Type
assume logic type LBL : string -> Type -> Type
assume type bytes
assume type exn
assume type HashMultiMap : Type -> Type -> Type
type double = float
type int32 = int
logic type b2t (b:bool) = b==true

type option 'a =
  | None : option 'a
  | Some : v:'a -> option 'a

assume type heap
assume logic val SelHeap : #'a:Type -> heap -> ref 'a -> Tot 'a
assume logic val UpdHeap : #'a:Type -> heap -> ref 'a -> 'a -> Tot heap
assume logic val EmpHeap : heap
assume logic val InHeap  : #'a:Type -> heap -> ref 'a -> Tot bool
logic type HeapEq : heap -> heap -> Type
assume SelUpd1: forall ('a:Type) (h:heap) (x:ref 'a) (v:'a).{:pattern (SelHeap (UpdHeap h x v) x)} SelHeap (UpdHeap h x v) x == v
assume SelUpd2: forall ('a:Type) ('b:Type) (h:heap) (x:ref 'a) (y:ref 'b) (v:'b).{:pattern (SelHeap (UpdHeap h y v) x)} y=!=x ==> SelHeap (UpdHeap h y v) x == SelHeap h x
assume InHeap1:  forall ('a:Type) (h:heap) (x:ref 'a) (v:'a).{:pattern (InHeap (UpdHeap h x v) x)} InHeap (UpdHeap h x v) x == true
assume InHeap2:  forall ('a:Type) ('b:Type) (h:heap) (x:ref 'a) (y:ref 'b) (v:'b).{:pattern (InHeap (UpdHeap h y v) x)} y=!=x ==> InHeap (UpdHeap h y v) x == InHeap h x
assume HeapEqDef:    forall (h1:heap) (h2:heap).{:pattern HeapEq h1 h2} (forall ('a:Type) (r:ref 'a). SelHeap h1 r == SelHeap h2 r) ==> HeapEq h1 h2
assume HeapEqExt:    forall (h1:heap) (h2:heap).{:pattern HeapEq h1 h2} HeapEq h1 h2 ==> h1==h2
assume HeapEqRefl:   forall (h:heap).{:pattern HeapEq h h} HeapEq h h

assume type set : Type -> Type
assume logic val EmptySet : 'a:Type -> Tot (set 'a)
assume logic val Singleton : 'a:Type -> 'a -> Tot (set 'a)
assume logic val Union : 'a:Type -> set 'a -> set 'a -> Tot (set 'a)
assume logic val Intersection : 'a:Type -> set 'a -> set 'a -> Tot (set 'a)
logic type InSet : #'a:Type -> 'a -> set 'a -> Type
logic type SetEqual : #'a:Type -> set 'a -> set 'a -> Type
logic type Subset : #'a:Type -> set 'a -> set 'a -> Type
logic type SubsetEq : #'a:Type -> set 'a -> set 'a -> Type = fun ('a:Type) (s1:set 'a) (s2:set 'a) -> (SetEqual s1 s2 \/ Subset s1 s2)
logic type Supset   : #'a:Type -> set 'a -> set 'a -> Type = fun ('a:Type) (s1:set 'a) (s2:set 'a) -> Subset s2 s1
logic type SupsetEq : #'a:Type -> set 'a -> set 'a -> Type = fun ('a:Type) (s1:set 'a) (s2:set 'a) -> (SetEqual s1 s2 \/ Supset s1 s2)
assume InEmptySet:     forall 'a (a:'a).{:pattern InSet a EmptySet} ~(InSet a EmptySet)
assume InSingleton:    forall 'a (a:'a).{:pattern InSet a (Singleton a)} InSet a (Singleton a)
assume InSingletonInv: forall 'a (a:'a) (b:'a).{:pattern InSet a (Singleton b)} InSet a (Singleton b) <==> a==b
assume InUnion:        forall 'a s1 s2 (a:'a).{:pattern InSet a (Union s1 s2)} InSet a (Union s1 s2) <==> (InSet a s1 \/ InSet a s2)
assume InUnionL:       forall 'a s1 s2 (a:'a).{:pattern InSet a (Union s1 s2)} InSet a s1 ==> InSet a (Union s1 s2)
assume InUnionR:       forall 'a s1 s2 (a:'a).{:pattern InSet a (Union s1 s2)} InSet a s2 ==> InSet a (Union s1 s2)
assume UnionIdemL:     forall 'a (s1:set 'a) (s2:set 'a).{:pattern Union (Union s1 s2) s2} Union (Union s1 s2) s2 == Union s1 s2
assume UnionIdemR:     forall 'a (s1:set 'a) (s2:set 'a).{:pattern Union s1 (Union s1 s2)} Union s1 (Union s1 s2) == Union s1 s2
(* assume InInter:        forall 'a s1 s2 (a:'a). {:pattern InSet a (Intersection s1 s2)} InSet a (Intersection s1 s2) <==> (InSet a s1 /\ InSet a s2) *)
assume InInter:        forall 'a s1 s2 (a:'a). InSet a (Intersection s1 s2) <==> (InSet a s1 /\ InSet a s2)
assume InterIdemL:     forall 'a (s1:set 'a) (s2:set 'a).{:pattern Intersection (Intersection s1 s2) s2}  Intersection (Intersection s1 s2) s2 == Intersection s1 s2
assume InterdemR:      forall 'a (s1:set 'a) (s2:set 'a).{:pattern Intersection s1 (Intersection s1 s2)} Intersection s1 (Intersection s1 s2) == Intersection s1 s2
assume SetEqualDef:    forall 'a (s1:set 'a) (s2:set 'a).{:pattern SetEqual s1 s2} (forall (a:'a). InSet a s1 <==> InSet a s2) ==> SetEqual s1 s2 
assume SetEqualExt:    forall 'a (s1:set 'a) (s2:set 'a).{:pattern SetEqual s1 s2} SetEqual s1 s2 ==> s1==s2
assume SetEqualExt:    forall 'a (s:set 'a).{:pattern SetEqual s s} SetEqual s s
assume SubsetDef:      forall 'a (s1:set 'a) (s2:set 'a).{:pattern Subset s1 s2} (forall (a:'a).{:pattern InSet a s1} InSet a s1 ==> InSet a s2) ==> Subset s1 s2 

type aref = 
  | Ref : 'a:Type -> r:ref 'a -> aref

type refs =
  | AllRefs : refs
  | SomeRefs : v:set aref -> refs

(* let oneref (r:ref 'a) = Singleton (Ref r) *)

logic type Modifies (mods:refs) (h:heap) (h':heap) =
    (if b2t (is_AllRefs mods)
     then True
     else forall 'b (x:ref 'b). (b2t (InHeap h x) /\ ~(InSet (Ref x) (SomeRefs.v mods))) ==> (b2t (InHeap h' x) /\ SelHeap h x==SelHeap h' x))

type result : Type -> Type =
  | V : 'a:Type -> v:'a -> result 'a
  | E : 'a:Type -> e:exn -> result 'a
  | Err : 'a:Type -> msg:string -> result 'a

monad_lattice { (* STATE a wp wlp *)
  STATE::
             kind Pre     = heap -> Type
             kind Post ('a:Type) = 'a -> heap -> Type
             kind WP ('a:Type) = Post 'a -> Pre
             type return   ('a:Type) (x:'a) ('p:Post 'a) = 'p x
             type bind_wp  ('a:Type) ('b:Type) ('wp1:WP 'a) ('wlp1:WP 'a) ('wp2:'a -> WP 'b) ('wlp2:'a -> WP 'b) ('p:Post 'b) (h0:heap) = 
                 'wp1 (fun a h1 -> 'wp2 a 'p h1) h0
             type bind_wlp ('a:Type) ('b:Type) ('wlp1:WP 'a) ('wlp2:'a -> WP 'b) ('p:Post 'b) (h0:heap) = 'wlp1 (fun a -> 'wlp2 a 'p) h0
             type if_then_else ('a:Type) ('p:Type) ('wp_then:WP 'a) ('wp_else:WP 'a) ('post:Post 'a) (h0:heap) = 
                 (if 'p 
                  then 'wp_then 'post h0
                  else 'wp_else 'post h0)
             type ite_wlp  ('a:Type) ('wlp_cases:WP 'a) ('post:Post 'a) (h0:heap) =
                 (forall (a:'a) (h:heap). 'wlp_cases (fun a1 h1 -> a=!=a1 \/ h=!=h1) h0 \/ 'post a h)
             type ite_wp ('a:Type) ('wlp_cases:WP 'a) ('wp_cases:WP 'a) ('post:Post 'a) (h0:heap) =
                 (forall (a:'a) (h:heap). 'wlp_cases (fun a1 h1 -> a=!=a1 \/ h=!=h1) h0 \/ 'post a h)
                 /\ 'wp_cases (fun a h_ -> True) h0
             type wp_binop ('a:Type) ('wp1:WP 'a) ('op:Type -> Type -> Type) ('wp2:WP 'a) ('p:Post 'a) (h:heap) =
                 'op ('wp1 'p h) ('wp2 'p h)
             type wp_as_type ('a:Type) ('wp:WP 'a) = (forall ('p:Post 'a) (h:heap). 'wp 'p h)
             type close_wp ('a:Type) ('b:Type) ('wp:'b -> WP 'a) ('p:Post 'a) (h:heap) = (forall (b:'b). 'wp b 'p h)
             type close_wp_t ('a:Type) ('wp:Type -> WP 'a) ('p:Post 'a) (h:heap) = (forall ('b:Type). 'wp 'b 'p h)
             type assert_p ('a:Type) ('P:Type) ('wp:WP 'a) ('p:Post 'a) (h:heap) = ('P /\ 'wp 'p h)
             type assume_p ('a:Type) ('P:Type) ('wp:WP 'a) ('p:Post 'a) (h:heap) = ('P ==> 'wp 'p h)
             type null_wp ('a:Type) ('p:Post 'a) (h:heap) = (forall (x:'a) (h':heap). 'p x h')
             type trivial ('a:Type) ('wp:WP 'a) = (forall h0. 'wp (fun r h1 -> True) h0)
             with State ('a:Type) ('wp:WP 'a) = STATE 'a 'wp 'wp
             and ST ('a:Type) ('pre:Pre) ('post: heap -> Post 'a) =
                 STATE 'a
                   (fun ('p:Post 'a) (h:heap) -> 'pre h /\ (forall a h1. ('pre h /\ 'post h a h1) ==> 'p a h1)) (* WP *)
                   (fun ('p:Post 'a) (h:heap) -> (forall a h1. ('pre h /\ 'post h a h1) ==> 'p a h1))           (* WLP *)
             and ST2 ('a:Type) ('pre:Pre) ('post: heap -> Post 'a) (mods:refs) =
                 STATE 'a
                   (fun ('p:Post 'a) (h:heap) -> 'pre h /\ (forall a h1. ('pre h /\ Modifies mods h h1 /\ 'post h a h1) ==> 'p a h1)) (* WP *)
                   (fun ('p:Post 'a) (h:heap) -> (forall a h1. ('pre h /\ Modifies mods h h1 /\ 'post h a h1) ==> 'p a h1))           (* WLP *)
;
  EXN::
             kind Pre  = Type
             kind Post ('a:Type) = result 'a -> Type
             kind WP   ('a:Type) = Post 'a -> Pre
             type return ('a:Type) (x:'a) ('p:Post 'a) = 'p (V x)
             type bind_wp ('a:Type) ('b:Type) ('wp1:WP 'a) ('wlp1:WP 'a) ('wp2:'a -> WP 'b) ('wlp2:'a -> WP 'b) ('p:Post 'b) =
                 (forall (rb:result 'b). 'p rb \/ 'wlp1 (fun ra1 -> if b2t (is_V ra1)
                                                                    then 'wlp2 (V.v ra1) (fun rb2 -> rb2=!=rb)
                                                                    else ra1 =!= rb))
                 /\ 'wp1 (fun ra1 -> (ITE (b2t (is_V ra1))
                                          ('wp2 (V.v ra1) (fun rb2 -> True))
                                           True))
             type bind_wlp ('a:Type) ('b:Type) ('wlp1:WP 'a) ('wlp2:'a -> WP 'b) ('p:Post 'b) =
                 (forall (rb:result 'b). 'p rb \/ 'wlp1 (fun ra1 -> if b2t (is_V ra1)
                                                                    then 'wlp2 (V.v ra1) (fun rb2 -> rb2=!=rb)
                                                                    else  ra1 =!= rb))
             type if_then_else ('a:Type) ('p:Type) ('wp_then:WP 'a) ('wp_else:WP 'a) ('post:Post 'a) =
                 (if 'p 
                  then 'wp_then 'post
                  else 'wp_else 'post)
             type ite_wlp  ('a:Type) ('wlp_cases:WP 'a) ('post:Post 'a) =
                 (forall (a:result 'a). 'wlp_cases (fun a1 -> a=!=a1) \/ 'post a)
             type ite_wp ('a:Type) ('wlp_cases:WP 'a) ('wp_cases:WP 'a) ('post:Post 'a) =
                 (forall (a:result 'a). 'wlp_cases (fun a1 -> a=!=a1) \/ 'post a)
                 /\ 'wp_cases (fun ra2 -> True)
             type wp_binop ('a:Type) ('wp1:WP 'a) ('op:Type -> Type -> Type) ('wp2:WP 'a) ('p:Post 'a) =
                 'op ('wp1 'p) ('wp2 'p)
             type wp_as_type ('a:Type) ('wp:WP 'a) = (forall ('p:Post 'a). 'wp 'p)
             type close_wp ('a:Type) ('b:Type) ('wp:'b -> WP 'a) ('p:Post 'a) = (forall (b:'b). 'wp b 'p)
             type close_wp_t ('a:Type) ('wp:Type -> WP 'a) ('p:Post 'a)  = (forall ('b:Type). 'wp 'b 'p)
             type assert_p ('a:Type) ('P:Type) ('wp:WP 'a) ('p:Post 'a) = ('P /\ 'wp 'p)
             type assume_p ('a:Type) ('P:Type) ('wp:WP 'a) ('p:Post 'a) = ('P ==> 'wp 'p)
             type null_wp ('a:Type) ('p:Post 'a) = (forall (r:result 'a). 'p r)
             type trivial ('a:Type) ('wp:WP 'a) = 'wp (fun r -> True) 
             with Exn ('a:Type) ('pre:Pre) ('post:Post 'a) =
                 EXN 'a
                   (fun 'p -> 'pre /\ (forall (r:result 'a). ('pre /\ 'post r) ==> 'p r)) (* WP *)
                   (fun 'p -> (forall (r:result 'a). ('pre /\ 'post r) ==> 'p r))         (* WLP *)
 ;
  ALL::
             kind Pre  = heap -> Type
             kind Post ('a:Type) = result 'a -> heap -> Type
             kind WP ('a:Type) = Post 'a -> Pre
             type return ('a:Type) (x:'a) ('p:Post 'a) = 'p (V x)

             type bind_wp ('a:Type) ('b:Type) ('wp1:WP 'a) ('wlp1:WP 'a) ('wp2:'a -> WP 'b) ('wlp2:'a -> WP 'b) ('p:Post 'b) (h0:heap) =
                 ('wp1 (fun ra h1 -> b2t (is_V ra) ==> 'wp2 (V.v ra) 'p h1) h0)
             type bind_wlp ('a:Type) ('b:Type) ('wlp1:WP 'a) ('wlp2:'a -> WP 'b) ('p:Post 'b) (h0:heap) =
                 (forall rb h. 'wlp1 (fun ra h1 -> 
                     if b2t (is_V ra)
                     then 'wlp2 (V.v ra) (fun rb2 h2 -> rb==rb2 /\ h==h2) h1
                     else rb==ra /\ h==h1) h0 ==> 'p rb h)
             type if_then_else ('a:Type) ('p:Type) ('wp_then:WP 'a) ('wp_else:WP 'a) ('post:Post 'a) (h0:heap) =
                 (if 'p 
                  then 'wp_then 'post h0
                  else 'wp_else 'post h0)
             type ite_wlp  ('a:Type) ('wlp_cases:WP 'a) ('post:Post 'a) (h0:heap) =
                 (forall (ra:result 'a) (h:heap). 'wlp_cases (fun ra2 h2 -> ra=!=ra2 \/ h=!=h2) h0 \/ 'post ra h)
             type ite_wp ('a:Type) ('wlp_cases:WP 'a) ('wp_cases:WP 'a) ('post:Post 'a) (h0:heap) =
                 (forall (ra:result 'a) (h:heap). 'wlp_cases (fun ra2 h2 -> ra=!=ra2 \/ h=!=h2) h0 \/ 'post ra h)
                 /\ 'wp_cases (fun _a _b -> True) h0
             type wp_binop ('a:Type) ('wp1:WP 'a) ('op:Type -> Type -> Type) ('wp2:WP 'a) ('p:Post 'a) (h:heap) =
                 'op ('wp1 'p h) ('wp2 'p h)
             type wp_as_type ('a:Type) ('wp:WP 'a) = (forall ('p:Post 'a) (h:heap). 'wp 'p h)
             type close_wp ('a:Type) ('b:Type) ('wp:'b -> WP 'a) ('p:Post 'a) (h:heap) = (forall (b:'b). 'wp b 'p h)
             type close_wp_t ('a:Type) ('wp:Type -> WP 'a) ('p:Post 'a) (h:heap) = (forall ('b:Type). 'wp 'b 'p h)
             type assert_p ('a:Type) ('P:Type) ('wp:WP 'a) ('p:Post 'a) (h:heap) = ('P /\ 'wp 'p h)
             type assume_p ('a:Type) ('P:Type) ('wp:WP 'a) ('p:Post 'a) (h:heap) = ('P ==> 'wp 'p h)
             type null_wp ('a:Type) ('p:Post 'a) (h0:heap) = (forall (a:result 'a) (h:heap). 'p a h)
             type trivial ('a:Type) ('wp:WP 'a) = (forall (h0:heap). 'wp (fun r h1 -> True) h0)
             with All ('a:Type) ('pre:Pre) ('post: heap -> Post 'a) (mods:refs) =
                 ALL 'a
                   (fun ('p:Post 'a) (h:heap) -> 'pre h /\ (forall ra h1. (Modifies mods h h1 /\ 'post h ra h1) ==> 'p ra h1)) (* WP *)
                   (fun ('p:Post 'a) (h:heap) -> forall ra h1. ('pre h /\ Modifies mods h h1 /\ 'post h ra h1) ==> 'p ra h1)             (* WLP *)
             and ML ('a:Type) =
                 ALL 'a (fun 'p h0 -> forall (a:result 'a) (h:heap). 'p a h) 
                        (fun 'p h0 -> forall (a:result 'a) (h:heap). 'p a h)

  with
  PURE  ~> STATE = (fun ('a:Type) ('wp:PURE.WP 'a) ('p:STATE.Post 'a) (h:heap) -> 'wp (fun a -> 'p a h));
  STATE ~> ALL   = (fun ('a:Type) ('wp:STATE.WP 'a) ('p:ALL.Post 'a) -> 'wp (fun a -> 'p (V a)));
  PURE  ~> EXN   = (fun ('a:Type) ('wp:PURE.WP 'a) ('p:EXN.Post 'a) -> 'wp (fun a -> 'p (V a)));
  EXN   ~> ALL   = (fun ('a:Type) ('wp:EXN.WP 'a) ('p:ALL.Post 'a) (h:heap) -> 'wp (fun ra -> 'p ra h))
}

type lex_t =
  | LexPair : 'a:Type -> 'b:Type -> 'a -> 'b -> lex_t
  | LexTop : lex_t

type Tuple2 'a 'b =
  | MkTuple2: _1:'a
           -> _2:'b
           -> Tuple2 'a 'b

type Tuple3 'a 'b 'c =
  | MkTuple3: _1:'a
           -> _2:'b
           -> _3:'c
          -> Tuple3 'a 'b 'c

type Tuple4 'a 'b 'c 'd =
  | MkTuple4: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> Tuple4 'a 'b 'c 'd

type Tuple5 'a 'b 'c 'd 'e =
  | MkTuple5: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> _5:'e
           -> Tuple5 'a 'b 'c 'd 'e

type Tuple6 'a 'b 'c 'd 'e 'f =
  | MkTuple6: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> _5:'e
           -> _6:'f
           -> Tuple6 'a 'b 'c 'd 'e 'f


type Tuple7 'a 'b 'c 'd 'e 'f 'g =
  | MkTuple7: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> _5:'e
           -> _6:'f
           -> _7:'g
           -> Tuple7 'a 'b 'c 'd 'e 'f 'g


type Tuple8 'a 'b 'c 'd 'e 'f 'g 'h =
  | MkTuple8: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> _5:'e
           -> _6:'f
           -> _7:'g
           -> _8:'h
           -> Tuple8 'a 'b 'c 'd 'e 'f 'g 'h

type DTuple2: 'a:Type
          -> 'b:('a -> Type)
          -> Type =
  | MkDTuple2: 'a:Type
           -> 'b:('a -> Type)
           -> _1:'a
           -> _2:'b _1
           -> DTuple2 'a 'b

(* type DTuple3: 'a:Type *)
(*           -> 'b:('a -> Type) *)
(*           -> 'c:(x:'a -> 'b x -> Type) *)
(*           -> Type = *)
(*   | MkDTuple3: 'a:Type *)
(*            -> 'b:('a -> Type) *)
(*            -> 'c:(x:'a -> 'b x -> Type) *)
(*            -> _1:'a *)
(*            -> _2:'b _1 *)
(*            -> _3:'c _1 _2 *)
(*            -> DTuple3 'a 'b 'c *)

(* type DTuple4: 'a:Type *)
(*           -> 'b:(x:'a -> Type) *)
(*           -> 'c:(x:'a -> 'b x -> Type) *)
(*           -> 'd:(x:'a -> y:'b x -> z:'c x y -> Type) *)
(*           -> Type = *)
(*   | MkDTuple4: 'a:Type *)
(*            -> 'b:('a -> Type) *)
(*            -> 'c:(x:'a -> 'b x -> Type) *)
(*            -> 'd:(x:'a -> y:'b x -> z:'c x y -> Type) *)
(*            -> _1:'a *)
(*            -> _2:'b _1 *)
(*            -> _3:'c _1 _2 *)
(*            -> _4:'d _1 _2 _3 *)
(*            -> DTuple4 'a 'b 'c 'd *)

(*  type Tuple5: 'a:Type *)
(*           -> 'b:('a -> Type) *)
(*           -> 'c:(x:'a -> 'b x -> Type) *)
(*           -> 'd:(x:'a -> y:'b x -> z:'c x y -> Type) *)
(*           -> 'e:(x:'a -> y:'b x -> z:'c x y -> w:'d x y z -> Type) *)
(*           -> Type = *)
(*   | MkTuple5: 'a:Type *)
(*            -> 'b:('a -> Type) *)
(*            -> 'c:(x:'a -> 'b x -> Type) *)
(*            -> 'd:(x:'a -> y:'b x -> z:'c x y -> Type) *)
(*            -> 'e:(x:'a -> y:'b x -> z:'c x y -> w:'d x y z -> Type) *)
(*            -> _1:'a *)
(*            -> _2:'b _1 *)
(*            -> _3:'c _1 _2 *)
(*            -> _4:'d _1 _2 _3 *)
(*            -> _5:'e _1 _2 _3 _4 *)
(*            -> Tuple5 'a 'b 'c 'd 'e *)

(*  type Tuple6: 'a:Type *)
(*           -> 'b:('a -> Type) *)
(*           -> 'c:(x:'a -> 'b x -> Type) *)
(*           -> 'd:(x:'a -> y:'b x -> z:'c x y -> Type) *)
(*           -> 'e:(x:'a -> y:'b x -> z:'c x y -> w:'d x y z -> Type) *)
(*           -> 'f:(x:'a -> y:'b x -> z:'c x y -> w:'d x y z -> u:'e x y z w -> Type) *)
(*           -> Type = *)
(*   | MkTuple6: 'a:Type *)
(*            -> 'b:('a -> Type) *)
(*            -> 'c:(x:'a -> 'b x -> Type) *)
(*            -> 'd:(x:'a -> y:'b x -> z:'c x y -> Type) *)
(*            -> 'e:(x:'a -> y:'b x -> z:'c x y -> w:'d x y z -> Type) *)
(*            -> 'f:(x:'a -> y:'b x -> z:'c x y -> w:'d x y z -> v:'e x y z w -> Type) *)
(*            -> _1:'a *)
(*            -> _2:'b _1 *)
(*            -> _3:'c _1 _2 *)
(*            -> _4:'d _1 _2 _3 *)
(*            -> _5:'e _1 _2 _3 _4 *)
(*            -> _6:'f _1 _2 _3 _4 _5 *)
(*            -> Tuple6 'a 'b 'c 'd 'e 'f *)

(*  type Tuple7: 'a:Type *)
(*           -> 'b:('a -> Type) *)
(*           -> 'c:(x:'a -> 'b x -> Type) *)
(*           -> 'd:(x:'a -> y:'b x -> z:'c x y -> Type) *)
(*           -> 'e:(x:'a -> y:'b x -> z:'c x y -> w:'d x y z -> Type) *)
(*           -> 'f:(x:'a -> y:'b x -> z:'c x y -> w:'d x y z -> u:'e x y z w -> Type) *)
(*           -> 'g:(x:'a -> y:'b x -> z:'c x y -> w:'d x y z -> u:'e x y z w -> v:'f x y z w u -> Type) *)
(*           -> Type = *)
(*   | MkTuple7: 'a:Type *)
(*            -> 'b:('a -> Type) *)
(*            -> 'c:(x:'a -> 'b x -> Type) *)
(*            -> 'd:(x:'a -> y:'b x -> z:'c x y -> Type) *)
(*            -> 'e:(x:'a -> y:'b x -> z:'c x y -> w:'d x y z -> Type) *)
(*            -> 'f:(x:'a -> y:'b x -> z:'c x y -> w:'d x y z -> u:'e x y z w -> Type) *)
(*            -> 'g:(x:'a -> y:'b x -> z:'c x y -> w:'d x y z -> u:'e x y z w -> v:'f x y z w u -> Type) *)
(*            -> _1:'a *)
(*            -> _2:'b _1 *)
(*            -> _3:'c _1 _2 *)
(*            -> _4:'d _1 _2 _3 *)
(*            -> _5:'e _1 _2 _3 _4 *)
(*            -> _6:'f _1 _2 _3 _4 _5 *)
(*            -> _7:'g _1 _2 _3 _4 _5 _6 *)
(*            -> Tuple7 'a 'b 'c 'd 'e 'f 'g *)

(*  type Tuple8: 'a:Type *)
(*           -> 'b:('a -> Type) *)
(*           -> 'c:(a:'a -> 'b a -> Type) *)
(*           -> 'd:(a:'a -> b:'b a -> c:'c a b -> Type) *)
(*           -> 'e:(a:'a -> b:'b a -> c:'c a b -> d:'d a b c -> Type) *)
(*           -> 'f:(a:'a -> b:'b a -> c:'c a b -> d:'d a b c -> e:'e a b c d -> Type) *)
(*           -> 'g:(a:'a -> b:'b a -> c:'c a b -> d:'d a b c -> e:'e a b c d -> f:'f a b c d e -> Type) *)
(*           -> 'h:(a:'a -> b:'b a -> c:'c a b -> d:'d a b c -> e:'e a b c d -> f:'f a b c d e -> g:'g a b c d e f -> Type) *)
(*           -> Type = *)
(*   | MkTuple8: 'a:Type *)
(*            -> 'b:('a -> Type) *)
(*            -> 'c:(a:'a -> 'b a -> Type) *)
(*            -> 'd:(a:'a -> b:'b a -> c:'c a b -> Type) *)
(*            -> 'e:(a:'a -> b:'b a -> c:'c a b -> d:'d a b c -> Type) *)
(*            -> 'f:(a:'a -> b:'b a -> c:'c a b -> d:'d a b c -> e:'e a b c d -> Type) *)
(*            -> 'g:(a:'a -> b:'b a -> c:'c a b -> d:'d a b c -> e:'e a b c d -> f:'f a b c d e -> Type) *)
(*            -> 'h:(a:'a -> b:'b a -> c:'c a b -> d:'d a b c -> e:'e a b c d -> f:'f a b c d e -> g:'g a b c d e f -> Type) *)
(*            -> _1:'a *)
(*            -> _2:'b _1 *)
(*            -> _3:'c _1 _2 *)
(*            -> _4:'d _1 _2 _3 *)
(*            -> _5:'e _1 _2 _3 _4 *)
(*            -> _6:'f _1 _2 _3 _4 _5 *)
(*            -> _7:'g _1 _2 _3 _4 _5 _6 *)
(*            -> _8:'h _1 _2 _3 _4 _5 _6 _7 *)
(*            -> Tuple8 'a 'b 'c 'd 'e 'f 'g 'h *)

(* Primitive (structural) equality.
   What about for function types? *)
assume val op_Equality : 'a:Type -> 'a -> 'a -> Tot bool
assume val op_disEquality : 'a:Type -> 'a -> 'a -> Tot bool

logic type LT : int -> int -> Type    (* infix < in concrete syntax *)
logic type GT : int -> int -> Type    (* infix > in concrete syntax *)
logic type LTE : int -> int -> Type   (* infix <= in concrete syntax *)
logic type GTE : int -> int -> Type   (* infix >= in concrete syntax *)

type either 'a 'b =
  | Inl : v:'a -> either 'a 'b
  | Inr : v:'b -> either 'a 'b

type list 'a =
  | Nil : list 'a
  | Cons : hd:'a -> tl:list 'a -> list 'a

val fst : ('a * 'b) -> Tot 'a
let fst x = MkTuple2._1 x

val snd : ('a * 'b) -> Tot 'b
let snd x = MkTuple2._2 x

assume val Assume: 'P:Type -> unit -> (y:unit{'P})
assume val admit: unit -> Pure unit True (fun x -> False)
assume val admitP: 'P:Type -> unit -> Pure unit True (fun x -> 'P)
assume val Assert : 'P:Type -> unit -> Pure unit (requires $"assertion failed" 'P) (ensures \x -> True)
assume val lemma : 'P:Type -> x:unit{'P} -> z:unit{'P}
assume val unreachable : x:unit{LBL "unreachable" False} -> 'a
assume val failwith: string -> 'a (* TODO: refine with the Exn monad *)
assume val raise: exn -> 'a       (* TODO: refine with the Exn monad *)
assume val pipe_right: 'a -> ('a -> 'b) -> 'b
assume val pipe_left: ('a -> 'b) -> 'a -> 'b
assume val ignore: 'a -> unit
assume val exit: int -> 'a
assume val try_with: (unit -> 'a) -> (exn -> 'a) -> 'a
assume logic val op_AmpAmp             : bool -> bool -> Tot bool
assume logic val op_BarBar             : bool -> bool -> Tot bool
assume logic val op_Negation           : bool -> Tot bool
assume logic val op_Multiply           : int -> int -> Tot int
assume logic val op_Subtraction        : int -> int -> Tot int
assume logic val op_Addition           : int -> int -> Tot int
assume logic val op_Minus              : int -> Tot int
assume logic val op_LessThanOrEqual    : int -> int -> Tot bool
assume logic val op_GreaterThan        : int -> int -> Tot bool
assume logic val op_GreaterThanOrEqual : int -> int -> Tot bool
assume logic val op_LessThan           : int -> int -> Tot bool
type nat = i:int{i >= 0}
type pos = i:int{i > 0}
type nonzero = i:int{i<>0}

(* For the moment we require not just that the divisor is non-zero,
   but also that the dividend is natural. This works around a
   mismatch between the semantics of integer division in SMT-LIB and
   in F#/OCaml. For SMT-LIB ints the modulus is always positive (as in
   math Euclidian division), while for F#/OCaml ints the modulus has
   the same sign as the dividend. Our arbitrary precision ints don't
   quite correspond to finite precision F#/OCaml ints though, but to
   OCaml's big_ints (for which the modulus is always positive).  So
   we'll need to return to this point anyway, when we discuss how to
   soundly map F* ints to something in F#/OCaml. *)
assume val op_Modulus            : nat -> nonzero -> Tot int
assume val op_Division           : nat -> nonzero -> Tot int

(* Unrefined specifications for these functions for typing ML code *)
assume val op_ColonEquals: ref 'a -> 'a -> unit
assume val op_Dereference: ref 'a -> 'a
assume type Boxed : Type -> Type


(* An effect abbreviation for a lemma *)
(*ghost*) effect Fact ('res:Type) ('p:Type) = Pure 'res True (fun r -> 'p)
