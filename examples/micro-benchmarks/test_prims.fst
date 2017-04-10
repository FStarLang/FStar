(*
   Copyright 2008-2016 Nikhil Swamy and Microsoft Research

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
(* False is the empty inductive type *)
type False =

(* True is the singleton inductive type *)
type True =
  | T

(* another singleton type, with its only inhabitant written '()'
   we assume it is primitive, for convenient interop with other languages *)
assume new type unit : Type0

(*
   infix binary '==';
   proof irrelevant, heterogeneous equality in Type#0;
   primitive (TODO: make it an inductive?)
*)
assume type Eq2 : #a:Type -> #b:Type -> a -> b -> Type0

(* bool is a two element type with elements {'true', 'false'}
   we assume it is primitive, for convenient interop with other languages *)
assume new type bool : Type0

(* bool-to-type coercion *)
opaque type b2t (b:bool) = (b == true)

(* constructive conjunction *)
type c_and  (p:Type) (q:Type) =
  | And   : p -> q -> c_and p q

(* '/\'  : specialized to Type#0 *)
opaque type l_and (p:Type0) (q:Type0) = c_and p q

(* constructive disjunction *)
type c_or   (p:Type) (q:Type) =
  | Left  : p -> c_or p q
  | Right : q -> c_or p q

(* '\/'  : specialized to Type#0 *)
opaque type l_or (p:Type0) (q:Type0) = c_or p q

(* '==>' : specialized to Type#0 *)
opaque type l_imp (p:Type0) (q:Type0) = p -> Tot q
                                         (* ^^^ NB: The Tot effect is primitive;            *)
				         (*         elaborated using PURE a few lines below *)
(* infix binary '<==>' *)
opaque type l_iff (p:Type) (q:Type) = (p ==> q) /\ (q ==> p)

(* prefix unary '~' *)
opaque type l_not (p:Type) = p ==> False

type XOR (p:Type) (q:Type) = (p \/ q) /\ ~(p /\ q)

opaque type ITE (p:Type) (q:Type) (r:Type) = (p ==> q) /\ (~p ==> r)

(* infix binary '<<'; a built-in well-founded partial order over all terms *)
assume type precedes : #a:Type -> #b:Type -> a -> b -> Type0

(* A coercion down to universe 0 *)
type squash (p:Type) = u:unit{p}

(* forall (x:a). p x : specialized to Type#0 *)
opaque type Forall (#a:Type) (p:a -> Type0) = squash (x:a -> Tot (p x))

(* dependent pairs DTuple2 in concrete syntax is '(x:a & b x)' *)
type DTuple2 (a:Type)
             (b:(a -> Type)) =
  | MkDTuple2: _1:a
            -> _2:b _1
            -> DTuple2 a b

(* exists (x:a). p x : specialized to Type#0 *)
opaque type Exists (#a:Type) (p:a -> Type0) = squash (x:a & p x)

(* PURE effect *)
type PurePre = Type0
type PurePost (a:Type) = a -> Type0
type PureWP   (a:Type) = PurePost a -> Tot PurePre
type pure_return (a:Type) (x:a) (p:PurePost a) =
     p x
type pure_bind_wlp (a:Type) (b:Type)
                   (wlp1:PureWP a) (wlp2:(a -> Tot (PureWP b)))
                   (p:PurePost b) =
     wlp1 (fun (x:a) -> wlp2 x p)
type pure_bind_wp  (a:Type) (b:Type)
                   (wp1:PureWP a) (wlp1:PureWP a)
                   (wp2: (a -> Tot (PureWP b))) (wlp2: (a -> Tot (PureWP b))) =
     pure_bind_wlp a b wp1 wp2
type pure_if_then_else (a:Type) (p:Type) (wp_then:PureWP a) (wp_else:PureWP a) (post:PurePost a) =
     ITE p (wp_then post) (wp_else post)
type pure_ite_wlp (a:Type) (wlp_cases:PureWP a) (post:PurePost a) =
     (forall (x:a). wlp_cases (fun (x':a) -> ~(Eq2 #a #a x x')) \/ post x)
type pure_ite_wp (a:Type) (wlp_cases:PureWP a) (wp_cases:PureWP a) (post:PurePost a) =
     pure_ite_wlp a wlp_cases post
    /\ wp_cases (fun (x:a) -> True)
type pure_wp_binop (a:Type) (wp1:PureWP a) (op:(Type -> Type -> Type)) (wp2:PureWP a) (p:PurePost a) =
     op (wp1 p) (wp2 p)
type pure_wp_as_type (a:Type) (wp:PureWP a) = forall (p:PurePost a). wp p
type pure_close_wp (a:Type) (b:Type) (wp:(b -> Tot (PureWP a))) (p:PurePost a) = forall (b:b). wp b p
type pure_assert_p (a:Type) (q:Type) (wp:PureWP a) (p:PurePost a) = q /\ wp p
type pure_assume_p (a:Type) (q:Type) (wp:PureWP a) (p:PurePost a) = q ==> wp p
type pure_null_wp  (a:Type) (p:PurePost a) = forall (x:a). p x
type pure_trivial  (a:Type) (wp:PureWP a) = wp (fun (x:a) -> True)

total new_effect { (* The definition of the PURE effect is fixed; no user should ever change this *)
  PURE : a:Type -> wp:PureWP a -> wlp:PureWP a -> Effect
  with return       = pure_return
     ; bind_wlp     = pure_bind_wlp
     ; bind_wp      = pure_bind_wp
     ; if_then_else = pure_if_then_else
     ; ite_wlp      = pure_ite_wlp
     ; ite_wp       = pure_ite_wp
     ; wp_binop     = pure_wp_binop
     ; wp_as_type   = pure_wp_as_type
     ; close_wp     = pure_close_wp
     ; assert_p     = pure_assert_p
     ; assume_p     = pure_assume_p
     ; null_wp      = pure_null_wp
     ; trivial      = pure_trivial
}

effect Pure (a:Type) (pre:PurePre) (post:PurePost a) =
        PURE a
             (fun (p:PurePost a) -> pre /\ (forall (x:a). post x ==> p x)) // PureWP
             (fun (p:PurePost a) -> forall (x:a). pre /\ post x ==> p x)   // WLP
effect Admit (a:Type) = PURE a (fun (p:PurePost a) -> True) (fun (p:PurePost a) -> True)
default effect Tot (a:Type) = PURE a (pure_null_wp a) (pure_null_wp a)

total new_effect GHOST = PURE
sub_effect
  PURE ~> GHOST = fun (a:Type) (wp:PureWP a) -> wp
default effect GTot (a:Type) = GHOST a (pure_null_wp a) (pure_null_wp a)
effect Ghost (a:Type) (pre:Type) (post:PurePost a) =
       GHOST a
           (fun (p:PurePost a) -> pre /\ (forall (x:a). post x ==> p x))
           (fun (p:PurePost a) -> forall (x:a). pre /\ post x ==> p x)

assume new type int : Type0
assume val op_AmpAmp             : bool -> bool -> Tot bool
assume val op_BarBar             : bool -> bool -> Tot bool
assume val op_Negation           : bool -> Tot bool
assume val op_Multiply           : int -> int -> Tot int
assume val op_Subtraction        : int -> int -> Tot int
assume val op_Addition           : int -> int -> Tot int
assume val op_Minus              : int -> Tot int
assume val op_LessThanOrEqual    : int -> int -> Tot bool
assume val op_GreaterThan        : int -> int -> Tot bool
assume val op_GreaterThanOrEqual : int -> int -> Tot bool
assume val op_LessThan           : int -> int -> Tot bool
(* Primitive (structural) equality.
   Restricted to small types.
   But, still allows functions ... TODO: disallow functions *)
assume val op_Equality :    #a:Type0 -> a -> a -> Tot bool
assume val op_disEquality : #a:Type0 -> a -> a -> Tot bool
assume new type char   : Type0
assume new type float  : Type0
assume new type string : Type0
assume new type exn : Type0
type double = float

assume val strcat : string -> string -> Tot string
assume new type uint8 : Type0
type byte = uint8

type list (a:Type) =
  | Nil  : list a
  | Cons : hd:a -> tl:list a -> list a

type pattern =
  | SMTPat   : #a:Type -> a -> pattern
  | SMTPatT  : a:Type -> pattern
//  | SMTPatOr : list (list pattern) -> pattern //TODO: rechecking this fails some universe checks

assume type decreases : #a:Type -> a -> Type0

(*
   Lemma is desugared specially. You can write:

     Lemma phi                 for   Lemma (requires True) phi []
     Lemma t1..tn              for   Lemma unit t1..tn
*)
effect Lemma (a:Type) (pre:Type) (post:Type) (pats:list pattern) =
       Pure a pre (fun r -> post)


type option (a:Type) =
  | None : option a
  | Some : v:a -> option a

type either 'a 'b =
  | Inl : v:'a -> either 'a 'b
  | Inr : v:'b -> either 'a 'b

type result (a:Type) =
  | V   : v:a -> result a
  | E   : e:exn -> result a
  | Err : msg:string -> result a

new_effect DIV = PURE
effect Div (a:Type) (pre:PurePre) (post:PurePost a) =
       DIV a
           (fun (p:PurePost a) -> pre /\ (forall a. post a ==> p a)) (* WP *)
           (fun (p:PurePost a) -> forall a. pre /\ post a ==> p a)   (* WLP *)

default effect Dv (a:Type) =
     DIV a (fun (p:PurePost a) -> (forall (x:a). p x))
           (fun (p:PurePost a) -> (forall (x:a). p x))

type STPre_h  (heap:Type)          = heap -> Type0
type STPost_h (heap:Type) (a:Type) = a -> heap -> Type0
type STWP_h   (heap:Type) (a:Type) = STPost_h heap a -> Tot (STPre_h heap)

type st_return        (heap:Type) (a:Type)
                      (x:a) (p:STPost_h heap a) =
     p x
type st_bind_wp       (heap:Type) (a:Type) (b:Type)
                      (wp1:STWP_h heap a) (wlp1:STWP_h heap a)
                      (wp2:(a -> Tot (STWP_h heap b))) (wlp2:(a -> Tot (STWP_h heap b)))
                      (p:STPost_h heap b) (h0:heap) =
     wp1 (fun a -> wp2 a p) h0
type st_bind_wlp      (heap:Type) (a:Type) (b:Type)
                      (wlp1:STWP_h heap a) (wlp2:(a -> Tot (STWP_h heap b)))
                      (p:STPost_h heap b) (h0:heap) =
     wlp1 (fun a -> wlp2 a p) h0
type st_if_then_else  (heap:Type) (a:Type) (p:Type)
                      (wp_then:STWP_h heap a) (wp_else:STWP_h heap a)
                      (post:STPost_h heap a) (h0:heap) =
     ITE p
        (wp_then post h0)
	(wp_else post h0)
type st_ite_wlp       (heap:Type) (a:Type)
                      (wlp_cases:STWP_h heap a)
                      (post:STPost_h heap a) (h0:heap) =
     (forall (a:a) (h:heap).
           wlp_cases (fun a1 h1 -> a=!=a1 \/ h=!=h1) h0
        \/ post a h)
type st_ite_wp        (heap:Type) (a:Type)
                      (wlp_cases:STWP_h heap a) (wp_cases:STWP_h heap a)
                      (post:STPost_h heap a) (h0:heap) =
     st_ite_wlp heap a wlp_cases post h0
     /\ wp_cases (fun a h_ -> True) h0
type st_wp_binop      (heap:Type) (a:Type)
                      (wp1:STWP_h heap a)
                      (op:(Type -> Type -> Type))
                      (wp2:STWP_h heap a)
                      (p:STPost_h heap a) (h:heap) =
     op (wp1 p h) (wp2 p h)
type st_wp_as_type    (heap:Type) (a:Type) (wp:STWP_h heap a) =
     (forall (p:STPost_h heap a) (h:heap). wp p h)
type st_close_wp      (heap:Type) (a:Type) (b:Type)
                      (wp:(b -> Tot (STWP_h heap a)))
                      (p:STPost_h heap a) (h:heap) =
     (forall (b:b). wp b p h)
type st_assert_p      (heap:Type) (a:Type) (p:Type)
                      (wp:STWP_h heap a)
                      (q:STPost_h heap a) (h:heap) =
     p /\ wp q h
type st_assume_p      (heap:Type) (a:Type) (p:Type)
                      (wp:STWP_h heap a)
                      (q:STPost_h heap a) (h:heap) =
     p ==> wp q h
type st_null_wp       (heap:Type) (a:Type)
                      (p:STPost_h heap a) (h:heap) =
     (forall (x:a) (h:heap). p x h)
type st_trivial       (heap:Type) (a:Type)
                      (wp:STWP_h heap a) =
     (forall h0. wp (fun r h1 -> True) h0)

new_effect {
  STATE_h (heap:Type) : result:Type -> wp:STWP_h heap result -> wlp:STWP_h heap result -> Effect
  with return       = st_return heap
     ; bind_wp      = st_bind_wp heap
     ; bind_wlp     = st_bind_wlp heap
     ; if_then_else = st_if_then_else heap
     ; ite_wlp      = st_ite_wlp heap
     ; ite_wp       = st_ite_wp heap
     ; wp_binop     = st_wp_binop heap
     ; wp_as_type   = st_wp_as_type heap
     ; close_wp     = st_close_wp heap
     ; assert_p     = st_assert_p heap
     ; assume_p     = st_assume_p heap
     ; null_wp      = st_null_wp heap
     ; trivial      = st_trivial heap
}

(* Effect EXCEPTION *)
type ExPre  = Type0
type ExPost (a:Type) = result a -> Type0
type ExWP   (a:Type) = ExPost a -> Tot ExPre
type ex_return (a:Type) (x:a) (p:ExPost a) = p (V x)
type ex_bind_wlp (a:Type) (b:Type) (wlp1:ExWP a) (wlp2:(a -> Tot (ExWP b))) (p:ExPost b) =
   (forall (rb:result b). p rb \/ wlp1 (fun ra1 -> if V? ra1
                                          then wlp2 (V.v ra1) (fun rb2 -> rb2=!=rb)
                                          else ra1 =!= rb))
type ex_bind_wp (a:Type) (b:Type)
		(wp1:ExWP a) (wlp1:ExWP a)
		(wp2:(a -> Tot (ExWP b))) (wlp2:(a -> Tot (ExWP b))) (p:ExPost b) =
   ex_bind_wlp a b wlp1 wlp2 p
   /\ wp1 (fun ra1 -> if V? ra1
                   then wp2 (V.v ra1) (fun rb2 -> True)
                   else True)
type ex_if_then_else (a:Type) (p:Type) (wp_then:ExWP a) (wp_else:ExWP a) (post:ExPost a) =
   ITE p
       (wp_then post)
       (wp_else post)
type ex_ite_wlp  (a:Type) (wlp_cases:ExWP a) (post:ExPost a) =
    (forall (a:result a). wlp_cases (fun a1 -> a=!=a1) \/ post a)
type ex_ite_wp (a:Type) (wlp_cases:ExWP a) (wp_cases:ExWP a) (post:ExPost a) =
    ex_ite_wlp a wlp_cases post
    /\ wp_cases (fun ra2 -> True)
type ex_wp_binop (a:Type) (wp1:ExWP a) (op:(Type -> Type -> Type)) (wp2:ExWP a) (p:ExPost a) =
   op (wp1 p) (wp2 p)
type ex_wp_as_type (a:Type) (wp:ExWP a) = (forall (p:ExPost a). wp p)
type ex_close_wp (a:Type) (b:Type) (wp:(b -> Tot (ExWP a))) (p:ExPost a) = (forall (b:b). wp b p)
type ex_assert_p (a:Type) (q:Type) (wp:ExWP a) (p:ExPost a) = (q /\ wp p)
type ex_assume_p (a:Type) (q:Type) (wp:ExWP a) (p:ExPost a) = (q ==> wp p)
type ex_null_wp (a:Type) (p:ExPost a) = (forall (r:result a). p r)
type ex_trivial (a:Type) (wp:ExWP a) = wp (fun r -> True)

new_effect {
  EXN : result:Type -> wp:ExWP result -> wlp:ExWP result -> Effect
  with
    return       = ex_return
  ; bind_wlp     = ex_bind_wlp
  ; bind_wp      = ex_bind_wp
  ; if_then_else = ex_if_then_else
  ; ite_wlp      = ex_ite_wlp
  ; ite_wp       = ex_ite_wp
  ; wp_binop     = ex_wp_binop
  ; wp_as_type   = ex_wp_as_type
  ; close_wp     = ex_close_wp
  ; assert_p     = ex_assert_p
  ; assume_p     = ex_assume_p
  ; null_wp      = ex_null_wp
  ; trivial      = ex_trivial
}
effect Exn (a:Type) (pre:ExPre) (post:ExPost a) =
       EXN a
         (fun (p:ExPost a) -> pre /\ (forall (r:result a). (pre /\ post r) ==> p r)) (* WP *)
         (fun (p:ExPost a) -> (forall (r:result a). (pre /\ post r) ==> p r))       (* WLP *)
default effect Ex (a:Type) = Exn a True (fun v -> True)

type AllPre_h  (h:Type)           = h -> Type
type AllPost_h (h:Type) (a:Type)  = result a -> h -> Type
type AllWP_h   (h:Type) (a:Type)  = AllPost_h h a -> Tot (AllPre_h h)

type all_return  (heap:Type) (a:Type) (x:a) (p:AllPost_h heap a) = p (V x)
type all_bind_wp (heap:Type) (a:Type) (b:Type)
                 (wp1:AllWP_h heap a) (wlp1:AllWP_h heap a)
                 (wp2:(a -> Tot (AllWP_h heap b))) (wlp2:(a -> Tot (AllWP_h heap b)))
                 (p:AllPost_h heap b) (h0:heap) =
   (wp1 (fun ra h1 -> V? ra ==> wp2 (V.v ra) p h1) h0)
type all_bind_wlp (heap:Type) (a:Type) (b:Type)
                  (wlp1:AllWP_h heap a) (wlp2:(a -> Tot (AllWP_h heap b)))
                  (p:AllPost_h heap b) (h0:heap) =
   (forall rb h. wlp1 (fun ra h1 ->
       if V? ra
       then wlp2 (V.v ra) (fun rb2 h2 -> rb=!=rb2 \/ h=!=h2) h1
       else rb=!=ra \/ h=!=h1) h0 \/ p rb h)
type all_if_then_else (heap:Type) (a:Type) (p:Type)
                      (wp_then:AllWP_h heap a) (wp_else:AllWP_h heap a)
                      (post:AllPost_h heap a) (h0:heap) =
   ITE p
       (wp_then post h0)
       (wp_else post h0)
type all_ite_wlp  (heap:Type) (a:Type)
                  (wlp_cases:AllWP_h heap a)
                  (post:AllPost_h heap a) (h0:heap) =
     (forall (ra:result a) (h:heap). wlp_cases (fun ra2 h2 -> ra=!=ra2 \/ h=!=h2) h0 \/ post ra h)
type all_ite_wp (heap:Type) (a:Type)
                (wlp_cases:AllWP_h heap a) (wp_cases:AllWP_h heap a)
                (post:AllPost_h heap a) (h0:heap) =
     (forall (ra:result a) (h:heap). wlp_cases (fun ra2 h2 -> ra=!=ra2 \/ h=!=h2) h0 \/ post ra h)
      /\ wp_cases (fun _a _b -> True) h0
type all_wp_binop (heap:Type) (a:Type)
                  (wp1:AllWP_h heap a) (op:(Type -> Type -> Type))
                  (wp2:AllWP_h heap a) (p:AllPost_h heap a) (h:heap) =
     op (wp1 p h) (wp2 p h)
type all_wp_as_type (heap:Type) (a:Type) (wp:AllWP_h heap a) =
    (forall (p:AllPost_h heap a) (h:heap). wp p h)
type all_close_wp (heap:Type) (a:Type) (b:Type)
                  (wp:(b -> Tot (AllWP_h heap a)))
                  (p:AllPost_h heap a) (h:heap) =
    (forall (b:b). wp b p h)
type all_assert_p (heap:Type) (a:Type) (p:Type)
                  (wp:AllWP_h heap a) (q:AllPost_h heap a) (h:heap) =
    p /\ wp q h
type all_assume_p (heap:Type) (a:Type) (p:Type)
                  (wp:AllWP_h heap a) (q:AllPost_h heap a) (h:heap) =
    p ==> wp q h
type all_null_wp (heap:Type) (a:Type)
                 (p:AllPost_h heap a) (h0:heap) =
    (forall (a:result a) (h:heap). p a h)
type all_trivial (heap:Type) (a:Type) (wp:AllWP_h heap a) =
    (forall (h0:heap). wp (fun r h1 -> True) h0)

new_effect {
  ALL_h (heap:Type) : a:Type -> wp:AllWP_h heap a -> wlp:AllWP_h heap a -> Effect
  with
    return       = all_return       heap
  ; bind_wp      = all_bind_wp      heap
  ; bind_wlp     = all_bind_wlp     heap
  ; if_then_else = all_if_then_else heap
  ; ite_wlp      = all_ite_wlp      heap
  ; ite_wp       = all_ite_wp       heap
  ; wp_binop     = all_wp_binop     heap
  ; wp_as_type   = all_wp_as_type   heap
  ; close_wp     = all_close_wp     heap
  ; assert_p     = all_assert_p     heap
  ; assume_p     = all_assume_p     heap
  ; null_wp      = all_null_wp      heap
  ; trivial      = all_trivial      heap
}

sub_effect
  PURE  ~> DIV   = fun (a:Type) (wp:PureWP a) (p:PurePost a) -> wp (fun a -> p a)
sub_effect
  DIV   ~> EXN   = fun (a:Type) (wp:PureWP a) (p:ExPost a) -> wp (fun a -> p (V a))

type lex_t =
  | LexTop  : lex_t
  | LexCons : #a:Type -> a -> lex_t -> lex_t

(* 'a * 'b *)
type Tuple2 'a 'b =
  | MkTuple2: _1:'a
           -> _2:'b
           -> Tuple2 'a 'b

(* 'a * 'b * 'c *)
type Tuple3 'a 'b 'c =
  | MkTuple3: _1:'a
           -> _2:'b
           -> _3:'c
          -> Tuple3 'a 'b 'c

(* 'a * 'b * 'c * 'd *)
type Tuple4 'a 'b 'c 'd =
  | MkTuple4: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> Tuple4 'a 'b 'c 'd

(* 'a * 'b * 'c * 'd * 'e *)
type Tuple5 'a 'b 'c 'd 'e =
  | MkTuple5: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> _5:'e
           -> Tuple5 'a 'b 'c 'd 'e

(* 'a * 'b * 'c * 'd * 'e * 'f *)
type Tuple6 'a 'b 'c 'd 'e 'f =
  | MkTuple6: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> _5:'e
           -> _6:'f
           -> Tuple6 'a 'b 'c 'd 'e 'f


(* 'a * 'b * 'c * 'd * 'e * 'f * 'g *)
type Tuple7 'a 'b 'c 'd 'e 'f 'g =
  | MkTuple7: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> _5:'e
           -> _6:'f
           -> _7:'g
           -> Tuple7 'a 'b 'c 'd 'e 'f 'g

(* 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h *)
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

(* Concrete syntax (x:a & y:b x & c x y) *)
type DTuple3 (a:Type)
             (b:(a -> Type))
             (c:(x:a -> b x -> Type)) =
   | MkDTuple3:_1:a
             -> _2:b _1
             -> _3:c _1 _2
             -> DTuple3 a b c

(* Concrete syntax (x:a & y:b x & z:c x y & d x y z) *)
type DTuple4 (a:Type)
             (b:(x:a -> Type))
             (c:(x:a -> b x -> Type))
             (d:(x:a -> y:b x -> z:c x y -> Type)) =
 | MkDTuple4:_1:a
           -> _2:b _1
           -> _3:c _1 _2
           -> _4:d _1 _2 _3
           -> DTuple4 a b c d

type as_requires (#a:Type) (wp:PureWP a)  = wp (fun x -> True)
type as_ensures  (#a:Type) (wlp:PureWP a) (x:a) = ~ (wlp (fun y -> (y=!=x)))

val fst : ('a * 'b) -> Tot 'a
let fst x = MkTuple2._1 x

val snd : ('a * 'b) -> Tot 'b
let snd x = MkTuple2._2 x

val dfst : #a:Type -> #b:(a -> Type) -> (x:a & b x) -> Tot a
let dfst #a #b t = MkDTuple2._1 t

val dsnd : #a:Type -> #b:(a -> Type) -> t:(x:a & b x) -> Tot (b (MkDTuple2._1 t))
let dsnd #a #b t = MkDTuple2._2 t

type Let (#a:Type) (x:a) (body:(a -> Type)) = body x
logic type InductionHyp : #a:Type -> a -> Type -> Type
assume val by_induction_on: #a:Type -> #p:Type -> induction_on:a -> proving:p -> Lemma (ensures (InductionHyp induction_on p))
logic type Using : #a:Type -> Type -> a -> Type
assume val using: #a:Type -> #p:Type -> proving:p -> pat:a -> Lemma (ensures (Using p pat))
assume val _assume : p:Type -> unit -> Pure unit (requires (True)) (ensures (fun x -> p))
assume val admit   : #a:Type -> unit -> Admit a
assume val magic   : #a:Type -> unit -> Tot a
assume val admitP  : p:Type -> Pure unit True (fun x -> p)
assume val _assert : p:Type -> unit -> Pure unit (requires $"assertion failed" p) (ensures (fun x -> True))
assume val cut     : p:Type -> Pure unit (requires $"assertion failed" p) (fun x -> p)
assume val qintro  : #a:Type -> #p:(a -> Type) -> =f:(x:a -> Lemma (p x)) -> Lemma (forall (x:a). p x)
assume val ghost_lemma: #a:Type -> #p:(a -> Type) -> #q:(a -> unit -> Type) -> =f:(x:a -> Ghost unit (p x) (q x)) -> Lemma (forall (x:a). p x ==> q x ())
assume val raise: exn -> Ex 'a       (* TODO: refine with the Exn monad *)
val ignore: #a:Type -> a -> Tot unit
let ignore #a x = ()

type nat = i:int{i >= 0}
type pos = i:int{i > 0}
type nonzero = i:int{i<>0}

(*    For the moment we require not just that the divisor is non-zero, *)
(*    but also that the dividend is natural. This works around a *)
(*    mismatch between the semantics of integer division in SMT-LIB and *)
(*    in F#/OCaml. For SMT-LIB ints the modulus is always positive (as in *)
(*    math Euclidian division), while for F#/OCaml ints the modulus has *)
(*    the same sign as the dividend. Our arbitrary precision ints don't *)
(*    quite correspond to finite precision F#/OCaml ints though, but to *)
(*    OCaml's big_ints (for which the modulus is always positive).  So *)
(*    we'll need to return to this point anyway, when we discuss how to *)
(*    soundly map F* ints to something in F#/OCaml.  *)

assume val op_Modulus            : int -> nonzero -> Tot int
assume val op_Division           : nat -> nonzero -> Tot int

assume val string_of_bool: bool -> Tot string
assume val string_of_int: int -> Tot string
