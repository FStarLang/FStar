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
type l_False =

(* True is the singleton inductive type *)
type l_True =
  | T

(* another singleton type, with its only inhabitant written '()'
   we assume it is primitive, for convenient interop with other languages *)
assume new type unit : Type0

(*
   infix binary '==';
   proof irrelevant, heterogeneous equality in Type#0;
   primitive (TODO: make it an inductive?)
*)
assume type eq2 : #a:Type -> #b:Type -> a -> b -> Type0

(* bool is a two element type with elements {'true', 'false'}
   we assume it is primitive, for convenient interop with other languages *)
assume new type bool : Type0

(* bool-to-type coercion *)
type b2t (b:bool) = (b == true)

(* constructive conjunction *)
type c_and  (p:Type) (q:Type) =
  | And   : p -> q -> c_and p q

(* '/\'  : specialized to Type#0 *)
type l_and (p:Type0) (q:Type0) = c_and p q

(* constructive disjunction *)
type c_or   (p:Type) (q:Type) =
  | Left  : p -> c_or p q
  | Right : q -> c_or p q

(* '\/'  : specialized to Type#0 *)
type l_or (p:Type0) (q:Type0) = c_or p q

(* '==>' : specialized to Type#0 *)
type l_imp (p:Type0) (q:Type0) = p -> GTot q
                                         (* ^^^ NB: The Tot effect is primitive;            *)
				         (*         elaborated using PURE a few lines below *)
(* infix binary '<==>' *)
type l_iff (p:Type) (q:Type) = (p ==> q) /\ (q ==> p)

(* prefix unary '~' *)
type l_not (p:Type) = p ==> False

type l_ITE (p:Type) (q:Type) (r:Type) = (p ==> q) /\ (~p ==> r)

(* infix binary '<<'; a built-in well-founded partial order over all terms *)
assume type precedes : #a:Type -> #b:Type -> a -> b -> Type0

(* internalizing the typing relation for the SMT encoding: (has_type x t) *)
assume type has_type : #a:Type -> a -> Type -> Type0

(* A coercion down to universe 0 *)
type squash (p:Type) = x:unit{p}
  
(* forall (x:a). p x : specialized to Type#0 *)
type l_Forall (#a:Type) (p:a -> GTot Type0) = squash (x:a -> GTot (p x))

(* dependent pairs DTuple2 in concrete syntax is '(x:a & b x)' *)
type dtuple2 (a:Type)
             (b:(a -> GTot Type)) =
  | Mkdtuple2: _1:a
            -> _2:b _1
            -> dtuple2 a b

(* exists (x:a). p x : specialized to Type#0 *)
type l_Exists (#a:Type) (p:a -> GTot Type0) = squash (x:a & p x)

(* PURE effect *)
let pure_pre = Type0
let pure_post (a:Type) = a -> GTot Type0
let pure_wp   (a:Type) = pure_post a -> GTot pure_pre

inline let pure_return (a:Type) (x:a) (p:pure_post a) =
     p x
inline let pure_bind_wlp (a:Type) (b:Type)
                   (wlp1:pure_wp a) (wlp2:(a -> GTot (pure_wp b)))
                   (p:pure_post b) =
     wlp1 (fun (x:a) -> wlp2 x p)
inline let pure_bind_wp  (a:Type) (b:Type)
                   (wp1:pure_wp a) (wlp1:pure_wp a)
                   (wp2: (a -> GTot (pure_wp b))) (wlp2: (a -> GTot (pure_wp b))) =
     pure_bind_wlp a b wp1 wp2
inline let pure_if_then_else (a:Type) (p:Type) (wp_then:pure_wp a) (wp_else:pure_wp a) (post:pure_post a) =
     l_ITE p (wp_then post) (wp_else post)
inline let pure_ite_wlp (a:Type) (wlp_cases:pure_wp a) (post:pure_post a) =
     (forall (x:a). ~(wlp_cases (fun (x':a) -> ~(eq2 #a #a x x'))) ==> post x)
inline let pure_ite_wp (a:Type) (wlp_cases:pure_wp a) (wp_cases:pure_wp a) (post:pure_post a) =
     pure_ite_wlp a wlp_cases post
    /\ wp_cases (fun (x:a) -> True)
inline let pure_wp_binop (a:Type) (wp1:pure_wp a) (op:(Type -> Type -> Type)) (wp2:pure_wp a) (p:pure_post a) =
     op (wp1 p) (wp2 p)
inline let pure_wp_as_type (a:Type) (wp:pure_wp a) = forall (p:pure_post a). wp p
inline let pure_close_wp (a:Type) (b:Type) (wp:(b -> GTot (pure_wp a))) (p:pure_post a) = forall (b:b). wp b p
inline let pure_assert_p (a:Type) (q:Type) (wp:pure_wp a) (p:pure_post a) = q /\ wp p
inline let pure_assume_p (a:Type) (q:Type) (wp:pure_wp a) (p:pure_post a) = q ==> wp p
inline let pure_null_wp  (a:Type) (p:pure_post a) = forall (x:a). p x
inline let pure_trivial  (a:Type) (wp:pure_wp a) = wp (fun (x:a) -> True)

total new_effect { (* The definition of the PURE effect is fixed; no user should ever change this *)
  PURE : a:Type -> wp:pure_wp a -> wlp:pure_wp a -> Effect
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

effect Pure (a:Type) (pre:pure_pre) (post:pure_post a) =
        PURE a
             (fun (p:pure_post a) -> pre /\ (forall (x:a). post x ==> p x)) // pure_wp
             (fun (p:pure_post a) -> forall (x:a). pre /\ post x ==> p x)   // WLP
effect Admit (a:Type) = PURE a (fun (p:pure_post a) -> True) (fun (p:pure_post a) -> True)

(* The primitive effect Tot is definitionally equal to an instance of PURE *)
default effect Tot (a:Type) = PURE a (pure_null_wp a) (pure_null_wp a)

total new_effect GHOST = PURE

inline let purewp_id (a:Type) (wp:pure_wp a) = wp

sub_effect
  PURE ~> GHOST = purewp_id

(* The primitive effect GTot is definitionally equal to an instance of GHOST *)
default effect GTot (a:Type) = GHOST a (pure_null_wp a) (pure_null_wp a)

effect Ghost (a:Type) (pre:Type) (post:pure_post a) =
       GHOST a
           (fun (p:pure_post a) -> pre /\ (forall (x:a). post x ==> p x))
           (fun (p:pure_post a) -> forall (x:a). pre /\ post x ==> p x)

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
   This still allows functions ... TODO: disallow functions *)
assume val op_Equality :    'a -> 'a -> Tot bool
assume val op_disEquality : 'a -> 'a -> Tot bool
assume type char   : Type0
assume new type float  : Type0
assume new type string : Type0
assume new type exn : Type0
type double = float
assume new type array : Type -> Type0
assume val strcat : string -> string -> Tot string

(* THESE BOUNDED INT TYPES ARE A HACK! 
   CURRENTLY NEEDED FOR BOOTSTRAPPING. 
   TODO: REMOVE THEM *)
type int16 = i:int{i > -32769  /\ 32768 > i}
type int32 = int
assume new type int64  : Type0
assume type uint8  : Type0
assume new type uint16 : Type0
assume new type uint32 : Type0
assume new type uint64 : Type0

type byte = uint8

type list (a:Type) =
  | Nil  : list a
  | Cons : hd:a -> tl:list a -> list a

type pattern =
  | SMTPat   : #a:Type -> a -> pattern
  | SMTPatT  : a:Type0 -> pattern 
  | SMTPatOr : list (list pattern) -> pattern 

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
sub_effect PURE ~> DIV  = purewp_id

effect Div (a:Type) (pre:pure_pre) (post:pure_post a) =
       DIV a
           (fun (p:pure_post a) -> pre /\ (forall a. post a ==> p a)) (* WP *)
           (fun (p:pure_post a) -> forall a. pre /\ post a ==> p a)   (* WLP *)

default effect Dv (a:Type) =
     DIV a (fun (p:pure_post a) -> (forall (x:a). p x))
           (fun (p:pure_post a) -> (forall (x:a). p x))


let st_pre_h  (heap:Type)          = heap -> GTot Type0
let st_post_h (heap:Type) (a:Type) = a -> heap -> GTot Type0
let st_wp_h   (heap:Type) (a:Type) = st_post_h heap a -> Tot (st_pre_h heap)

inline let st_return        (heap:Type) (a:Type)
                            (x:a) (p:st_post_h heap a) =
     p x
inline let st_bind_wp       (heap:Type) (a:Type) (b:Type)
                            (wp1:st_wp_h heap a) (wlp1:st_wp_h heap a)
                            (wp2:(a -> GTot (st_wp_h heap b))) (wlp2:(a -> GTot (st_wp_h heap b)))
                            (p:st_post_h heap b) (h0:heap) =
     wp1 (fun a h1 -> wp2 a p h1) h0
inline let st_bind_wlp      (heap:Type) (a:Type) (b:Type)
                             (wlp1:st_wp_h heap a) (wlp2:(a -> GTot (st_wp_h heap b)))
                             (p:st_post_h heap b) (h0:heap) =
     wlp1 (fun a h1 -> wlp2 a p h1) h0
inline let st_if_then_else  (heap:Type) (a:Type) (p:Type)
                             (wp_then:st_wp_h heap a) (wp_else:st_wp_h heap a)
                             (post:st_post_h heap a) (h0:heap) =
     l_ITE p
        (wp_then post h0)
	(wp_else post h0)
inline let st_ite_wlp       (heap:Type) (a:Type)
                             (wlp_cases:st_wp_h heap a)
                             (post:st_post_h heap a) (h0:heap) =
     (forall (a:a) (h:heap).
           ~ (wlp_cases (fun a1 h1 -> a=!=a1 \/ h=!=h1) h0)
	   ==> post a h)
inline let st_ite_wp        (heap:Type) (a:Type)
                             (wlp_cases:st_wp_h heap a) (wp_cases:st_wp_h heap a)
                             (post:st_post_h heap a) (h0:heap) =
     st_ite_wlp heap a wlp_cases post h0
     /\ wp_cases (fun a h_ -> True) h0
inline let st_wp_binop      (heap:Type) (a:Type)
                             (wp1:st_wp_h heap a)
                             (op:(Type -> Type -> GTot Type))
                             (wp2:st_wp_h heap a)
                             (p:st_post_h heap a) (h:heap) =
     op (wp1 p h) (wp2 p h)
inline let st_wp_as_type    (heap:Type) (a:Type) (wp:st_wp_h heap a) =
     (forall (p:st_post_h heap a) (h:heap). wp p h)
inline let st_close_wp      (heap:Type) (a:Type) (b:Type)
                             (wp:(b -> GTot (st_wp_h heap a)))
                             (p:st_post_h heap a) (h:heap) =
     (forall (b:b). wp b p h)
inline let st_assert_p      (heap:Type) (a:Type) (p:Type)
                             (wp:st_wp_h heap a)
                             (q:st_post_h heap a) (h:heap) =
     p /\ wp q h
inline let st_assume_p      (heap:Type) (a:Type) (p:Type)
                             (wp:st_wp_h heap a)
                             (q:st_post_h heap a) (h:heap) =
     p ==> wp q h
inline let st_null_wp       (heap:Type) (a:Type)
                             (p:st_post_h heap a) (h:heap) =
     (forall (x:a) (h:heap). p x h)
inline let st_trivial       (heap:Type) (a:Type)
                             (wp:st_wp_h heap a) =
     (forall h0. wp (fun r h1 -> True) h0)

new_effect {
  STATE_h (heap:Type) : result:Type -> wp:st_wp_h heap result -> wlp:st_wp_h heap result -> Effect
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
let ex_pre  = Type0
let ex_post (a:Type) = result a -> GTot Type0
let ex_wp   (a:Type) = ex_post a -> GTot ex_pre
inline let ex_return   (a:Type) (x:a) (p:ex_post a) = p (V x)
inline let ex_bind_wlp (a:Type) (b:Type) (wlp1:ex_wp a) (wlp2:(a -> GTot (ex_wp b))) (p:ex_post b) =
   (forall (rb:result b). p rb \/ wlp1 (fun ra1 -> if is_V ra1
                                          then wlp2 (V.v ra1) (fun rb2 -> rb2=!=rb)
                                          else ra1 =!= rb))
inline let ex_bind_wp (a:Type) (b:Type)
		       (wp1:ex_wp a) (wlp1:ex_wp a)
		       (wp2:(a -> GTot (ex_wp b))) (wlp2:(a -> GTot (ex_wp b))) (p:ex_post b) =
   ex_bind_wlp a b wlp1 wlp2 p
   /\ wp1 (fun ra1 -> if is_V ra1
                   then wp2 (V.v ra1) (fun rb2 -> True)
                   else True)
inline let ex_if_then_else (a:Type) (p:Type) (wp_then:ex_wp a) (wp_else:ex_wp a) (post:ex_post a) =
   l_ITE p
       (wp_then post)
       (wp_else post)
inline let ex_ite_wlp  (a:Type) (wlp_cases:ex_wp a) (post:ex_post a) =
    (forall (a:result a). ~ (wlp_cases (fun a1 -> a=!=a1)) ==> post a)
inline let ex_ite_wp (a:Type) (wlp_cases:ex_wp a) (wp_cases:ex_wp a) (post:ex_post a) =
    ex_ite_wlp a wlp_cases post
    /\ wp_cases (fun ra2 -> True)
inline let ex_wp_binop (a:Type) (wp1:ex_wp a) (op:(Type -> Type -> GTot Type)) (wp2:ex_wp a) (p:ex_post a) =
   op (wp1 p) (wp2 p)
inline let ex_wp_as_type (a:Type) (wp:ex_wp a) = (forall (p:ex_post a). wp p)
inline let ex_close_wp (a:Type) (b:Type) (wp:(b -> GTot (ex_wp a))) (p:ex_post a) = (forall (b:b). wp b p)
inline let ex_assert_p (a:Type) (q:Type) (wp:ex_wp a) (p:ex_post a) = (q /\ wp p)
inline let ex_assume_p (a:Type) (q:Type) (wp:ex_wp a) (p:ex_post a) = (q ==> wp p)
inline let ex_null_wp (a:Type) (p:ex_post a) = (forall (r:result a). p r)
inline let ex_trivial (a:Type) (wp:ex_wp a) = wp (fun r -> True)

new_effect {
  EXN : result:Type -> wp:ex_wp result -> wlp:ex_wp result -> Effect
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
effect Exn (a:Type) (pre:ex_pre) (post:ex_post a) =
       EXN a
         (fun (p:ex_post a) -> pre /\ (forall (r:result a). (pre /\ post r) ==> p r)) (* WP *)
         (fun (p:ex_post a) -> (forall (r:result a). (pre /\ post r) ==> p r))       (* WLP *)
inline let lift_div_exn (a:Type) (wp:pure_wp a) (p:ex_post a) = wp (fun a -> p (V a))
sub_effect DIV ~> EXN = lift_div_exn
default effect Ex (a:Type) = Exn a True (fun v -> True)

let all_pre_h  (h:Type)           = h -> GTot Type0
let all_post_h (h:Type) (a:Type)  = result a -> h -> GTot Type0
let all_wp_h   (h:Type) (a:Type)  = all_post_h h a -> Tot (all_pre_h h)

inline let all_return  (heap:Type) (a:Type) (x:a) (p:all_post_h heap a) = p (V x)
inline let all_bind_wp (heap:Type) (a:Type) (b:Type)
                        (wp1:all_wp_h heap a) (wlp1:all_wp_h heap a)
                        (wp2:(a -> GTot (all_wp_h heap b))) (wlp2:(a -> GTot (all_wp_h heap b)))
                        (p:all_post_h heap b) (h0:heap) =
   (wp1 (fun ra h1 -> is_V ra ==> wp2 (V.v ra) p h1) h0)
inline let all_bind_wlp (heap:Type) (a:Type) (b:Type)
                         (wlp1:all_wp_h heap a) (wlp2:(a -> GTot (all_wp_h heap b)))
                         (p:all_post_h heap b) (h0:heap) =
   (forall rb h. wlp1 (fun ra h1 ->
       if is_V ra
       then wlp2 (V.v ra) (fun rb2 h2 -> rb=!=rb2 \/ h=!=h2) h1
       else rb=!=ra \/ h=!=h1) h0 \/ p rb h)
inline let all_if_then_else (heap:Type) (a:Type) (p:Type)
                             (wp_then:all_wp_h heap a) (wp_else:all_wp_h heap a)
                             (post:all_post_h heap a) (h0:heap) =
   l_ITE p
       (wp_then post h0)
       (wp_else post h0)
inline let all_ite_wlp  (heap:Type) (a:Type)
                         (wlp_cases:all_wp_h heap a)
                         (post:all_post_h heap a) (h0:heap) =
     (forall (ra:result a) (h:heap). ~ (wlp_cases (fun ra2 h2 -> ra=!=ra2 \/ h=!=h2) h0) ==> post ra h)
inline let all_ite_wp (heap:Type) (a:Type)
                       (wlp_cases:all_wp_h heap a) (wp_cases:all_wp_h heap a)
                       (post:all_post_h heap a) (h0:heap) =
     (forall (ra:result a) (h:heap). wlp_cases (fun ra2 h2 -> ra=!=ra2 \/ h=!=h2) h0 \/ post ra h)
      /\ wp_cases (fun _a _b -> True) h0
inline let all_wp_binop (heap:Type) (a:Type)
                         (wp1:all_wp_h heap a) (op:(Type -> Type -> GTot Type))
                         (wp2:all_wp_h heap a) (p:all_post_h heap a) (h:heap) =
     op (wp1 p h) (wp2 p h)
inline let all_wp_as_type (heap:Type) (a:Type) (wp:all_wp_h heap a) =
    (forall (p:all_post_h heap a) (h:heap). wp p h)
inline let all_close_wp (heap:Type) (a:Type) (b:Type)
                         (wp:(b -> GTot (all_wp_h heap a)))
                         (p:all_post_h heap a) (h:heap) =
    (forall (b:b). wp b p h)
inline let all_assert_p (heap:Type) (a:Type) (p:Type)
                         (wp:all_wp_h heap a) (q:all_post_h heap a) (h:heap) =
    p /\ wp q h
inline let all_assume_p (heap:Type) (a:Type) (p:Type)
                         (wp:all_wp_h heap a) (q:all_post_h heap a) (h:heap) =
    p ==> wp q h
inline let all_null_wp (heap:Type) (a:Type)
                        (p:all_post_h heap a) (h0:heap) =
    (forall (a:result a) (h:heap). p a h)
inline let all_trivial (heap:Type) (a:Type) (wp:all_wp_h heap a) =
    (forall (h0:heap). wp (fun r h1 -> True) h0)

new_effect {
  ALL_h (heap:Type) : a:Type -> wp:all_wp_h heap a -> wlp:all_wp_h heap a -> Effect
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





type lex_t =
  | LexTop  : lex_t
  | LexCons : #a:Type -> a -> lex_t -> lex_t

(* 'a * 'b *)
type tuple2 'a 'b =
  | Mktuple2: _1:'a
           -> _2:'b
           -> tuple2 'a 'b

(* 'a * 'b * 'c *)
type tuple3 'a 'b 'c =
  | Mktuple3: _1:'a
           -> _2:'b
           -> _3:'c
          -> tuple3 'a 'b 'c

(* 'a * 'b * 'c * 'd *)
type tuple4 'a 'b 'c 'd =
  | Mktuple4: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> tuple4 'a 'b 'c 'd

(* 'a * 'b * 'c * 'd * 'e *)
type tuple5 'a 'b 'c 'd 'e =
  | Mktuple5: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> _5:'e
           -> tuple5 'a 'b 'c 'd 'e

(* 'a * 'b * 'c * 'd * 'e * 'f *)
type tuple6 'a 'b 'c 'd 'e 'f =
  | Mktuple6: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> _5:'e
           -> _6:'f
           -> tuple6 'a 'b 'c 'd 'e 'f


(* 'a * 'b * 'c * 'd * 'e * 'f * 'g *)
type tuple7 'a 'b 'c 'd 'e 'f 'g =
  | Mktuple7: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> _5:'e
           -> _6:'f
           -> _7:'g
           -> tuple7 'a 'b 'c 'd 'e 'f 'g

(* 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h *)
type tuple8 'a 'b 'c 'd 'e 'f 'g 'h =
  | Mktuple8: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> _5:'e
           -> _6:'f
           -> _7:'g
           -> _8:'h
           -> tuple8 'a 'b 'c 'd 'e 'f 'g 'h

(* Concrete syntax (x:a & y:b x & c x y) *)
type dtuple3 (a:Type)
             (b:(a -> GTot Type))
             (c:(x:a -> b x -> GTot Type)) =
   | Mkdtuple3:_1:a
             -> _2:b _1
             -> _3:c _1 _2
             -> dtuple3 a b c

(* Concrete syntax (x:a & y:b x & z:c x y & d x y z) *)
type dtuple4 (a:Type)
             (b:(x:a -> GTot Type))
             (c:(x:a -> b x -> GTot Type))
             (d:(x:a -> y:b x -> z:c x y -> GTot Type)) =
 | Mkdtuple4:_1:a
           -> _2:b _1
           -> _3:c _1 _2
           -> _4:d _1 _2 _3
           -> dtuple4 a b c d

let as_requires (#a:Type) (wp:pure_wp a)  = wp (fun x -> True)
let as_ensures  (#a:Type) (wlp:pure_wp a) (x:a) = ~ (wlp (fun y -> (y=!=x)))

val fst : ('a * 'b) -> Tot 'a
let fst x = Mktuple2._1 x

val snd : ('a * 'b) -> Tot 'b
let snd x = Mktuple2._2 x

val dfst : #a:Type -> #b:(a -> GTot Type) -> dtuple2 a b -> Tot a
let dfst #a #b t = Mkdtuple2._1 t

val dsnd : #a:Type -> #b:(a -> GTot Type) -> t:dtuple2 a b -> Tot (b (Mkdtuple2._1 t))
let dsnd #a #b t = Mkdtuple2._2 t

assume val _assume : p:Type -> unit -> Pure unit (requires (True)) (ensures (fun x -> p))
assume val admit   : #a:Type -> unit -> Admit a
assume val magic   : #a:Type -> unit -> Tot a
irreducible val unsafe_coerce  : #a:Type -> #b: Type -> a -> Tot b
let unsafe_coerce #a #b x = admit(); x
assume val admitP  : p:Type -> Pure unit True (fun x -> p)
assume val _assert : p:Type -> unit -> Pure unit (requires p) (ensures (fun x -> True))
assume val cut     : p:Type -> Pure unit (requires p) (fun x -> p)
assume val qintro  : #a:Type -> #p:(a -> GTot Type) -> $f:(x:a -> Lemma (p x)) -> Lemma (forall (x:a). p x)
assume val ghost_lemma: #a:Type -> #p:(a -> GTot Type) -> #q:(a -> unit -> GTot Type) -> $f:(x:a -> Ghost unit (p x) (q x)) -> Lemma (forall (x:a). p x ==> q x ())
assume val raise: exn -> Ex 'a       (* TODO: refine with the Exn monad *)
assume new type range_of : #a:Type -> a -> Type0
irreducible type labeled (#a:Type0) (#x:a) (r:range_of x) (msg:string) (b:Type) = b

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
