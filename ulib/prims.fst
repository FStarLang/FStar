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

(* Type of attributes *)
assume new type attribute : Type0
(* An attribute indicating that some effect must be processed by dmff *)
assume val cps : attribute

(* A predicate to express when a type supports decidable equality
   The type-checker emits axioms for hasEq for each inductive type *)
assume type hasEq: Type -> GTot Type0

type eqtype = a:Type{hasEq a}

(* False is the empty inductive type *)
type c_False =

(* True is the singleton inductive type *)
type c_True =
  | T

(* another singleton type, with its only inhabitant written '()'
   we assume it is primitive, for convenient interop with other languages *)
assume new type unit : Type0
assume HasEq_unit: hasEq unit

(* A coercion down to universe 0 *)
type squash (p:Type) : Type0 = x:unit{p}

(*
 * Squashed versions of truth and falsehood
 *)
type l_True = squash c_True
type l_False = squash c_False

(* An SMT-pattern to control unfolding inductives;
   In a proof, you can say `allow_inversion (option a)`
   to allow the SMT solver. cf. allow_inversion below
 *)
let inversion (a:Type) = True

(* The usual equality deifned as an inductive type *)
type equals (#a:Type) (x:a) : a -> Type =
  | Refl : equals x x
  
(* infix binary '==';
   proof irrelevant, heterogeneous equality in Type#0
*)   
//TODO: instead of hard-wiring the == syntax, 
//       we should just rename eq2 to op_Equals_Equals
type eq2 (#a:Type) (x:a) (y:a) = squash (equals x y)

(* Heterogeneous equality *)
type h_equals (#a:Type) (x:a) : #b:Type -> b -> Type = 
  | HRefl : h_equals x x

(* A proof-irrelevant version of h_equals *)
type eq3 (#a:Type) (#b:Type) (x:a) (y:b) = squash (h_equals x y)

unfold let op_Equals_Equals_Equals (#a:Type) (#b:Type) (x:a) (y:b) = eq3 x y

(* bool is a two element type with elements {'true', 'false'}
   we assume it is primitive, for convenient interop with other languages *)
assume new type bool : Type0
assume HasEq_bool: hasEq bool

(* bool-to-type coercion *)
type b2t (b:bool) = (b == true)

(* constructive conjunction *)
type c_and  (p:Type) (q:Type) =
  | And   : p -> q -> c_and p q

(* '/\'  : specialized to Type#0 *)
type l_and (p:Type0) (q:Type0) = squash (c_and p q)

(* constructive disjunction *)
type c_or   (p:Type) (q:Type) =
  | Left  : p -> c_or p q
  | Right : q -> c_or p q

(* '\/'  : specialized to Type#0 *)
type l_or (p:Type0) (q:Type0) = squash (c_or p q)

(* '==>' : specialized to Type#0 *)
type l_imp (p:Type0) (q:Type0) = squash (p -> GTot q)
                                         (* ^^^ NB: The GTot effect is primitive;            *)
				         (*         elaborated using GHOST a few lines below *)
(* infix binary '<==>' *)
type l_iff (p:Type) (q:Type) = (p ==> q) /\ (q ==> p)

(* prefix unary '~' *)
type l_not (p:Type) = l_imp p False

unfold type l_ITE (p:Type) (q:Type) (r:Type) = (p ==> q) /\ (~p ==> r)

(* infix binary '<<'; a built-in well-founded partial order over all terms *)
assume type precedes : #a:Type -> #b:Type -> a -> b -> Type0

(* internalizing the typing relation for the SMT encoding: (has_type x t) *)
assume type has_type : #a:Type -> a -> Type -> Type0
  
(* forall (x:a). p x : specialized to Type#0 *)
type l_Forall (#a:Type) (p:a -> GTot Type0) = squash (x:a -> GTot (p x))

(* The type of squashed types *)
type prop = a:Type0{ forall (x:a). x === () }

(* dependent pairs DTuple2 in concrete syntax is '(x:a & b x)' *)
unopteq type dtuple2 (a:Type)
             (b:(a -> GTot Type)) =
  | Mkdtuple2: _1:a
            -> _2:b _1
            -> dtuple2 a b

(* exists (x:a). p x : specialized to Type#0 *)
type l_Exists (#a:Type) (p:a -> GTot Type0) = squash (x:a & p x)

assume new type range : Type0
assume val range_0:range

assume new type string : Type0
assume HasEq_string: hasEq string

irreducible let labeled (r:range) (msg:string) (b:Type) = b
type range_of (#a:Type) (x:a) = range

(* PURE effect *)
let pure_pre = Type0
let pure_post (a:Type) = a -> GTot Type0
let pure_wp   (a:Type) = pure_post a -> GTot pure_pre

assume type guard_free: Type0 -> Type0

unfold let pure_return (a:Type) (x:a) (p:pure_post a) =
     forall (y:a). y==x ==> p y

unfold let pure_bind_wp (r1:range) (a:Type) (b:Type)
                   (wp1:pure_wp a) (wp2: (a -> GTot (pure_wp b)))
                   (p : pure_post b) =
	wp1 (fun (x:a) -> wp2 x p)
unfold let pure_if_then_else (a:Type) (p:Type) (wp_then:pure_wp a) (wp_else:pure_wp a) (post:pure_post a) =
     l_ITE p (wp_then post) (wp_else post)

unfold let pure_ite_wp (a:Type) (wp:pure_wp a) (post:pure_post a) =
     forall (k:pure_post a).
	 (forall (x:a).{:pattern (guard_free (k x))} k x <==> post x)
	 ==> wp k

unfold let pure_stronger (a:Type) (wp1:pure_wp a) (wp2:pure_wp a) =
        forall (p:pure_post a). wp1 p ==> wp2 p

unfold let pure_close_wp (a:Type) (b:Type) (wp:(b -> GTot (pure_wp a))) (p:pure_post a) = forall (b:b). wp b p
unfold let pure_assert_p (a:Type) (q:Type) (wp:pure_wp a) (p:pure_post a) = q /\ wp p
unfold let pure_assume_p (a:Type) (q:Type) (wp:pure_wp a) (p:pure_post a) = q ==> wp p
unfold let pure_null_wp  (a:Type) (p:pure_post a) = forall (x:a). p x
unfold let pure_trivial  (a:Type) (wp:pure_wp a) = wp (fun (x:a) -> True)

total new_effect { (* The definition of the PURE effect is fixed; no user should ever change this *)
  PURE : a:Type -> wp:pure_wp a -> Effect
  with return_wp    = pure_return
     ; bind_wp      = pure_bind_wp
     ; if_then_else = pure_if_then_else
     ; ite_wp       = pure_ite_wp
     ; stronger     = pure_stronger
     ; close_wp     = pure_close_wp
     ; assert_p     = pure_assert_p
     ; assume_p     = pure_assume_p
     ; null_wp      = pure_null_wp
     ; trivial      = pure_trivial
}

effect Pure (a:Type) (pre:pure_pre) (post:pure_post a) =
        PURE a
             (fun (p:pure_post a) -> pre /\ (forall (x:a). pre /\ post x ==> p x)) // pure_wp
effect Admit (a:Type) = PURE a (fun (p:pure_post a) -> True)

(* The primitive effect Tot is definitionally equal to an instance of PURE *)
effect Tot (a:Type) = PURE a (pure_null_wp a)

total new_effect GHOST = PURE

unfold let purewp_id (a:Type) (wp:pure_wp a) = wp

sub_effect
  PURE ~> GHOST = purewp_id

(* The primitive effect GTot is definitionally equal to an instance of GHOST *)
effect GTot (a:Type) = GHOST a (pure_null_wp a)
(* #set-options "--print_universes --print_implicits --print_bound_var_types --debug Prims --debug_level Extreme" *)
effect Ghost (a:Type) (pre:Type) (post:pure_post a) =
       GHOST a
           (fun (p:pure_post a) -> pre /\ (forall (x:a). post x ==> p x))

assume new type int : Type0

assume HasEq_int: hasEq int

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
assume val op_Equality :    #a:Type{hasEq a} -> a -> a -> Tot bool
assume val op_disEquality : #a:Type{hasEq a} -> a -> a -> Tot bool
assume new type exn : Type0
assume new type array : Type -> Type0
assume val strcat : string -> string -> Tot string

type list (a:Type) =
  | Nil  : list a
  | Cons : hd:a -> tl:list a -> list a

noeq type pattern =
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

noeq type result (a:Type) =
  | V   : v:a -> result a
  | E   : e:exn -> result a
  | Err : msg:string -> result a

(* This new bit for Dijkstra Monads for Free; it has a "double meaning",
 * either as an alias for reasoning about the direct definitions, or as a marker
 * for places where a CPS transformation should happen. *)
effect M (a:Type) = Tot a (attributes cps)

let returnM (a:Type) (x:a) : M a = x

new_effect DIV = PURE
sub_effect PURE ~> DIV  = purewp_id

effect Div (a:Type) (pre:pure_pre) (post:pure_post a) =
       DIV a
           (fun (p:pure_post a) -> pre /\ (forall a. pre /\ post a ==> p a)) (* WP *)

effect Dv (a:Type) =
     DIV a (fun (p:pure_post a) -> (forall (x:a). p x))


let st_pre_h  (heap:Type)          = heap -> GTot Type0
let st_post_h (heap:Type) (a:Type) = a -> heap -> GTot Type0
let st_wp_h   (heap:Type) (a:Type) = st_post_h heap a -> Tot (st_pre_h heap)

unfold let st_return        (heap:Type) (a:Type)
                            (x:a) (p:st_post_h heap a) =
     p x
unfold let st_bind_wp       (heap:Type) 
			    (r1:range) 
			    (a:Type) (b:Type)
                            (wp1:st_wp_h heap a)
                            (wp2:(a -> GTot (st_wp_h heap b)))
                            (p:st_post_h heap b) (h0:heap) =
  wp1 (fun a h1 -> wp2 a p h1) h0
unfold let st_if_then_else  (heap:Type) (a:Type) (p:Type)
                             (wp_then:st_wp_h heap a) (wp_else:st_wp_h heap a)
                             (post:st_post_h heap a) (h0:heap) =
     l_ITE p
        (wp_then post h0)
	(wp_else post h0)
unfold let st_ite_wp        (heap:Type) (a:Type)
                            (wp:st_wp_h heap a)
                            (post:st_post_h heap a) (h0:heap) =
     forall (k:st_post_h heap a).
	 (forall (x:a) (h:heap).{:pattern (guard_free (k x h))} k x h <==> post x h)
	 ==> wp k h0
unfold let st_stronger  (heap:Type) (a:Type) (wp1:st_wp_h heap a)
                        (wp2:st_wp_h heap a) =
     (forall (p:st_post_h heap a) (h:heap). wp1 p h ==> wp2 p h)

unfold let st_close_wp      (heap:Type) (a:Type) (b:Type)
                             (wp:(b -> GTot (st_wp_h heap a)))
                             (p:st_post_h heap a) (h:heap) =
     (forall (b:b). wp b p h)
unfold let st_assert_p      (heap:Type) (a:Type) (p:Type)
                             (wp:st_wp_h heap a)
                             (q:st_post_h heap a) (h:heap) =
     p /\ wp q h
unfold let st_assume_p      (heap:Type) (a:Type) (p:Type)
                             (wp:st_wp_h heap a)
                             (q:st_post_h heap a) (h:heap) =
     p ==> wp q h
unfold let st_null_wp       (heap:Type) (a:Type)
                             (p:st_post_h heap a) (h:heap) =
     (forall (x:a) (h:heap). p x h)
unfold let st_trivial       (heap:Type) (a:Type)
                             (wp:st_wp_h heap a) =
     (forall h0. wp (fun r h1 -> True) h0)

new_effect {
  STATE_h (heap:Type) : result:Type -> wp:st_wp_h heap result -> Effect
  with return_wp      = st_return heap
     ; bind_wp      = st_bind_wp heap
     ; if_then_else = st_if_then_else heap
     ; ite_wp       = st_ite_wp heap
     ; stronger     = st_stronger heap
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
unfold let ex_return   (a:Type) (x:a) (p:ex_post a) : GTot Type0 = p (V x)
unfold let ex_bind_wp (r1:range) (a:Type) (b:Type)
		       (wp1:ex_wp a)
		       (wp2:(a -> GTot (ex_wp b))) (p:ex_post b)
         : GTot Type0 =
  forall (k:ex_post b).
     (forall (rb:result b).{:pattern (guard_free (k rb))} k rb <==> p rb)
     ==> (wp1 (fun ra1 -> (V? ra1 ==> wp2 (V?.v ra1) k)
			/\ (E? ra1 ==> k (E (E?.e ra1)))))

unfold let ex_ite_wp (a:Type) (wp:ex_wp a) (post:ex_post a) =
  forall (k:ex_post a).
     (forall (rb:result a).{:pattern (guard_free (k rb))} k rb <==> post rb)
     ==> wp k

unfold let ex_if_then_else (a:Type) (p:Type) (wp_then:ex_wp a) (wp_else:ex_wp a) (post:ex_post a) =
   l_ITE p
       (wp_then post)
       (wp_else post)
unfold let ex_stronger (a:Type) (wp1:ex_wp a) (wp2:ex_wp a) =
        (forall (p:ex_post a). wp1 p ==> wp2 p)

unfold let ex_close_wp (a:Type) (b:Type) (wp:(b -> GTot (ex_wp a))) (p:ex_post a) = (forall (b:b). wp b p)
unfold let ex_assert_p (a:Type) (q:Type) (wp:ex_wp a) (p:ex_post a) = (q /\ wp p)
unfold let ex_assume_p (a:Type) (q:Type) (wp:ex_wp a) (p:ex_post a) = (q ==> wp p)
unfold let ex_null_wp (a:Type) (p:ex_post a) = (forall (r:result a). p r)
unfold let ex_trivial (a:Type) (wp:ex_wp a) = wp (fun r -> True)

new_effect {
  EXN : result:Type -> wp:ex_wp result -> Effect
  with
    return_wp    = ex_return
  ; bind_wp      = ex_bind_wp
  ; if_then_else = ex_if_then_else
  ; ite_wp       = ex_ite_wp
  ; stronger     = ex_stronger
  ; close_wp     = ex_close_wp
  ; assert_p     = ex_assert_p
  ; assume_p     = ex_assume_p
  ; null_wp      = ex_null_wp
  ; trivial      = ex_trivial
}
effect Exn (a:Type) (pre:ex_pre) (post:ex_post a) =
       EXN a
         (fun (p:ex_post a) -> pre /\ (forall (r:result a). (pre /\ post r) ==> p r)) (* WP *)

unfold let lift_div_exn (a:Type) (wp:pure_wp a) (p:ex_post a) = wp (fun a -> p (V a))
sub_effect DIV ~> EXN = lift_div_exn
effect Ex (a:Type) = Exn a True (fun v -> True)

let all_pre_h  (h:Type)           = h -> GTot Type0
let all_post_h (h:Type) (a:Type)  = result a -> h -> GTot Type0
let all_wp_h   (h:Type) (a:Type)  = all_post_h h a -> Tot (all_pre_h h)

unfold let all_ite_wp (heap:Type) (a:Type)
                      (wp:all_wp_h heap a)
                      (post:all_post_h heap a) (h0:heap) =
    forall (k:all_post_h heap a).
       (forall (x:result a) (h:heap).{:pattern (guard_free (k x h))} k x h <==> post x h)
       ==> wp k h0
unfold let all_return  (heap:Type) (a:Type) (x:a) (p:all_post_h heap a) = p (V x)
unfold let all_bind_wp (heap:Type) (r1:range) (a:Type) (b:Type)
                       (wp1:all_wp_h heap a)
                       (wp2:(a -> GTot (all_wp_h heap b)))
                       (p:all_post_h heap b) (h0:heap) : GTot Type0 =
  wp1 (fun ra h1 -> (V? ra ==> wp2 (V?.v ra) p h1)) h0

unfold let all_if_then_else (heap:Type) (a:Type) (p:Type)
                             (wp_then:all_wp_h heap a) (wp_else:all_wp_h heap a)
                             (post:all_post_h heap a) (h0:heap) =
   l_ITE p
       (wp_then post h0)
       (wp_else post h0)
unfold let all_stronger (heap:Type) (a:Type) (wp1:all_wp_h heap a)
                        (wp2:all_wp_h heap a) =
    (forall (p:all_post_h heap a) (h:heap). wp1 p h ==> wp2 p h)

unfold let all_close_wp (heap:Type) (a:Type) (b:Type)
                         (wp:(b -> GTot (all_wp_h heap a)))
                         (p:all_post_h heap a) (h:heap) =
    (forall (b:b). wp b p h)
unfold let all_assert_p (heap:Type) (a:Type) (p:Type)
                         (wp:all_wp_h heap a) (q:all_post_h heap a) (h:heap) =
    p /\ wp q h
unfold let all_assume_p (heap:Type) (a:Type) (p:Type)
                         (wp:all_wp_h heap a) (q:all_post_h heap a) (h:heap) =
    p ==> wp q h
unfold let all_null_wp (heap:Type) (a:Type)
                        (p:all_post_h heap a) (h0:heap) =
    (forall (a:result a) (h:heap). p a h)
unfold let all_trivial (heap:Type) (a:Type) (wp:all_wp_h heap a) =
    (forall (h0:heap). wp (fun r h1 -> True) h0)

new_effect {
  ALL_h (heap:Type) : a:Type -> wp:all_wp_h heap a -> Effect
  with
    return_wp    = all_return       heap
  ; bind_wp      = all_bind_wp      heap
  ; if_then_else = all_if_then_else heap
  ; ite_wp       = all_ite_wp       heap
  ; stronger     = all_stronger     heap
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
unopteq type dtuple3 (a:Type)
             (b:(a -> GTot Type))
             (c:(x:a -> b x -> GTot Type)) =
   | Mkdtuple3:_1:a
             -> _2:b _1
             -> _3:c _1 _2
             -> dtuple3 a b c

(* Concrete syntax (x:a & y:b x & z:c x y & d x y z) *)
unopteq type dtuple4 (a:Type)
             (b:(x:a -> GTot Type))
             (c:(x:a -> b x -> GTot Type))
             (d:(x:a -> y:b x -> z:c x y -> GTot Type)) =
 | Mkdtuple4:_1:a
           -> _2:b _1
           -> _3:c _1 _2
           -> _4:d _1 _2 _3
           -> dtuple4 a b c d

(* Concrete syntax (w:a & x:b w & y:c w x & z:d w x y & e w x y z) *)
unopteq type dtuple5 (a:Type)
             (b:(w:a -> GTot Type))
             (c:(w:a -> b w -> GTot Type))
             (d:(w:a -> x:b w -> y:c w x -> GTot Type))
             (e:(w:a -> x:b w -> y:c w x -> z:d w x y -> GTot Type)) =
 | Mkdtuple5:_1:a
           -> _2:b _1
           -> _3:c _1 _2
           -> _4:d _1 _2 _3
           -> _5:e _1 _2 _3 _4
           -> dtuple5 a b c d e

(* Concrete syntax (v:a & w:b v & x:c v w & y:d v w x & z:e v w x y & f v w x y z) *)
unopteq type dtuple6 (a:Type)
             (b:(v:a -> GTot Type))
             (c:(v:a -> b v -> GTot Type))
             (d:(v:a -> w:b v -> x:c v w -> GTot Type))
             (e:(v:a -> w:b v -> x:c v w -> y:d v w x -> GTot Type))
             (f:(v:a -> w:b v -> x:c v w -> y:d v w x -> z:e v w x y -> GTot Type)) =
 | Mkdtuple6:_1:a
           -> _2:b _1
           -> _3:c _1 _2
           -> _4:d _1 _2 _3
           -> _5:e _1 _2 _3 _4
           -> _6:f _1 _2 _3 _4 _5
           -> dtuple6 a b c d e f

(* Concrete syntax (u:a & v:b u & w:c u v & x:d u v w & y:e u v w x & z:f u v w x y & g u v w x y z) *)
unopteq type dtuple7 (a:Type)
             (b:(u:a -> GTot Type))
             (c:(u:a -> b u -> GTot Type))
             (d:(u:a -> v:b u -> w:c u v -> GTot Type))
             (e:(u:a -> v:b u -> w:c u v -> x:d u v w -> GTot Type))
             (f:(u:a -> v:b u -> w:c u v -> x:d u v w -> y:e u v w x -> GTot Type))
             (g:(u:a -> v:b u -> w:c u v -> x:d u v w -> y:e u v w x -> z:f u v w x y -> GTot Type)) =
 | Mkdtuple7:_1:a
           -> _2:b _1
           -> _3:c _1 _2
           -> _4:d _1 _2 _3
           -> _5:e _1 _2 _3 _4
           -> _6:f _1 _2 _3 _4 _5
           -> _7:g _1 _2 _3 _4 _5 _6
           -> dtuple7 a b c d e f g

(* Concrete syntax (t:a & u:b t & v:c t u & w:d t u v & x:e t u v w & y:f t u v w x & z:g t u v w x y & h t u v w x y z) *)
unopteq type dtuple8 (a:Type)
             (b:(t:a -> GTot Type))
             (c:(t:a -> b t -> GTot Type))
             (d:(t:a -> u:b t -> v:c t u -> GTot Type))
             (e:(t:a -> u:b t -> v:c t u -> w:d t u v -> GTot Type))
             (f:(t:a -> u:b t -> v:c t u -> w:d t u v -> x:e t u v w -> GTot Type))
             (g:(t:a -> u:b t -> v:c t u -> w:d t u v -> x:e t u v w -> y:f t u v w x -> GTot Type))
             (h:(t:a -> u:b t -> v:c t u -> w:d t u v -> x:e t u v w -> y:f t u v w x -> z:g t u v w x y -> GTot Type)) =
 | Mkdtuple8:_1:a
           -> _2:b _1
           -> _3:c _1 _2
           -> _4:d _1 _2 _3
           -> _5:e _1 _2 _3 _4
           -> _6:f _1 _2 _3 _4 _5
           -> _7:g _1 _2 _3 _4 _5 _6
           -> _8:h _1 _2 _3 _4 _5 _6 _7
           -> dtuple8 a b c d e f g h

let as_requires (#a:Type) (wp:pure_wp a)  = wp (fun x -> True)
let as_ensures  (#a:Type) (wp:pure_wp a) (x:a) = ~ (wp (fun y -> (y=!=x)))

val fst : ('a * 'b) -> Tot 'a
let fst x = Mktuple2?._1 x

val snd : ('a * 'b) -> Tot 'b
let snd x = Mktuple2?._2 x

val dfst : #a:Type -> #b:(a -> GTot Type) -> dtuple2 a b -> Tot a
let dfst #a #b t = Mkdtuple2?._1 t

val dsnd : #a:Type -> #b:(a -> GTot Type) -> t:dtuple2 a b -> Tot (b (Mkdtuple2?._1 t))
let dsnd #a #b t = Mkdtuple2?._2 t

assume val _assume : p:Type -> unit -> Pure unit (requires (True)) (ensures (fun x -> p))
assume val admit   : #a:Type -> unit -> Admit a
assume val magic   : #a:Type -> unit -> Tot a
irreducible val unsafe_coerce  : #a:Type -> #b: Type -> a -> Tot b
let unsafe_coerce #a #b x = admit(); x
assume val admitP  : p:Type -> Pure unit True (fun x -> p)
val _assert : p:Type -> unit -> Pure unit (requires p) (ensures (fun x -> True))
let _assert p () = ()
val cut     : p:Type -> Pure unit (requires p) (fun x -> p)
let cut p = ()
assume val raise: exn -> Ex 'a       (* TODO: refine with the Exn monad *)


val ignore: #a:Type -> a -> Tot unit
let ignore #a x = ()

type nat = i:int{i >= 0}
type pos = i:int{i > 0}
type nonzero = i:int{i<>0}
let allow_inversion (a:Type)
  : Pure unit (requires True) (ensures (fun x -> inversion a))
  = ()

//allowing inverting option without having to globally increase the fuel just for this
val invertOption : a:Type -> Lemma
  (requires True)
  (ensures (forall (x:option a). None? x \/ Some? x))
  [SMTPatT (option a)]
let invertOption a = allow_inversion (option a)


(*    For the moment we require not just that the divisor is non-zero, *)
(*    but also that the dividend is natural. This works around a *)
(*    mismatch between the semantics of integer division in SMT-LIB and *)
(*    in F#/OCaml. For SMT-LIB ints the modulus is always positive (as in *)
(*    math Euclidian division), while for F#/OCaml ints the modulus has *)
(*    the same sign as the dividend.                                    *)

(*    Our arbitrary precision ints are compiled to zarith (big_ints)  *)
(*    in OCaml. Although in F# they are still compiled to platform-specific *)
(*    finite integers---this should eventually change to .NET BigInteger *)
assume val op_Modulus            : int -> nonzero -> Tot int
assume val op_Division           : nat -> nonzero -> Tot int

let rec pow2 (x:nat) : Tot pos =
  match x with
  | 0  -> 1
  | _  -> 2 `op_Multiply` (pow2 (x-1))

let abs (x:int) : Tot int = if x >= 0 then x else -x

assume val string_of_bool: bool -> Tot string
assume val string_of_int: int -> Tot string

(*********************************************************************************)
(* Marking terms for normalization *)
(*********************************************************************************)
abstract let normalize_term (#a:Type) (x:a) : a = x
abstract let normalize (a:Type0) = a

val assert_norm : p:Type -> Pure unit (requires (normalize p)) (ensures (fun _ -> p))
let assert_norm p = ()
