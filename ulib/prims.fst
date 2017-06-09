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

(* bool is a two element type with elements {'true', 'false'}
    we assume it is primitive, for convenient interop with other languages *)
assume new type bool : Type0
assume HasEq_bool: hasEq bool

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

(* The usual equality defined as an inductive type *)
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
             (fun (p:pure_post a) -> pre /\ (forall (x:a). post x ==> p x)) // pure_wp
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

(* This new bit for Dijkstra Monads for Free; it has a "double meaning",
 * either as an alias for reasoning about the direct definitions, or as a marker
 * for places where a CPS transformation should happen. *)
effect M (a:Type) = Tot a (attributes cps)

let returnM (a:Type) (x:a) : M a = x

type lex_t =
  | LexTop  : lex_t
  | LexCons : #a:Type -> a -> lex_t -> lex_t

let as_requires (#a:Type) (wp:pure_wp a)  = wp (fun x -> True)
let as_ensures  (#a:Type) (wp:pure_wp a) (x:a) = ~ (wp (fun y -> (y=!=x)))

assume val _assume : p:Type -> Pure unit (requires (True)) (ensures (fun x -> p))
assume val admit   : #a:Type -> unit -> Admit a
assume val magic   : #a:Type -> unit -> Tot a
irreducible val unsafe_coerce  : #a:Type -> #b: Type -> a -> Tot b
let unsafe_coerce #a #b x = admit(); x
assume val admitP  : p:Type -> Pure unit True (fun x -> p)
val _assert : p:Type -> Pure unit (requires p) (ensures (fun x -> p))
let _assert p = ()
val cut     : p:Type -> Pure unit (requires p) (fun x -> p)
let cut p = ()

type nat = i:int{i >= 0}
type pos = i:int{i > 0}
type nonzero = i:int{i<>0}

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

let min x y = if x <= y then x else y

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
