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

type eqtype = a:Type0{hasEq a}

(* bool is a two element type with elements {'true', 'false'}
    we assume it is primitive, for convenient interop with other languages *)
assume new type bool : eqtype

(* False is the empty inductive type *)
type c_False =

(* True is the singleton inductive type *)
type c_True =
  | T

(* another singleton type, with its only inhabitant written '()'
   we assume it is primitive, for convenient interop with other languages *)
assume new type unit : eqtype

(* A coercion down to universe 0 *)
[@ "tac_opaque"]
type squash (p:Type) : Type0 = x:unit{p}

(* F* will automatically insert `auto_squash` when simplifying terms,
   converting terms of the form `p /\ True` to `auto_squash p`.

   We distinguish these automatically inserted squashes from explicit,
   user-written squashes.

   It's marked `private` so that users cannot write it themselves.
*)
private
let auto_squash (p:Type) = squash p

(*
 * transition to prop and its enforcement
 *)
private type logical = Type0

(*
 * An attribute indicating that a symbol is an smt theory symbol
 *   and hence may not be used in smt patterns
 *
 * The typechecker warns if such symbols are used in patterns
 *)
assume val smt_theory_symbol : attribute

(*
 * Squashed versions of truth and falsehood
 *)
[@"tac_opaque" smt_theory_symbol]
let l_True :logical = squash c_True

[@ "tac_opaque" smt_theory_symbol]
let l_False :logical = squash c_False

(* The usual equality defined as an inductive type *)
type equals (#a:Type) (x:a) : a -> Type =
  | Refl : equals x x

(* infix binary '==';
   proof irrelevant, heterogeneous equality in Type#0
*)
//TODO: instead of hard-wiring the == syntax,
//       we should just rename eq2 to op_Equals_Equals

[@ "tac_opaque" smt_theory_symbol]
type eq2 (#a:Type) (x:a) (y:a) :logical = squash (equals x y)

(* Heterogeneous equality *)
type h_equals (#a:Type) (x:a) : #b:Type -> b -> Type =
  | HRefl : h_equals x x

(* A proof-irrelevant version of h_equals *)
[@ "tac_opaque" smt_theory_symbol]
type eq3 (#a:Type) (#b:Type) (x:a) (y:b) :logical = squash (h_equals x y)

unfold
let op_Equals_Equals_Equals (#a:Type) (#b:Type) (x:a) (y:b) = eq3 x y

(* bool-to-type coercion *)
type b2t (b:bool) :logical = (b == true)

(* constructive conjunction *)
type c_and  (p:Type) (q:Type) =
  | And   : p -> q -> c_and p q

(* '/\'  : specialized to Type#0 *)
[@ "tac_opaque" smt_theory_symbol]
type l_and (p q:logical) :logical = squash (c_and p q)

(* constructive disjunction *)
type c_or   (p:Type) (q:Type) =
  | Left  : p -> c_or p q
  | Right : q -> c_or p q

(* '\/'  : specialized to Type#0 *)
[@ "tac_opaque" smt_theory_symbol]
type l_or (p q:logical) :logical = squash (c_or p q)

(* '==>' : specialized to Type#0 *)
[@ "tac_opaque" smt_theory_symbol]
type l_imp (p q:logical) :logical = squash (p -> GTot q)
                                         (* ^^^ NB: The GTot effect is primitive;            *)
                                         (*         elaborated using GHOST a few lines below *)
(* infix binary '<==>' *)
[@smt_theory_symbol]
type l_iff (p q:logical) :logical = (p ==> q) /\ (q ==> p)

(* prefix unary '~' *)
[@smt_theory_symbol]
type l_not (p:logical) :logical = l_imp p False

unfold
type l_ITE (p q r:logical) :logical = (p ==> q) /\ (~p ==> r)

(* infix binary '<<'; a built-in well-founded partial order over all terms *)
assume
type precedes : #a:Type -> #b:Type -> a -> b -> Type0

(* internalizing the typing relation for the SMT encoding: (has_type x t) *)
assume
type has_type : #a:Type -> a -> Type -> Type0

(* forall (x:a). p x : specialized to Type#0 *)
[@ "tac_opaque" smt_theory_symbol]
type l_Forall (#a:Type) (p:a -> GTot Type0) :logical = squash (x:a -> GTot (p x))

let subtype_of (p1:Type) (p2:Type) = forall (x:p1). has_type x p2

(* The type of squashed types *)
type prop = a:Type0{ a `subtype_of` unit }

(* range is a type for the internal representations of source ranges
         The functions that follow below allow manipulating ranges
         abstractly.  Importantly, while we allow constructing ranges,
         we do not allow destructing them, since that would reveal
         that internally, set_range_of is not an identity function.
*)
assume new
type range : Type0

assume new
type string : eqtype

(* PURE effect *)
let pure_pre = Type0
let pure_post' (a:Type) (pre:Type) = (_:a{pre}) -> GTot Type0 // c.f. #57
let pure_post  (a:Type) = pure_post' a True
let pure_wp    (a:Type) = pure_post a -> GTot pure_pre

assume
type guard_free: Type0 -> Type0

unfold
let pure_return (a:Type) (x:a) (p:pure_post a) =
     forall (return_val:a). return_val==x ==> p return_val

unfold
let pure_bind_wp (r1:range) (a:Type) (b:Type)
                   (wp1:pure_wp a) (wp2: (a -> GTot (pure_wp b)))
                   (p : pure_post b) =
	wp1 (fun (bind_result_1:a) -> wp2 bind_result_1 p)

unfold
let pure_if_then_else (a:Type) (p:Type) (wp_then:pure_wp a) (wp_else:pure_wp a) (post:pure_post a) =
     l_ITE p (wp_then post) (wp_else post)

unfold
let pure_ite_wp (a:Type) (wp:pure_wp a) (post:pure_post a) =
     forall (k:pure_post a).
         (forall (x:a).{:pattern (guard_free (k x))} post x ==> k x)
         ==> wp k

unfold
let pure_stronger (a:Type) (wp1:pure_wp a) (wp2:pure_wp a) =
     forall (p:pure_post a). wp1 p ==> wp2 p

unfold
let pure_close_wp (a:Type) (b:Type) (wp:(b -> GTot (pure_wp a))) (p:pure_post a) = forall (b:b). wp b p

unfold
let pure_assert_p (a:Type) (q:Type) (wp:pure_wp a) (p:pure_post a) = q /\ wp p

unfold
let pure_assume_p (a:Type) (q:Type) (wp:pure_wp a) (p:pure_post a) = q ==> wp p

unfold
let pure_null_wp  (a:Type) (p:pure_post a) = forall (any_result:a). p any_result

unfold
let pure_trivial  (a:Type) (wp:pure_wp a) = wp (fun (trivial_result:a) -> True)

total
new_effect { (* The definition of the PURE effect is fixed; no user should ever change this *)
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

// Note the type of post, which allows to assume the precondition
// for the well-formedness of the postcondition. c.f. #57
effect Pure (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
        PURE a (fun (p:pure_post a) -> pre /\ (forall (pure_result:a). post pure_result ==> p pure_result))

effect Admit (a:Type) = PURE a (fun (p:pure_post a) -> True)

(* The primitive effect Tot is definitionally equal to an instance of PURE *)
effect Tot (a:Type) = PURE a (pure_null_wp a)

total
new_effect GHOST = PURE

unfold
let purewp_id (a:Type) (wp:pure_wp a) = wp

sub_effect
  PURE ~> GHOST = purewp_id

(* The primitive effect GTot is definitionally equal to an instance of GHOST *)
effect GTot (a:Type) = GHOST a (pure_null_wp a)
effect Ghost (a:Type) (pre:Type) (post:pure_post' a pre) =
       GHOST a (fun (p:pure_post a) -> pre /\ (forall (ghost_result:a). post ghost_result ==> p ghost_result))

(* dependent pairs DTuple2 in concrete syntax is '(x:a & b x)' *)
unopteq
type dtuple2 (a:Type)
             (b:(a -> GTot Type)) =
  | Mkdtuple2: _1:a
            -> _2:b _1
            -> dtuple2 a b

(* exists (x:a). p x : specialized to Type#0 *)
[@ "tac_opaque" smt_theory_symbol]
type l_Exists (#a:Type) (p:a -> GTot Type0) :logical = squash (x:a & p x)

assume new
type int : eqtype

assume
val range_0 : range

(* A total function to obtain the range of a term x *)
(* assume val range_of : #a:Type -> x:a -> Tot range *)
(* Building a range constant *)
assume
val mk_range : file:string -> from_line:int -> from_col:int -> to_line:int -> to_col:int -> Tot range

(* Tagging a term x with the range r *)
(* let set_range_of (#a:Type) (x:a) (r:range) = x *)

[@smt_theory_symbol]
assume
val op_AmpAmp             : bool -> bool -> Tot bool

[@smt_theory_symbol]
assume
val op_BarBar             : bool -> bool -> Tot bool

[@smt_theory_symbol]
assume
val op_Negation           : bool -> Tot bool

[@smt_theory_symbol]
assume
val op_Multiply           : int -> int -> Tot int

[@smt_theory_symbol]
assume
val op_Subtraction        : int -> int -> Tot int

[@smt_theory_symbol]
assume
val op_Addition           : int -> int -> Tot int

[@smt_theory_symbol]
assume
val op_Minus              : int -> Tot int

[@smt_theory_symbol]
assume
val op_LessThanOrEqual    : int -> int -> Tot bool

[@smt_theory_symbol]
assume
val op_GreaterThan        : int -> int -> Tot bool

[@smt_theory_symbol]
assume
val op_GreaterThanOrEqual : int -> int -> Tot bool

[@smt_theory_symbol]
assume
val op_LessThan           : int -> int -> Tot bool

[@smt_theory_symbol]
assume
val op_Equality :    #a:eqtype -> a -> a -> Tot bool

[@smt_theory_symbol]
assume
val op_disEquality : #a:eqtype -> a -> a -> Tot bool

assume new
type exn : Type0

assume new
type array : Type -> Type0


(*
 * to be used in attributes
 * s is the altertive function that should be printed in the warning
 * it can be omitted if the use case has no such function
 *)
irreducible
let deprecated (s:string) : unit = ()

assume val strcat : string -> string -> Tot string
inline_for_extraction unfold let (^) s1 s2 = strcat s1 s2

type list (a:Type) =
  | Nil  : list a
  | Cons : hd:a -> tl:list a -> list a

abstract
type pattern :Type0 = unit

// SMTPat and SMTPatOr desugar to these two
irreducible
let smt_pat (#a:Type) (x:a) : pattern = ()

irreducible
let smt_pat_or (x:list (list pattern)) : pattern = ()

assume
type decreases : #a:Type -> a -> Type0

(*
   Lemma is desugared specially. The valid forms are:

     Lemma (ensures post)
     Lemma post [SMTPat ...]
     Lemma (ensures post) [SMTPat ...]
     Lemma (ensures post) (decreases d)
     Lemma (ensures post) (decreases d) [SMTPat ...]
     Lemma (requires pre) (ensures post) (decreases d)
     Lemma (requires pre) (ensures post) [SMTPat ...]
     Lemma (requires pre) (ensures post) (decreases d) [SMTPat ...]

   and

     Lemma post    (== Lemma (ensures post))

   the squash argument on the postcondition allows to assume the
   precondition for the *well-formedness* of the postcondition.
   C.f. #57.
*)
effect Lemma (a:Type) (pre:Type) (post:squash pre -> Type) (pats:list pattern) =
       Pure a pre (fun r -> post ())

(* This new bit for Dijkstra Monads for Free; it has a "double meaning",
 * either as an alias for reasoning about the direct definitions, or as a marker
 * for places where a CPS transformation should happen. *)
effect M (a:Type) = Tot a (attributes cps)

let returnM (a:Type) (x:a) : M a = x

type lex_t =
  | LexTop  : lex_t
  | LexCons : #a:Type -> a -> lex_t -> lex_t

unfold
let as_requires (#a:Type) (wp:pure_wp a)  = wp (fun x -> True)
unfold
let as_ensures  (#a:Type) (wp:pure_wp a) (x:a) = ~ (wp (fun y -> (y=!=x)))

assume
val _assume : p:Type -> Pure unit (requires (True)) (ensures (fun x -> p))

assume
val admit   : #a:Type -> unit -> Admit a

assume
val magic   : #a:Type -> unit -> Tot a

irreducible
let unsafe_coerce (#a:Type) (#b: Type) (x:a) : b = admit (); x

assume
val admitP  : p:Type -> Pure unit True (fun x -> p)

val _assert : p:Type -> Pure unit (requires p) (ensures (fun x -> p))

let _assert p = ()

// Can be used to mark a query for a separate SMT invocation
abstract
let spinoff (p:Type) : Type = p

// Logically equivalent to assert, but spins off separate query
val assert_spinoff : (p:Type) -> Pure unit (requires (spinoff (squash p))) (ensures (fun x -> p))
let assert_spinoff p = ()

val cut : p:Type -> Pure unit (requires p) (fun x -> p)
let cut p = ()

type nat = i:int{i >= 0}
type pos = i:int{i > 0}
type nonzero = i:int{i<>0}

(*    Arbitrary precision ints are compiled to zarith (big_ints)       *)
(*    in OCaml and to .NET BigInteger in F#. Both these operations are *)
(*    Euclidean and are mapped to the corresponding theory symbols in  *)
(*    the SMT encoding *)
[@smt_theory_symbol]
assume
val op_Modulus            : int -> nonzero -> Tot int

[@smt_theory_symbol]
assume
val op_Division           : int -> nonzero -> Tot int

let rec pow2 (x:nat) : Tot pos =
  match x with
  | 0  -> 1
  | _  -> 2 `op_Multiply` (pow2 (x-1))

let min x y = if x <= y then x else y

let abs (x:int) : Tot int = if x >= 0 then x else -x

assume
val string_of_bool: bool -> Tot string

assume
val string_of_int: int -> Tot string

irreducible
let labeled (r:range) (msg:string) (b:Type) :Type = b

(* THIS IS MEANT TO BE KEPT IN SYNC WITH FStar.CheckedFiles.fs
   Incrementing this forces all .checked files to be invalidated *)
private
abstract
let __cache_version_number__ = 12
