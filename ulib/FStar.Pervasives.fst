(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Pervasives

(* This is a file from the core library, dependencies must be explicit *)
open Prims
include FStar.Pervasives.Native

unfold
let id (#a:Type) (x:a) : a = x

unfold
let trivial_pure_post (a:Type) : pure_post a = fun _ -> True

(* Sometimes it is convenient to explicit introduce nullary symbols
 * into the ambient context, so that SMT can appeal to their definitions
 * even when they are no mentioned explicitly in the program, e.g., when
 * needed for triggers.
 * Use `intro_ambient t` for that.
 * See, e.g., LowStar.Monotonic.Buffer.fst and its usage there for loc_none
 *)
abstract
let ambient (#a:Type) (x:a) = True
abstract
let intro_ambient (#a:Type) (x:a) : squash (ambient x) = ()

new_effect DIV = PURE
sub_effect PURE ~> DIV  = purewp_id

effect Div (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
       DIV a (fun (p:pure_post a) -> pre /\ (forall a. post a ==> p a))

effect Dv (a:Type) =
     DIV a (fun (p:pure_post a) -> (forall (x:a). p x))

(* We use the EXT effect to underspecify external system calls
   as being impure but having no observable effect on the state *)
effect EXT (a:Type) = Dv a

let st_pre_h   (heap:Type) = heap -> GTot Type0
let st_post_h' (heap:Type) (a:Type) (pre:Type) = a -> (_:heap{pre}) -> GTot Type0
let st_post_h  (heap:Type) (a:Type) = st_post_h' heap a True
let st_wp_h    (heap:Type) (a:Type) = st_post_h heap a -> Tot (st_pre_h heap)

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
	 (forall (x:a) (h:heap).{:pattern (guard_free (k x h))} post x h ==> k x h)
	 ==> wp k h0
unfold let st_stronger  (heap:Type) (a:Type) (wp1:st_wp_h heap a)
                        (wp2:st_wp_h heap a) =
     (forall (p:st_post_h heap a) (h:heap). wp1 p h ==> wp2 p h)

unfold let st_close_wp      (heap:Type) (a:Type) (b:Type)
                             (wp:(b -> GTot (st_wp_h heap a)))
                             (p:st_post_h heap a) (h:heap) =
     (forall (b:b). wp b p h)
unfold let st_trivial       (heap:Type) (a:Type)
                             (wp:st_wp_h heap a) =
     (forall h0. wp (fun r h1 -> True) h0)

new_effect {
  STATE_h (heap:Type) : result:Type -> wp:st_wp_h heap result -> Effect
  with return_wp    = st_return heap
     ; bind_wp      = st_bind_wp heap
     ; if_then_else = st_if_then_else heap
     ; ite_wp       = st_ite_wp heap
     ; stronger     = st_stronger heap
     ; close_wp     = st_close_wp heap
     ; trivial      = st_trivial heap
}


noeq type result (a:Type) =
  | V   : v:a -> result a
  | E   : e:exn -> result a
  | Err : msg:string -> result a

(* Effect EXCEPTION *)
let ex_pre  = Type0
let ex_post' (a:Type) (pre:Type) = (_:result a{pre}) -> GTot Type0
let ex_post  (a:Type) = ex_post' a True
let ex_wp    (a:Type) = ex_post a -> GTot ex_pre
unfold let ex_return   (a:Type) (x:a) (p:ex_post a) : GTot Type0 = p (V x)
unfold let ex_bind_wp (r1:range) (a:Type) (b:Type)
		       (wp1:ex_wp a)
		       (wp2:(a -> GTot (ex_wp b))) (p:ex_post b)
         : GTot Type0 =
  forall (k:ex_post b).
     (forall (rb:result b).{:pattern (guard_free (k rb))} p rb ==> k rb)
     ==> (wp1 (function
               | V ra1 -> wp2 ra1 k
               | E e -> k (E e)
               | Err m -> k (Err m)))

unfold let ex_ite_wp (a:Type) (wp:ex_wp a) (post:ex_post a) =
  forall (k:ex_post a).
     (forall (rb:result a).{:pattern (guard_free (k rb))} post rb ==> k rb)
     ==> wp k

unfold let ex_if_then_else (a:Type) (p:Type) (wp_then:ex_wp a) (wp_else:ex_wp a) (post:ex_post a) =
   l_ITE p
       (wp_then post)
       (wp_else post)
unfold let ex_stronger (a:Type) (wp1:ex_wp a) (wp2:ex_wp a) =
        (forall (p:ex_post a). wp1 p ==> wp2 p)

unfold let ex_close_wp (a:Type) (b:Type) (wp:(b -> GTot (ex_wp a))) (p:ex_post a) = (forall (b:b). wp b p)
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
  ; trivial      = ex_trivial
}
effect Exn (a:Type) (pre:ex_pre) (post:ex_post' a pre) =
       EXN a (fun (p:ex_post a) -> pre /\ (forall (r:result a). post r ==> p r))

unfold let lift_div_exn (a:Type) (wp:pure_wp a) (p:ex_post a) = wp (fun a -> p (V a))
sub_effect DIV ~> EXN = lift_div_exn
effect Ex (a:Type) = Exn a True (fun v -> True)

let all_pre_h   (h:Type)           = h -> GTot Type0
let all_post_h' (h:Type) (a:Type) (pre:Type)  = result a -> (_:h{pre}) -> GTot Type0
let all_post_h  (h:Type) (a:Type)  = all_post_h' h a True
let all_wp_h    (h:Type) (a:Type)  = all_post_h h a -> Tot (all_pre_h h)

unfold let all_ite_wp (heap:Type) (a:Type)
                      (wp:all_wp_h heap a)
                      (post:all_post_h heap a) (h0:heap) =
    forall (k:all_post_h heap a).
       (forall (x:result a) (h:heap).{:pattern (guard_free (k x h))} post x h ==> k x h)
       ==> wp k h0
unfold let all_return  (heap:Type) (a:Type) (x:a) (p:all_post_h heap a) = p (V x)
unfold let all_bind_wp (heap:Type) (r1:range) (a:Type) (b:Type)
                       (wp1:all_wp_h heap a)
                       (wp2:(a -> GTot (all_wp_h heap b)))
                       (p:all_post_h heap b) (h0:heap) : GTot Type0 =
  wp1 (fun ra h1 -> (match ra with
                  | V v     -> wp2 v p h1
		  | E e     -> p (E e) h1
		  | Err msg -> p (Err msg) h1)) h0

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
  ; trivial      = all_trivial      heap
}

(* An SMT-pattern to control unfolding inductives;
   In a proof, you can say `allow_inversion (option a)`
   to allow the SMT solver. cf. allow_inversion below
 *)
let inversion (a:Type) = True

let allow_inversion (a:Type)
  : Pure unit (requires True) (ensures (fun x -> inversion a))
  = ()

//allowing inverting option without having to globally increase the fuel just for this
val invertOption : a:Type -> Lemma
  (requires True)
  (ensures (forall (x:option a). None? x \/ Some? x))
  [SMTPat (option a)]
let invertOption a = allow_inversion (option a)

type either 'a 'b =
  | Inl : v:'a -> either 'a 'b
  | Inr : v:'b -> either 'a 'b



val dfst : #a:Type -> #b:(a -> GTot Type) -> dtuple2 a b -> Tot a
let dfst #a #b t = Mkdtuple2?._1 t

val dsnd : #a:Type -> #b:(a -> GTot Type) -> t:dtuple2 a b -> Tot (b (Mkdtuple2?._1 t))
let dsnd #a #b t = Mkdtuple2?._2 t

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

val ignore: #a:Type -> a -> Tot unit
let ignore #a x = ()
irreducible
let rec false_elim (#a:Type) (u:unit{false}) : Tot a = false_elim ()

(* These are the supported attributes for top-level declarations. Syntax
 * example:
 *   [@ Gc ] type list a = | Nil | Cons of a * list a
 * or:
 *   [@ CInline ] let f x = UInt32.(x +%^ 1)
 *
 * Please add new attributes to this list along with a comment! Attributes are
 * desugared but not type-checked; using the constructors of a data type
 * guarantees a minimal amount of typo-checking.
 * *)
type __internal_ocaml_attributes =
  | PpxDerivingShow
    (* Generate [@@ deriving show ] on the resulting OCaml type *)
  | PpxDerivingShowConstant of string
    (* Similar, but for constant printers. *)
  | PpxDerivingYoJson
    (* Generate [@@ deriving yojson ] on the resulting OCaml type *)
  | CInline
    (* KreMLin-only: generates a C "inline" attribute on the resulting
     * function declaration. *)
  | Substitute
    (* KreMLin-only: forces KreMLin to inline the function at call-site; this is
     * deprecated and the recommended way is now to use F*'s
     * [inline_for_extraction], which now also works for stateful functions. *)
  | Gc
    (* KreMLin-only: instructs KreMLin to heap-allocate any value of this
     * data-type; this requires running with a conservative GC as the
     * allocations are not freed. *)
  | Comment of string
    (* KreMLin-only: attach a comment to the declaration. Note that using F*-doc
     * syntax automatically fills in this attribute. *)
  | CPrologue of string
    (* KreMLin-only: verbatim C code to be prepended to the declaration.
     * Multiple attributes are valid and accumulate, separated by newlines. *)
  | CEpilogue of string
    (* Ibid. *)
  | CConst of string
    (* KreMLin-only: indicates that the parameter with that name is to be marked
     * as C const.  This will be checked by the C compiler, not by KreMLin or F*.
     *
     * This is deprecated and doesn't work as intended. Use
     * LowStar.ConstBuffer.fst instead! *)
  | CCConv of string
    (* A calling convention for C, one of stdcall, cdecl, fastcall *)
  | CAbstractStruct
    (* KreMLin-only: for types that compile to struct types (records and
     * inductives), indicate that the header file should only contain a forward
     * declaration, which in turn forces the client to only ever use this type
     * through a pointer. *)
  | CIfDef
    (* KreMLin-only: on a given `val foo`, compile if foo with #ifdef. *)
  | CMacro
    (* KreMLin-only: for a top-level `let v = e`, compile as a macro *)

(* Some supported attributes encoded using functions. *)

irreducible
let inline_let : unit = ()

irreducible
let plugin (x:int) : unit = ()

(* An attribute to mark things that the typechecker should *first*
 * elaborate and typecheck, but unfold before verification. *)
irreducible
let tcnorm : unit = ()

(*
 * we now erase all pure and ghost functions with unit return type to unit
 * this creates a small issue with abstract types. consider a module that
 * defines an abstract type t whose (internal) definition is unit and it also
 * defines a function f: int -> t.
 * with this new scheme, f would be erased to be just () inside the module
 * while the client calls to f would not, since t is abstract.
 * to get around this, when extracting interfaces, if we encounter an abstract type,
 * we will tag it with this attribute, so that extraction can treat it specially.
 *)
irreducible
let must_erase_for_extraction :unit = ()

let dm4f_bind_range : unit = ()

(** When attached a top-level definition, the typechecker will succeed
 * if and only if checking the definition results in an error. The
 * error number list is actually OPTIONAL. If present, it will be
 * checked that the definition raises exactly those errors in the
 * specified multiplicity, but order does not matter. *)
irreducible
let expect_failure (errs : list int) : unit = ()

(** When --lax is present, we the previous attribute since some definitions
 * only fail when verification is turned on. With this attribute, one can ensure
 * that a definition fails while lax-checking too. Same semantics as above,
 * but lax mode will be turned on for the definition.
 *)
irreducible
let expect_lax_failure (errs : list int) : unit = ()

(** Print the time it took to typecheck a top-level definition *)
irreducible
let tcdecltime : unit = ()

(**
 * **THIS ATTRIBUTE IS AN ESCAPE HATCH AND CAN BREAK SOUNDNESS**
 * **USE WITH CARE**
 * The positivity check for inductive types stops at abstraction
 * boundaries. This results in spurious errors about positivity,
 * e.g., when defining types like `type t = ref (option t)`
 * By adding this attribute to a declaration of a top-level name
 * positivity checks on applications of that name are admitted.
 * See, for instance, FStar.Monotonic.Heap.mref
 * We plan to decorate binders of abstract types with polarities
 * to allow us to check positivity across abstraction boundaries
 * and will eventually remove this attribute.
 *)
irreducible
let assume_strictly_positive : unit = ()

(**
 * This attribute is to be used as a hint for the unifier.
 * A function-typed symbol `t` marked with this attribute
 * will be treated as being injective in all its arguments
 * by the unifier.
 * That is, given a problem `t a1..an =?= t b1..bn`
 * the unifier will solve it by proving `ai =?= bi` for
 * all `i`, without trying to unfold the definition of `t`.
 **)
irreducible
let unifier_hint_injective : unit = ()

(**
 * This attribute is used to control the evaluation order
 * and unfolding strategy for certain definitions.
 *
 * In particular, given 
 *    [@(strict_on_arguments [1;2])]
 *    let f x0 (x1:list x0) (x1:option x0) = e
 *
 * An application `f e0 e1 e2` is reduced by the normalizer by:
 *   1. evaluating e0 ~>* v0, e1 ~>* v1, e2 ~>* v2
 *
 *   2 a.
 *      If, according to the positional arguments [1;2], 
 *      if v1 and v2 have constant head symbols 
 *             (e.g., v1 = Cons _ _ _, and v2 = None _)
 *      then `f` is unfolded to `e` and reduced as
 *        e[v0/x0][v1/x1][v2/x2]
 *       
 *   2 b. 
 *
 *     Otherwise, `f` is not unfolded and the term is `f e0 e1 e2`
 *     reduces to `f v0 v1 v2`.
 *
 *)
irreducible
let strict_on_arguments (x:list int) : unit = ()

(**
 * This attribute can be added to an inductive type definition, 
 * indicating that it should be erased on extraction to `unit`.
 * 
 * However, any pattern matching on the inductive type results 
 * in a `Ghost` effect, ensuring that computationally relevant
 * code cannot rely on the values of the erasable type.
 *
 * See examples/micro-benchmarks/Erasable.fst, for examples.
 * Also see https://github.com/FStarLang/FStar/issues/1844
 *)
irreducible
let erasable : unit = ()

(*********************************************************************************)
(* Marking terms for normalization *)
(*********************************************************************************)
abstract let normalize_term (#a:Type) (x:a) : a = x
abstract let normalize (a:Type0) :Type0 = a

abstract
noeq type norm_step =
  | Simpl
  | Weak
  | HNF
  | Primops
  | Delta
  | Zeta
  | Iota
  | NBE // use NBE instead of the normalizer
  | Reify
  | UnfoldOnly  : list string -> norm_step // each string is a fully qualified name like `A.M.f`
  | UnfoldFully : list string -> norm_step // idem
  | UnfoldAttr  : list string -> norm_step

// Helpers, so we don't expose the actual inductive
abstract let simplify : norm_step = Simpl
abstract let weak     : norm_step = Weak
abstract let hnf      : norm_step = HNF
abstract let primops  : norm_step = Primops
abstract let delta    : norm_step = Delta
abstract let zeta     : norm_step = Zeta
abstract let iota     : norm_step = Iota
abstract let nbe      : norm_step = NBE
abstract let reify_   : norm_step = Reify
abstract let delta_only  (s : list string) : norm_step = UnfoldOnly s
abstract let delta_fully (s : list string) : norm_step = UnfoldFully s
abstract let delta_attr  (s : list string) : norm_step = UnfoldAttr s

// Normalization marker
abstract let norm (s:list norm_step) (#a:Type) (x:a) : a = x

abstract val assert_norm : p:Type -> Pure unit (requires (normalize p)) (ensures (fun _ -> p))
let assert_norm p = ()

let normalize_term_spec (#a: Type) (x: a) : Lemma (normalize_term #a x == x) = ()
let normalize_spec (a: Type0) : Lemma (normalize a == a) = ()
let norm_spec (s: list norm_step) (#a: Type) (x: a) : Lemma (norm s #a x == x) = ()

(*
 * Use the following to expose an `opaque_to_smt` definition to the solver
 *   as: `reveal_opaque (`%defn) defn
 *)
let reveal_opaque (s:string) = norm_spec [delta_only [s]]

(*
 * Pure and ghost inner let bindings are now always inlined during the wp computation, if:
 * the return type is not unit and the head symbol is not marked irreducible.
 * To circumvent this behavior, singleton can be used.
 * See the example usage in ulib/FStar.Algebra.Monoid.fst.
 *)
irreducible let singleton (#a:Type) (x:a) :(y:a{y == x}) = x


(*
 * `with_type t e` is just an identity function, but it receives special treatment
 *  in the SMT encoding, where in addition to being an identity function, we have
 *  an SMT axiom:
 *  `forall t e.{:pattern (with_type t e)} has_type (with_type t e) t`
 *)
let with_type (#t:Type) (e:t) = e
