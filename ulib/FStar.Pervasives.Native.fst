module FStar.Pervasives.Native
open Prims

type option (a: Type) =
  | None : option a
  | Some : v: a -> option a

(* 'a * 'b *)
type tuple2 'a 'b = | Mktuple2 : _1: 'a -> _2: 'b -> tuple2 'a 'b

let fst (x: tuple2 'a 'b) : 'a = Mktuple2?._1 x

let snd (x: tuple2 'a 'b) : 'b = Mktuple2?._2 x

(* 'a * 'b * 'c *)
type tuple3 'a 'b 'c = | Mktuple3 : _1: 'a -> _2: 'b -> _3: 'c -> tuple3 'a 'b 'c

(* 'a * 'b * 'c * 'd *)
type tuple4 'a 'b 'c 'd = | Mktuple4 : _1: 'a -> _2: 'b -> _3: 'c -> _4: 'd -> tuple4 'a 'b 'c 'd

(* 'a * 'b * 'c * 'd * 'e *)
type tuple5 'a 'b 'c 'd 'e =
  | Mktuple5 : _1: 'a -> _2: 'b -> _3: 'c -> _4: 'd -> _5: 'e -> tuple5 'a 'b 'c 'd 'e

(* 'a * 'b * 'c * 'd * 'e * 'f *)
type tuple6 'a 'b 'c 'd 'e 'f =
  | Mktuple6 : _1: 'a -> _2: 'b -> _3: 'c -> _4: 'd -> _5: 'e -> _6: 'f -> tuple6 'a 'b 'c 'd 'e 'f

(* 'a * 'b * 'c * 'd * 'e * 'f * 'g *)
type tuple7 'a 'b 'c 'd 'e 'f 'g =
  | Mktuple7 : _1: 'a -> _2: 'b -> _3: 'c -> _4: 'd -> _5: 'e -> _6: 'f -> _7: 'g ->
    tuple7 'a 'b 'c 'd 'e 'f 'g

(* 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h *)
type tuple8 'a 'b 'c 'd 'e 'f 'g 'h =
  | Mktuple8 : _1: 'a -> _2: 'b -> _3: 'c -> _4: 'd -> _5: 'e -> _6: 'f -> _7: 'g -> _8: 'h ->
    tuple8 'a 'b 'c 'd 'e 'f 'g 'h

(* 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i *)
type tuple9 'a 'b 'c 'd 'e 'f 'g 'h 'i =
  | Mktuple9 : 
    _1: 'a ->
    _2: 'b ->
    _3: 'c ->
    _4: 'd ->
    _5: 'e ->
    _6: 'f ->
    _7: 'g ->
    _8: 'h ->
    _9: 'i ->
    tuple9 'a 'b 'c 'd 'e 'f 'g 'h 'i

(* 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j *)
type tuple10 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j =
  | Mktuple10 : 
    _1: 'a ->
    _2: 'b ->
    _3: 'c ->
    _4: 'd ->
    _5: 'e ->
    _6: 'f ->
    _7: 'g ->
    _8: 'h ->
    _9: 'i ->
    _10: 'j ->
    tuple10 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j

(* 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k *)
type tuple11 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k =
  | Mktuple11 : 
    _1: 'a ->
    _2: 'b ->
    _3: 'c ->
    _4: 'd ->
    _5: 'e ->
    _6: 'f ->
    _7: 'g ->
    _8: 'h ->
    _9: 'i ->
    _10: 'j ->
    _11: 'k ->
    tuple11 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k

(* 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l *)
type tuple12 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l =
  | Mktuple12 : 
    _1: 'a ->
    _2: 'b ->
    _3: 'c ->
    _4: 'd ->
    _5: 'e ->
    _6: 'f ->
    _7: 'g ->
    _8: 'h ->
    _9: 'i ->
    _10: 'j ->
    _11: 'k ->
    _12: 'l ->
    tuple12 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l

(* 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm *)
type tuple13 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm =
  | Mktuple13 : 
    _1: 'a ->
    _2: 'b ->
    _3: 'c ->
    _4: 'd ->
    _5: 'e ->
    _6: 'f ->
    _7: 'g ->
    _8: 'h ->
    _9: 'i ->
    _10: 'j ->
    _11: 'k ->
    _12: 'l ->
    _13: 'm ->
    tuple13 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm

(* 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm * 'n *)
type tuple14 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm 'n =
  | Mktuple14 : 
    _1: 'a ->
    _2: 'b ->
    _3: 'c ->
    _4: 'd ->
    _5: 'e ->
    _6: 'f ->
    _7: 'g ->
    _8: 'h ->
    _9: 'i ->
    _10: 'j ->
    _11: 'k ->
    _12: 'l ->
    _13: 'm ->
    _14: 'n ->
    tuple14 'a 'b 'c 'd 'e 'f 'g 'h 'i 'j 'k 'l 'm 'n

(* Marking terms for normalization *)
abstract
let normalize_term (#a: Type) (x: a) : a = x
abstract
let normalize (a: Type0) : Type0 = a

abstract noeq
type norm_step =
  | Simpl
  | Weak
  | HNF
  | Primops
  | Delta
  | Zeta
  | Iota
  | NBE // use NBE instead of the normalizer
  | Reify
  | UnfoldOnly : list string -> norm_step // each string is a fully qualified name like `A.M.f`
  | UnfoldFully : list string -> norm_step // idem
  | UnfoldAttr : list string -> norm_step

// Helpers, so we don't expose the actual inductive
abstract
let simplify: norm_step = Simpl
abstract
let weak: norm_step = Weak
abstract
let hnf: norm_step = HNF
abstract
let primops: norm_step = Primops
abstract
let delta: norm_step = Delta
abstract
let zeta: norm_step = Zeta
abstract
let iota: norm_step = Iota
abstract
let nbe: norm_step = NBE
abstract
let reify_: norm_step = Reify
abstract
let delta_only (s: list string) : norm_step = UnfoldOnly s
abstract
let delta_fully (s: list string) : norm_step = UnfoldFully s
abstract
let delta_attr (s: list string) : norm_step = UnfoldAttr s

// Normalization marker
abstract
let norm (s: list norm_step) (#a: Type) (x: a) : a = x
abstract
val assert_norm: p: Type -> Pure unit (requires (normalize p)) (ensures (fun _ -> p))
let assert_norm p = ()

let normalize_term_spec (#a: Type) (x: a) : Lemma (normalize_term #a x == x) = ()
let normalize_spec (a: Type0) : Lemma (normalize a == a) = ()
let norm_spec (s: list norm_step) (#a: Type) (x: a) : Lemma (norm s #a x == x) = ()

(*
 * Pure and ghost inner let bindings are now always inlined during the wp computation, if:
 * the return type is not unit and the head symbol is not marked irreducible.
 * To circumvent this behavior, singleton can be used.
 * See the example usage in ulib/FStar.Algebra.Monoid.fst.
 *)
irreducible
let singleton (#a: Type) (x: a) : (y: a{y == x}) = x

(*
 * `with_type t e` is just an identity function, but it receives special treatment
 *  in the SMT encoding, where in addition to being an identity function, we have
 *  an SMT axiom:
 *  `forall t e.{:pattern (with_type t e)} has_type (with_type t e) t`
 *)
let with_type (#t: Type) (e: t) = e

