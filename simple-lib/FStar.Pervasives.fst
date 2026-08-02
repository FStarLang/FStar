(*
   A minimal FStar.Pervasives for the simplified effect system.

   Only the pieces the type checker itself refers to are provided here:
   the divergent effect, SMT patterns, normalization markers and a few
   common datatypes.
*)
[@@"no_prelude"]
module FStar.Pervasives

open Prims
open FStar.Pervasives.Native

(**** The divergent effect *)

assume effect DIV

assume sub_effect PURE ~> DIV
assume sub_effect GHOST ~> DIV

effect Div (a: Type) = DIV a
effect Dv  (a: Type) = DIV a

(** [Lemma] is a [Pure unit] computation; the type checker inserts the
    result type [unit] and normalizes the arguments. *)
effect Lemma (a: Type) = PURE a

(**** SMT patterns *)

assume new type pattern : Type0

assume val smt_pat (#a: Type) (x: a) : Tot pattern

assume val smt_pat_or (x: list (list pattern)) : Tot pattern

(**** Normalization *)

noeq
type norm_step =
  | Simpl
  | Weak
  | HNF
  | Primops
  | Delta
  | Zeta
  | ZetaFull
  | Iota
  | Reify
  | NBE
  | UnfoldOnly : list string -> norm_step
  | UnfoldOnce : list string -> norm_step
  | UnfoldFully : list string -> norm_step
  | UnfoldAttr : list string -> norm_step
  | UnfoldQual : list string -> norm_step
  | UnfoldNamespace : list string -> norm_step
  | Unmeta
  | Unascribe

let simplify = Simpl
let weak = Weak
let hnf = HNF
let primops = Primops
let delta = Delta
let zeta = Zeta
let zeta_full = ZetaFull
let iota = Iota
let nbe = NBE
let unmeta = Unmeta
let unascribe = Unascribe
let delta_only (s: list string) = UnfoldOnly s
let delta_once (s: list string) = UnfoldOnce s
let delta_fully (s: list string) = UnfoldFully s
let delta_attr (s: list string) = UnfoldAttr s
let delta_qualifier (s: list string) = UnfoldQual s
let delta_namespace (s: list string) = UnfoldNamespace s

assume val norm (steps: list norm_step) (#a: Type) (x: a) : Tot a

assume val normalize_term (#a: Type) (x: a) : Tot a

assume val normalize (a: prop) : prop

assume val assert_norm (p: prop) : Pure unit (requires (normalize p)) (ensures (fun _ -> p))

(**** Common datatypes *)

type either (a b: Type) =
  | Inl : v: a -> either a b
  | Inr : v: b -> either a b

let dfst (#a: Type) (#b: a -> GTot Type) (t: dtuple2 a b) : Tot a = Mkdtuple2?._1 t

let dsnd (#a: Type) (#b: a -> GTot Type) (t: dtuple2 a b) : Tot (b (Mkdtuple2?._1 t)) =
  Mkdtuple2?._2 t

let id (#a: Type) (x: a) : Tot a = x

(**** Attributes understood by the type checker *)

assume val remove_unused_type_parameters : list int -> unit
assume val spinoff (p: prop) : prop
assume val trivial_pure_post (a: Type) : Tot (a -> prop)
