module FStarC.NormSteps

(* A mirror of FStar.NormSteps in ulib *)

open Prims
noeq
type norm_step =
  | Simpl // Logical simplification, e.g., [P /\ True ~> P]
  | Weak // Weak reduction: Do not reduce under binders
  | HNF // Head normal form
  | Primops // Reduce primitive operators, e.g., [1 + 1 ~> 2]
  | Delta // Unfold all non-recursive definitions
  | Zeta // Unroll recursive calls
  | ZetaFull // Unroll recursive calls fully
  | Iota // Reduce case analysis (i.e., match)
  | NBE // Use normalization-by-evaluation, instead of interpretation (experimental)
  | Reify // Reify effectful definitions into their representations
  | NormDebug // Turn on debugging for this call
  | UnfoldOnly : list string -> norm_step // Unlike Delta, unfold definitions for only the given
  | UnfoldOnce : list string -> norm_step
  // names, each string is a fully qualified name
  // like `A.M.f`
  // idem
  | UnfoldFully : list string -> norm_step
  | UnfoldAttr : list string -> norm_step // Unfold definitions marked with the given attributes
  | UnfoldQual : list string -> norm_step
  | UnfoldNamespace : list string -> norm_step
  | Unmeta : norm_step
  | Unascribe // Remove type ascriptions [t <: ty ~> t]

irreducible
let simplify = Simpl

irreducible
let weak = Weak

irreducible
let hnf = HNF

irreducible
let primops = Primops

irreducible
let delta = Delta

irreducible
let norm_debug = NormDebug

irreducible
let zeta = Zeta

irreducible
let zeta_full = ZetaFull

irreducible
let iota = Iota

irreducible
let nbe = NBE

irreducible
let reify_ = Reify

irreducible
let delta_only s = UnfoldOnly s

irreducible
let delta_once s = UnfoldOnce s

irreducible
let delta_fully s = UnfoldFully s

irreducible
let delta_attr s = UnfoldAttr s

irreducible
let delta_qualifier s = UnfoldQual s

irreducible
let delta_namespace s = UnfoldNamespace s

irreducible
let unmeta = Unmeta

irreducible
let unascribe = Unascribe
