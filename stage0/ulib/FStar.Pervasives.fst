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

/// Implementation of FStar.Pervasives.fsti
let remove_unused_type_parameters _ = ()

let smt_pat #_ _ = ()

let smt_pat_or _ = ()

let spinoff p = p

#push-options "--no_tactics"
let spinoff_eq _ = ()
let spinoff_equiv _ = ()
#pop-options

let assert_spinoff _ = ()

let ambient #_ _ = True

let intro_ambient #_ _ = ()

let normalize_term #_ x = x

let normalize a = a

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
let delta_fully s = UnfoldFully s

irreducible
let delta_attr s = UnfoldAttr s

irreducible
let delta_qualifier s = UnfoldAttr s

irreducible
let delta_namespace s = UnfoldNamespace s

irreducible
let unmeta = Unmeta

irreducible
let unascribe = Unascribe

let norm _ #_ x = x

let assert_norm _ = ()

let normalize_term_spec #_ _ = ()

let normalize_spec _ = ()

let norm_spec _ #_ _ = ()

let inversion _ = True

let allow_inversion _ = ()

let invertOption _ = ()

let rec false_elim #_ _ = false_elim ()

let inline_let = ()

let rename_let _ = ()

let plugin _ = ()

let tcnorm = ()

let must_erase_for_extraction = ()

let dm4f_bind_range = ()

let expect_failure _ = ()

let expect_lax_failure _ = ()

let tcdecltime = ()

let unifier_hint_injective = ()

let strict_on_arguments _ = ()

let resolve_implicits = ()

let override_resolve_implicits_handler #a x l = ()

let handle_smt_goals = ()

let erasable = ()

let commute_nested_matches = ()

let noextract_to _ = ()

let normalize_for_extraction _ = ()

let ite_soundness_by _ = ()

let default_effect _ = ()
let top_level_effect _ = ()
let effect_param = ()
let bind_has_range_args = ()
let primitive_extraction = ()

let extract_as_impure_effect = ()

let strictly_positive = ()

let unused = ()

let no_auto_projectors = ()

let no_auto_projectors_decls = ()

let no_subtyping = ()

let admit_termination = ()

let singleton #_ x = x

let coercion = ()

let desugar_of_variant_record _ = ()

let defer_to #a (_:a) = ()
