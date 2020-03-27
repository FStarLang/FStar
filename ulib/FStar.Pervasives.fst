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

open Prims

let pattern = unit

let smt_pat #_ _ = ()

let smt_pat_or _ = ()

let spinoff p = p

let assert_spinoff _ = ()

let ambient #_ _ = True

let intro_ambient #_ _ = ()

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

let assume_strictly_positive = ()

let unifier_hint_injective = ()

let strict_on_arguments _ = ()

let resolve_implicits = ()

let erasable = ()

let normalize_term #_ x = x
let normalize a = a

noeq type norm_step' =
  | Simpl
  | Weak
  | HNF
  | Primops
  | Delta
  | Zeta
  | Iota
  | NBE // use NBE instead of the normalizer
  | Reify
  | UnfoldOnly  : list string -> norm_step' // each string is a fully qualified name like `A.M.f`
  | UnfoldFully : list string -> norm_step' // idem
  | UnfoldAttr  : list string -> norm_step'

let norm_step = norm_step'

let simplify = Simpl
let weak = Weak
let hnf = HNF
let primops = Primops
let delta = Delta
let zeta = Zeta
let iota = Iota
let nbe = NBE
let reify_ = Reify
let delta_only s = UnfoldOnly s
let delta_fully s = UnfoldFully s
let delta_attr s = UnfoldAttr s

let norm _ #_ x = x

let assert_norm _ = ()

let normalize_term_spec #_ _ = ()
let normalize_spec _ = ()
let norm_spec _ #_ _ = ()

let singleton #_ x = x
