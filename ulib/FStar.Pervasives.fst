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
[@@"no_prelude"]
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

let norm _ #_ x = x

let assert_norm _ = ()

let normalize_term_spec #_ _ = ()

let normalize_spec _ = ()

let norm_spec _ #_ _ = ()

let inversion _ = True

let allow_inversion _ = ()

let invertOption _ = ()

let rec false_elim #_ _ = false_elim ()

let singleton #_ x = x

let normalize_for_extraction _ = ()
let normalize_for_extraction_type = ()
