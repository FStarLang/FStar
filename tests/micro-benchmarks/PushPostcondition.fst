(*
   Copyright 2008-2025 Microsoft Research

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
module PushPostcondition

(* When a definition is checked against a computation type with a non-trivial
   postcondition, the postcondition is recorded in the environment and is
   turned into a refinement on the expected type at the point where the
   result of the body is finally checked. This localizes the proof obligation
   at the tail of each branch instead of raising it for the body as a whole.

   The tests below pin down that the obligation lands in tail position, and
   that recording the postcondition does not perturb type inference. *)

assume val p : int -> prop
assume val lem (x:int) : Lemma (p x)

(* The obligation must be raised separately in each branch of the match, with
   that branch's equations in scope. Stating it for the body as a whole would
   require an extra case analysis. *)
let per_branch (b:bool) : Pure int (requires True) (ensures fun r -> p r) =
  if b then (lem 1; 1) else (lem 2; 2)

(* The expected postcondition must not be visible to unification. Here the
   inner let is unannotated and its right-hand side is a match, so its type is
   initially a unification variable. Solving that variable with the refinement
   would move the obligation into the branches of the inner match, i.e. before
   [lem] establishes it. *)
let no_inference_leak (b:bool) : Pure int (requires True) (ensures fun r -> p r) =
  let y = if b then 1 else 2 in
  lem y;
  y

(* Same, through an ascription rather than a lambda: the desugarer turns an
   annotated definition into a lambda whose body is ascribed, so the
   ascription is what carries the postcondition down to the body. *)
let no_inference_leak_ascribed (b:bool) : int =
  ((let y = if b then 1 else 2 in
    lem y;
    y) <: Pure int (requires True) (ensures fun r -> p r))

(* A lambda passed as an argument gets the postcondition from its expected
   arrow type, with no ascription involved. *)
assume val apply_it (f: (x:int -> Pure int (requires True) (ensures fun r -> p r))) : unit

let lambda_argument () : unit =
  apply_it (fun x -> lem x; x)

(* Refining the expected type must not disturb an inferred implicit argument
   or a subsequent application. *)
let inferred_implicit (#a:Type) (x:a) : Pure a (requires True) (ensures fun r -> r == x) =
  let y = x in
  y

(* A [$]-binder forces an equality check against the expected type rather than
   a subtyping check, so no refinement may be introduced there. *)
assume val eq_binder ($x:unit) : unit

let use_eq_ok () : Pure unit (requires True) (ensures fun _ -> True) =
  eq_binder ()
