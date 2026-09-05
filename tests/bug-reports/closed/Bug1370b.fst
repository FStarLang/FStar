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
module Bug1370b

(* An effect abbreviation is another name for an effect: it takes no
   parameters and its right-hand side carries no specification.  The
   eta-expanded spelling [effect M (a:Type) = N a] is still accepted, since
   that is all an abbreviation could ever have expressed; everything else is
   rejected here rather than silently mis-elaborated. *)

effect Good1 = Tot
effect Good2 (a:Type) = PURE a

(* The right-hand side is not an eta-expansion of an effect name. *)
[@@(expect_failure [316])]
effect Ouch1 (a:Type) = Tot False

(* One argument, two parameters. *)
[@@(expect_failure [316])]
effect Ouch2 (x:int) (a:Type) = Tot a

(* Same: [x] is never applied, so it was always dead. *)
[@@(expect_failure [316])]
effect Ouch3 (a:Type) (x:int) = Tot a

(* A specification on an abbreviation has nowhere to go.  An [ensures] would
   have to refine the result type at every use site; it used to be dropped on
   the floor when the abbreviation was rooted at [Tot], which is the bug this
   refusal closes. *)
[@@(expect_failure [316])]
effect Ouch4 (a:Type) (x:int) = PURE a (ensures fun _ -> x > 0)

[@@(expect_failure [316])]
effect Ouch5 (a:Type) = Tot a (ensures fun _ -> False)

(* A [requires] would have to become an implicit binder on the *arrow* the
   computation type is the codomain of, and an abbreviation has no arrow. *)
[@@(expect_failure [316])]
effect Ouch6 (a:Type) (x:int) = PURE a (requires x > 0)
