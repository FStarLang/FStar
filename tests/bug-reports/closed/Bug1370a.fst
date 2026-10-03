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
module Bug1370a

open FStar.Pervasives
open FStar.Exn

// The point of this test used to be that the parameters of an effect
// abbreviation are ordered as written: Raises : a:Type0 -> ex:exn -> Effect.
// An abbreviation is now just another name for an effect, so there are no
// parameters to order and nowhere to put a specification: the declaration
// below is rejected, and that refusal is what this test now pins down.
// (Which exception is raised is not tracked by the effect system either.)
[@@expect_failure [316]]
effect Raises (a:Type) (ex:exn) =
    Exn a (requires True) (ensures fun _ -> ex == ex)

effect Raises (a:Type) = Exn a

exception Bad

// Note: an effect abbreviation may only be applied to its result type; the
// remaining arguments of a computation type are the requires/ensures clauses.
val u : nat -> Exn nat
let u i = if i > 10
    then i
    else raise Bad                  // expected to work
