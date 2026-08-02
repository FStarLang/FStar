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

// The point of this test is that the parameters of an effect abbreviation
// must be ordered as written: Raises : a:Type0 -> ex:exn -> Effect.
// (Which exception is raised is no longer tracked by the effect system, so
// the negative part of the original test is gone.)
effect Raises (a:Type) (ex:exn) =
    Exn a (requires True) (ensures fun _ -> ex == ex)

exception Bad

// Note: an effect abbreviation may only be applied to its result type; the
// remaining arguments of a computation type are the requires/ensures clauses.
val u : nat -> Exn nat
let u i = if i > 10
    then i
    else raise Bad                  // expected to work
