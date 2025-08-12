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
module FStar.Tactics.Typeclasses

open FStar.Tactics.Effect
open FStar.Stubs.Reflection.Types (* for `decls` *)

(* The attribute that marks instances. This is the main attribute
needed as it is used to find instances for typeclass resolution. *)
val tcinstance : unit

(* These attribute that mark classes and methods, which can be useful
to control their normalization or to generate code. *)
val tcclass  : unit
val tcmethod : unit

(* Functional dependencies of a class. It takes an int list
representing the arguments of the class (starting from 0, both explicit
and implicit alike) that are dependent on the rest. When trying to apply
an instance, if the fundeps are unresolved (i.e. contain uvars) but the
other arguments do not, we will apply the instance and instantiate the
fundeps. *)
val fundeps : list int -> unit

(* Use this attribute in an instance to prevent it from instantiating
the goal, **even if** there are functional dependencies for the class
that seem to match. *)
val noinst : unit

(* The attribute that marks class fields
   to signal that no method should be generated for them *)
val no_method : unit

(* The typeclass resolution metaprogram. This is a plugin, clients can
run this tactics without having to know its definition in the .fst *)
val tcresolve : unit -> Tac unit

(* Like `tcresolve`, but will print debugging information when called. *)
val tcresolve_debug : unit -> Tac unit

(* The metaprogram to generate class methods. Also a plugin. This
is inserted automatically by the desugaring phase for any `class`
declaration. *)
val mk_class (nm:string) : Tac decls

(* Helper to solve an explicit argument by typeclass resolution *)
[@@tcnorm]
unfold let solve (#a:Type) (#[tcresolve ()] ev : a) : Tot a = ev

(* Like `solve`, but prints debugging information. *)
[@@tcnorm]
unfold let solve_debug (#a:Type) (#[tcresolve_debug ()] ev : a) : Tot a = ev
