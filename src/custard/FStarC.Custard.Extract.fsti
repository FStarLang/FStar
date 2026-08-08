(*
   Copyright 2008-2026 Microsoft Research

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

(** The Custard extraction loop.

    See doc/ref/custard.md section 3.3.  This is the demand-driven worklist:
    starting from the entry points, we look each definition up, normalize it,
    translate it to the Custard IR, and request whatever it refers to.

    A request is a [spec_key]: a definition together with the concrete
    arguments of its [Mono] binders (section 3.1).  Requests are interned, so
    two call sites that agree on the [Mono] arguments share one
    specialization. *)
module FStarC.Custard.Extract

open FStarC
open FStarC.Effect
open FStarC.Custard.Syntax

module Dep   = FStarC.Parser.Dep
module Ident = FStarC.Ident
module TcEnv = FStarC.TypeChecker.Env

(** A specialization request: a definition, plus the value of each of its
    [Mono] binders, given by the binder's index in the definition's type. *)
type spec_key = {
  sk_lid:  Ident.lident;
  sk_args: list (int & FStarC.Syntax.Syntax.term);
  (* The terms actually substituted into the body, which are the same
     arguments in *weak head* normal form.  Kept apart from [sk_args] because
     the two answer different questions: [sk_args] is the specialization's
     identity, so it must be fully reduced, while what goes into the body
     should be reduced no further than it takes to see the value's head. *)
  sk_subst: list (int & FStarC.Syntax.Syntax.term);
  (* Section 3.2c.  A [Mono] argument may mention runtime values -- a
     dictionary built out of one, a closure over one -- and when it does, the
     parts that are runtime are abstracted out of it and passed at runtime
     instead.  [sk_holes] is how many were abstracted; every term in
     [sk_args] and [sk_subst] is then a lambda over exactly that many
     binders, shared between them, and the specialization takes that many
     extra parameters after its [Poly] ones.

     It has to be part of the key.  Abstracting a runtime [int] out of an
     argument produces the same term as an argument that was written as a
     function of an [int]; the two are different specializations with
     different arities, and only the count tells them apart. *)
  sk_holes: int;
}

val state : Type0

val init : Dep.deps -> TcEnv.env -> ML state

(** The normalizer steps applied to every definition before translation.
    Section 3.3 of the design doc explains each one. *)
val custard_norm_steps : list TcEnv.step

(** Request the extraction of a specialization, returning the IR name it will
    be emitted under.  Idempotent. *)
val request : state -> spec_key -> ML name

(** Drain the worklist and return the program in dependency order (definitions
    before their uses), which is the order the backends want. *)
val run : state -> list Ident.lident -> option Ident.lident -> ML program
