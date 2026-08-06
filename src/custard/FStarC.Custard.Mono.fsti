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

(** Classification of a definition's binders into monomorphized and
    polymorphic ones -- section 3.1 of doc/ref/custard.md. *)
module FStarC.Custard.Mono

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax

module Ident = FStarC.Ident
module TcEnv = FStarC.TypeChecker.Env

type bclass =
  (* Substituted away at specialization time; one copy of the definition is
     emitted per distinct argument. *)
  | Mono
  (* Kept as a parameter of the specialized definition. *)
  | Poly
  (* Non-informative (section 5.1): the binder is deleted from the specialized
     definition's signature, and the corresponding argument is deleted from
     every call site.  This is rule 1 of section 3.1. *)
  | Dropped

val bclass_to_string : bclass -> string

instance val showable_bclass : Class.Show.showable bclass

(** True when a binder carries no runtime value, either because it is a type
    (types are compiled uniformly, section 5.0, so a type argument cannot
    change any layout) or because its sort is non-informative (section 5.1).

    Custard decides deletion with this predicate alone, and never by looking at
    whether a binder is implicit or explicit.  The implicit/explicit
    distinction is a source-level convenience with no bearing on what has to
    exist at runtime, and Custard has no interoperability obligation that would
    make the source arity worth preserving. *)
val is_type_binder (b:binder) : ML bool

val is_erased_binder (env:TcEnv.env) (b:binder) : ML bool

(** [erased_binders env t] applies [is_erased_binder] to each binder of [t]'s
    outermost arrow, in order.  Used wherever a spine has to be filtered but no
    full [classify] is available: constructor applications, applications of a
    variable, and type applications. *)
val erased_binders (env:TcEnv.env) (t:typ) : ML (list bool)

(** [type_binders env t] marks the binders of [t] that are types.  This is the
    dual filter, used at the *type* level: the arguments of a type constructor
    that survive into a [cty] are exactly its type parameters. *)
val type_binders (env:TcEnv.env) (t:typ) : ML (list bool)

(** [classify env attrs t] classifies the binders of a definition of type [t]
    carrying the top-level attributes [attrs].  The returned list has one
    entry per binder of [t]'s outermost arrow, in order. *)
val classify (env:TcEnv.env) (attrs:list attribute) (t:typ) : ML (list bclass)

(** True if any binder is [Mono], i.e. uses of this definition have to be
    specialized. *)
val has_mono (cs:list bclass) : ML bool

(** True if any binder is [Dropped], i.e. uses of this definition have to have
    arguments deleted. *)
val has_dropped (cs:list bclass) : ML bool
