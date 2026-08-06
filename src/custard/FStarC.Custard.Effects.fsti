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

(** Effect classification; see section 7 of doc/ref/custard.md.

    Custard's only effect-directed question is whether a term may be dropped,
    duplicated or reordered, so the lattice has three points and [E_Impure] is
    not subdivided.  Two source mechanisms feed into it: F*'s effect names,
    via [TcUtil.effect_extraction_mode], and the [extract_as_impure_effect]
    attribute, which Pulse uses to encode its effects as *type constructors*
    rather than as F* effects. *)
module FStarC.Custard.Effects

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.Custard.Syntax

module Ident = FStarC.Ident
module TcEnv = FStarC.TypeChecker.Env

(** Section 7.1: map an effect name into the lattice.  Raises
    [Error_CustardUnextractableEffect] for an effect whose extraction mode is
    [Extract_none]. *)
val of_lid : TcEnv.env -> Ident.lident -> ML eff

(** True when the head of [t] is a type constructor carrying
    [@@extract_as_impure_effect]. *)
val head_is_impure_marker : TcEnv.env -> typ -> ML bool

(** For [stt b p q], returns [Some b]: the representation of a marked type is
    its first argument, and the remaining (index) arguments are erased.  Returns
    [None] when the head does not carry the attribute. *)
val impure_effect_result : TcEnv.env -> typ -> ML (option typ)

(** The result type of a computation, seen through the marker: for a marked
    codomain this is the payload rather than the marked application. *)
val result_typ : TcEnv.env -> comp -> ML typ

(** The effect of a computation type, including the [extract_as_impure_effect]
    promotion of section 7.2: [a -> stt b p q] is impure even though its F*
    effect name is [Tot]. *)
val of_comp : TcEnv.env -> comp -> ML eff
