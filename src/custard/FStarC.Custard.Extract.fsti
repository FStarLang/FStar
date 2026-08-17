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

(** The typing environment as it stands, i.e. including whatever modules the
    requests so far have caused to be loaded. *)
val tcenv : state -> ML TcEnv.env

(** Load the module a lid belongs to, if the run has not already.  A
    generated declaration (section 13) has to do this by hand: it inspects
    types the demand-driven loop has not asked about, and an abbreviation
    whose module is not loaded does not unfold -- it merely looks abstract. *)
val ensure_lid_available : state -> Ident.lident -> ML unit

(** The IR name a lid is emitted under, before any specialization suffix.  It
    is the [FStar.Stubs.*] rewrite (section 8.2) that makes this worth
    exporting: a generated declaration must spell names the same way. *)
val name_of_lid : Ident.lident -> ML name

(** Request the extraction of a specialization, returning the IR name it will
    be emitted under.  Idempotent. *)
val request : state -> spec_key -> ML name

(** Translate an F* type, resp. term, exactly as the extraction loop would.
    A generated declaration (section 13) is written as F* syntax and handed to
    these, so that requesting, specialization, erasure and reification are the
    ones the rest of the program gets and not a second implementation. *)
val ty_of_typ : state -> FStarC.Syntax.Syntax.typ -> ML cty
val expr_of_term : state -> FStarC.Syntax.Syntax.term -> ML expr

(** Give {!FStarC.Custard.Mono} a way to report the request chain of section
    3.6.  It runs below the extractor and has no [state] to read; without this
    a budget exhausted in a type-level normalization names no definition. *)
val install_chain_reporter : state -> ML unit

(** Drain the worklist and return the program in dependency order (definitions
    before their uses), which is the order the backends want.

    The callback is invoked once per module the run loads, after everything
    that module's definitions refer to has been extracted.  It is how
    generated declarations get made without [Extract] having to depend on the
    module that generates them (section 13). *)
val run : state -> list Ident.lident -> option Ident.lident ->
          (FStarC.Syntax.Syntax.modul -> ML unit) -> ML program

(** [request] for a definition with no [Mono] binders, which is every
    definition a *generated* declaration refers to (section 13). *)
val request_lid : state -> Ident.lident -> ML name

(** Add a declaration the extraction loop did not produce: a plugin
    registration, or the [DExternal] for an OCaml-only symbol one refers to
    (section 13).  The key is the declaration's identity for the purposes of
    emitting it once; a second [emit] under a key already used is ignored. *)
val emit : state -> string -> decl -> ML unit

(** Whether [emit] has already been given this key. *)
val emitted : state -> string -> ML bool

(** The declarations this run took from a linked unit rather than compiling
    (section 12.4).  They are deliberately *not* part of the program: they must
    not be renamed, simplified or emitted.  The later passes consult them --
    the layout analysis for their verdicts, the backends for the namespace to
    qualify their names with. *)
val imports : state -> ML (list (decl & option type_info))

(** Every file the linked units emitted into; see {!Unit.link_homes}. *)
val link_homes : state -> ML (list string)

(** The specialization key each emitted declaration was created for, by the
    declaration's name.  This is what a `.cui` exports as the identity of an
    entry: a downstream unit recognizes an already-compiled definition by the
    key its own request computes, and that key is a property of the F* term,
    not of any name Custard invented for it (section 12.3). *)
val exported_keys : state -> ML (list (string & string))

(** See {!FStarC.Custard.Loader.loaded_digests}. *)
val loaded_digests : state -> ML (list (string & string))
