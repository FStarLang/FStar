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

(** Effect-guarded simplification; see sections 6 and 7.3 of
    doc/ref/custard.md.

    Everything here is an instance of the same discipline: a subterm may only
    be dropped when its effect is [E_Pure] or [E_Ghost], and an impure one is
    kept in place (as a statement) instead. *)
module FStarC.Custard.Simplify

open FStarC
open FStarC.Effect
open FStarC.Custard.Syntax

(** Section 6, pass 1: let-normalization.  Establishes the invariant every
    later rewrite is written against -- *every operand is pure*, so an impure
    computation appears only as the right-hand side of an [ELet], the left of
    an [ESeq], or in tail position.  Runs before the layout analysis, since
    that pass drops arguments and so has to move effects. *)
val anf : program -> ML program

(** Every name a declaration mentions, in its signature and in its body, as
    [string_of_name] keys.  This is what dead-code elimination walks, and what
    section 12.9's splitter walks to decide which file a declaration can go
    in.  A constructor appears under its own name, not its type's;
    {!ctor_owners} maps one to the other. *)
val decl_deps : decl -> ML (list string)

(** Each constructor's type, as [string_of_name] keys.  A reference to a
    constructor is a reference to its declaration. *)
val ctor_owners : program -> ML (FStarC.SMap.t string)

(** Drop unused pure let-bindings, turn unused impure ones into sequencing,
    and contract [let x = e in x] to [e]. *)
(** [run imports vd prog].

    [vd] is the representation verdict the layout analysis reached for every
    type this program uses -- which of them are records, and how each
    constructor stores its inlined fields (section 5.5).  The two passes that
    apply it are the first ones to run, and they *only* apply it: a type's
    representation is a function of the type and nothing else, so nothing here
    is allowed to decide one.  Everything below them therefore sees the
    representation the backend will print.

    [imports] are the declarations this program links against rather than
    compiles.  A type's representation is settled and arrives in [vd]; they
    are here because the passes that ask how many constructors a type has,
    what its fields are called, or what an imported function's declared
    argument types are, still have to be able to see them. *)
val run : list decl -> verdicts -> program -> ML program
