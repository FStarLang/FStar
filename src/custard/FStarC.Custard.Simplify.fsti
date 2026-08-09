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

(** Drop unused pure let-bindings, turn unused impure ones into sequencing,
    and contract [let x = e in x] to [e]. *)
(** [run imports prog].  [imports] are the types this program uses but did not
    compile, each as the layout analysis left it (see [ti_pre]) together with
    the verdict its home unit reached about it.

    They are not part of [prog] and are never emitted; they are here because
    two of the passes below decide something about a type by looking at *other*
    types' declarations, and would otherwise silently reach a different answer
    from the unit that actually compiled it:

      - [inline_fields] asks whether the type of a marked field is a
        one-constructor variant, and expands the constructor if so;
      - [depat] and [records] ask how many constructors a type has.

    [unused_params] needs no such help: it only rewrites applications of
    declarations it has, so an imported type's parameters are pessimized for
    free, which is what section 12.4 asks for. *)
val run : list (dtype & dtype & bool) -> program -> ML program
