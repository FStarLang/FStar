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
module FStarC.Custard.PrintC

open FStarC.Effect
open FStarC.Custard.Syntax

(** What separate compilation adds (section 42).  Empty in whole-program mode,
    which is [no_unit]. *)
type unit_info = {
  (** The `--custard_unit` name, when there is one.  It is what namespaces the
      global initializer (section 42.3); its absence is what keeps every
      whole-program output byte-identical to what it was. *)
  cu_name:    option string;
  (** The header file of each linked unit, in link order, to `#include`
      (section 42.2). *)
  cu_headers: list string;
  (** The global initializer of each linked unit, in link order.  The unit
      holding the entry point calls these before its own (section 42.3). *)
  cu_inits:   list string;
}

val no_unit : unit_info

(** The name of this program's global initializer, or [None] when it has no
    globals and there is nothing for a downstream [main] to call.  It is what
    a `.cui` records (section 42.3), and it shares its predicate with the
    printer so that what the interface promises and what the source defines
    cannot drift apart. *)
val init_globals_name : unit_info -> program -> ML (option string)

(** Whether a declaration is part of this translation unit's interface: it has
    external linkage and appears in the header.  Everything else is [static]
    (section 24), which is also why a C unit's `.cui` offers only these
    (section 42.1). *)
val is_public : dlet -> ML bool

(** The whole program as one self-contained C11 translation unit (section 6,
    M8): a header and a source, in that order.  The first argument is the stem
    of the output file, which the source includes and the include guard is
    derived from.

    The program includes the declarations linked units already compiled
    (section 12.4 rule 2).  They are needed for the tables this builds -- a
    later decision about an imported type or call has to be the one its home
    unit made -- and are skipped at every emission site, since the header they
    came from is included instead (section 42.2).

    Only the [Root] declarations appear in the header; everything else is
    [static] (section 24). *)
val print_program : string -> unit_info -> program -> ML (string & string)
