(*
   Copyright 2008-2025 Microsoft Research

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

(** Custom extraction rules (section 8 of doc/ref/custard.md).

    Some F* definitions must not be compiled from their F* bodies.  A machine
    integer is specified as a record wrapping a refined mathematical integer,
    and [FStar.UInt32.add_mod] as modular arithmetic on that integer; compiling
    that literally gives correct but useless code (and, since Custard is
    whole-program, it drags the whole of [FStar.UInt] into every program).
    What we want instead is a machine type and a machine instruction.

    This module is the table that says so.  It is consulted in step 1 of the
    extraction loop (section 3.3), *before* the definition is looked up, so a
    definition with a rule is never requested and never appears in the output.

    Phase 1, which is what this is, hardcodes the rules.  Phase 2 will let
    plugins register their own through {!register_rule}, so that Pulse can ship
    its rules instead of patching the compiler. *)
module FStarC.Custard.Builtins

open FStarC
open FStarC.Effect
open FStarC.Const
open FStarC.Custard.Syntax

module Ident = FStarC.Ident

(** A symbol realized outside F*: an [assume val] with a hand-written
    implementation in an [.ml] or [.c] file. *)
type extern = {
  x_name:   option string;  (** target name, when it differs from the mangled one *)
  x_header: option string;  (** C header to include, for the C backends *)
}

type rule =
  | Rule_prim of int & (list cty -> list expr -> ML expr)
  (** [Rule_prim (n, f)] builds a term from the type arguments and [n]
      translated value arguments.  A use supplying fewer than [n] arguments is
      eta-expanded rather than rejected, so that a primitive can still be
      passed around as a function. *)

  | Rule_type of (list cty -> ML cty)
  (** Build a type from the type arguments. *)

  | Rule_extern of extern
  (** Emit a [DExternal] rather than compiling the F* definition. *)

  | Rule_opaque
  (** Compile the definition normally, but treat the resulting type as having a
      representation fixed elsewhere: no erasure and no newtype collapse. *)

  | Rule_realized
  (** The definition's module is realized by hand-written OCaml.  For a type
      this means {!FStarC.Custard.Syntax.Realized}: keep the declaration for
      its shape, do not emit it, and refer to the realization's own names.
      For anything else it means nothing -- a realized module's values are
      either compiled from their F* definitions like any others or, when the
      module only declares them, emitted as externals. *)

val register_rule : Ident.lident -> rule -> ML unit

(** The machine-integer type a module name denotes, if any: ["FStar.UInt32"]
    is [(Unsigned, Int32)]. *)
val machine_int_of_module : list string -> option (signedness & width)

(** The rule declared by a definition's attributes, if any:
    [@@custard_extern "target"] (plus an optional [@@custard_c_header "h.h"])
    and [@@custard_opaque].  Unlike {!lookup_rule} this needs the definition in
    hand, so the extractor consults it separately. *)
val rule_of_attributes : list FStarC.Syntax.Syntax.term -> ML (option rule)

(** Section 8.3: rewrite the [FStar.Stubs.*] namespace to the [FStarC.*] one
    it is a stub *for*.  [FStar.Stubs.Tactics.V2.Builtins] is ulib's view of
    the compiler's own [FStarC.Tactics.V2.Builtins], and the two must be one
    name, or a metaprogram and the engine that runs it would not link. *)
val no_fstar_stubs : list string -> list string

(** Whether a module is realized by hand in OCaml (section 8.2), and so has a
    [.ml] of its own in [src/ml] or [ulib/ml] that Custard must neither
    compile over nor write a file on top of.  Takes a namespace that has
    already been through {!no_fstar_stubs}. *)
val is_realized_module : list string -> ML bool

(** Whether a realized module is realized for its *types only*, so that its
    values are still compiled.  A realization normally replaces the whole
    module; the exception is a module listed for its types alone because the
    realizations name them, with no hand-written file of its own. *)
val is_type_only_realized_module : list string -> ML bool

(** Raised by a rule lookup that does not apply to the given name, so that the
    next extension in the chain is tried. *)
exception No_custard_rule

(** A rule lookup, as registered by a plugin.  It signals "not mine" by raising
    {!No_custard_rule}. *)
let rule_lookup_t = Ident.lident -> ML rule

(** Try [f] before everything already registered. *)
val register_pre_rule : rule_lookup_t -> ML unit

(** Try [f] only after everything already registered has declined. *)
val register_post_rule : rule_lookup_t -> ML unit


(** [lookup_rule l] is the rule for [l]: the extensions registered by plugins,
    then the table populated by {!register_rule}, then the hardcoded families
    (machine integers, the [Prims] connectives), which are matched by the shape
    of the name rather than enumerated. *)
val lookup_rule : Ident.lident -> ML (option rule)
