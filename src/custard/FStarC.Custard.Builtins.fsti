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

(* Whether a namespace -- given as it was written, before {!no_fstar_stubs} --
   is one of ulib's [FStar.Stubs.*] restatements of the compiler's own API.
   Those are never compiled: the compiler already defines what they declare. *)
val is_stub_module : list string -> bool

(* Stubs whose compiler counterpart is in a different *module*, not merely a
   different namespace: [no_fstar_stubs] cannot express these.  Keyed and
   valued by the fully qualified lid, as a string. *)
val stub_aliases : list (string & string)

(** Types that have no F* definition *and* none that Custard should emit,
    because a header outside F* already declares them: [FStar.Bytes.bytes] is
    a struct krmllib defines.  This is additive rather than a {!rule}: the
    module may also be realized in OCaml (section 8.2), which is a separate
    and unrelated fact about the same declaration.  A program declares its own
    with [@@custard_extern] (section 8.1, kind 4). *)
val extern_type_of_lid : Ident.lident -> ML (option extern)

(** Whether karamel supplies this module itself on the backend being emitted
    for, so that Custard must emit neither its types nor its definitions and
    must leave every use of them under the F* name (section 20).  Only ever
    true under [--custard_backend KrmlRust], where [Pulse.Lib.Slice] becomes
    Rust's own borrowed slice rather than the owning struct its F* definition
    describes. *)
val is_krml_model : list string -> ML bool

(** As {!is_krml_model}, for a declaration rather than a module: karamel also
    models [FStar.Pervasives.Native.tupleN] on the Rust path, because its
    [split_at] hook destructures a real tuple and crashes on a struct. *)
val is_krml_model_name : list string -> string -> ML bool

(** The names karamel spells the way F* spelled them before operator mangling
    was made uniform, rewritten on the way out so that a karamel built against
    an older F* keeps working.  The twin of
    [FStarC.Extraction.Krml.krml_compat_name], and temporary for the same
    reason: karamel is a separate repository and cannot be updated in the same
    commit.  Must be applied wherever a top-level name reaches the karamel AST,
    references and declarations alike, or a use is renamed away from its own
    definition. *)
val krml_compat_name : list string -> string -> list string & string

(** Whether karamel actually has a translation for this operation of a
    modelled module (section 20).  A model is a promise Custard makes on
    karamel's behalf -- "emit the F* name and karamel will rewrite it" -- and
    an operation karamel does not recognize is a promise it cannot keep: the
    name survives the Rust pass as a call to a function whose body was never
    emitted, and what should have been a diagnostic becomes a link error or,
    worse, an operation on the wrong representation.  Only the built-in models
    are checked; a module named by [--custard_krml_model] is the caller's
    assertion and is taken at its word. *)
val is_known_krml_model_op : list string -> string -> ML bool

(** Whether a module is realized by hand in OCaml (section 8.2), and so has a
    [.ml] of its own in [src/ml] or [ulib/ml] that Custard must neither
    compile over nor write a file on top of, or is one karamel models itself
    ({!is_krml_model}).  Takes a namespace that has already been through
    {!no_fstar_stubs}. *)
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


(* -------------------------------------------------------------------- *)
(* Section 36.  What a rule can add to the program                      *)
(* -------------------------------------------------------------------- *)

(** Section 36.2.  Keep [l] and everything it needs, as [--custard_entry]
    does.

    A rule runs in step 1 of the extraction loop and reachability is computed
    from the roots afterwards, so a rule that synthesizes a call to a runtime
    entry point the *source* never mentions is asking for a name that dead
    code elimination has every reason to delete.  That is a real pattern and
    not a mistake -- a launcher rule's whole job is to emit a call to
    something no F* code calls -- so a rule pins the symbols it will name.

    Call it from the plugin's initializer, next to {!register_rule}: the roots
    are collected once, before the loop starts. *)
val register_root : Ident.lident -> ML unit

(** The roots registered by plugins, in registration order. *)
val registered_roots : unit -> ML (list Ident.lident)

(** Section 36.3.  [lift_named id fs e] makes [e] -- which must be a *closed*
    lambda -- a top-level function called [id] carrying the flags [fs], and
    returns a reference to it.

    This is the operation a plugin generating device code needs and cannot
    write itself.  Section 19.12's [lift_lambdas] already lifts a lambda a
    rule leaves in place, but it chooses the name and it attaches no flags,
    and for a CUDA kernel both are the point: the name appears in profiler
    output and in disassembly, and [Prologue "__global__"] is the difference
    between a kernel and an ordinary host function.

    [id] is used verbatim, with no namespace and no mangling, because a
    generated symbol that a human is going to read in [nsys] should be the
    name the generator chose.  That also makes collision possible, so it is
    checked: two lifts under one name are an error rather than a silent
    overwrite.

    The lambda must have at least one binder.  A zero-binder lambda is its
    own body, so lifting one would produce a top-level variable rather than a
    function, and the flags -- whose whole point is that they decorate a
    *function* -- would go somewhere they mean nothing.  That is refused.

    The lambda must be closed.  A rule that wants to lift a body capturing
    locals closes it first, by adding the captures as leading parameters and
    passing them at the call -- there is nothing Custard can do about a
    capture that it could not do wrongly. *)
val lift_named : string -> list flag -> expr -> ML expr

(** The declarations {!lift_named} has created, oldest first.  Drained by the
    extraction loop when it collects the program. *)
val take_lifted : unit -> ML (list decl)
