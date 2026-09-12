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

(** Unit interfaces: the `.cui` file, and the index a run consults.

    See section 12 of doc/ref/custard.md.  A Custard unit is a whole program
    with holes, and [FStarC.Custard.Extract.request] is the single place a hole
    can be filled; separate compilation teaches it a third answer, alongside
    "already requested in this run" and "not yet requested": *someone else
    already built that*.

    A `.cui` is a serialized slice of the post-[Layout], post-[Rename] IR with
    the bodies stripped, together with the layout verdict of every type the
    unit reached.  It is deliberately not a source-level interface: none of the
    decisions it has to pin down are source-level decisions. *)
module FStarC.Custard.Unit

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Custard.Syntax

(** One exported declaration.  [ue_key] is the canonical specialization key
    (section 12.3), which is what a downstream [request] looks up; it is
    produced by [Extract.key_of_term] and is independent of every printing
    option. *)
type entry = {
  ue_key:   string;
  ue_decl:  decl;             (** post-[Layout], post-[Rename]; body stripped *)
  ue_type:  option type_info; (** present exactly for a [DType] *)
  (** The F* module whose file this declaration was emitted into, when the
      producing run split its output (section 12.9).  A whole-program unit
      emits everything into one OCaml module named after the unit, and there is
      nothing to say; a split one puts each declaration in a file of its own
      choosing, and a downstream reference has to be qualified by *that* file,
      not by the unit.  It is also what tells the consumer that the name it
      sees may be an at-home one, spelled plainly rather than mangled. *)
  ue_home:  option string;
}

(** The header exists to make a mismatch an error rather than a silent
    miscompilation.  [uh_digests] covers every checked file the run *loaded*,
    not merely those that contributed an emitted declaration: a unit that
    inlines an upstream [inline_for_extraction] definition depends on a body
    that appears in no interface at all (section 12.6). *)
type header = {
  uh_version: int;
  uh_name:    string;
  uh_backend: string;
  uh_options: list (string & string);
  uh_digests: list (string & string);
  (** The header file this unit emitted, for a downstream unit to `#include`
      (section 42.2).  Recorded rather than derived from [uh_name] because
      [-o] is what names it.  [None] for a backend with no header file. *)
  uh_header:  option string;
  (** The name of this unit's global initializer, absent when the unit has no
      globals and so there is nothing for a downstream [main] to call
      (section 42.3). *)
  uh_init:    option string;
}

type iface = {
  ui_header:  header;
  ui_entries: list entry;
}

(** Bumped whenever the IR or this format changes shape.  A `.cui` written by a
    different version is rejected, the same way a stale `.checked` file is. *)
val current_version : int

(** The options that can change a layout, as recorded in a header and compared
    on link. *)
val layout_options : unit -> ML (list (string & string))

val write_iface : string -> iface -> ML unit

(** Read and validate.  Raises a Custard error naming the file if the version,
    the backend or a layout option disagrees with this run. *)
val read_iface : string -> ML iface

(** A readable rendering, for [--custard_dump_cui]. *)
val iface_to_string : iface -> ML string

(** {1 The index} *)

(** Everything the linked units between them export, indexed by key. *)
val links : Type0

val empty_links : links

(** Load and validate every [--custard_link] file.  Two interfaces exporting
    the same key is an error: it would make which one a request resolves to
    depend on link order. *)
val load_links : list string -> ML links

(** The unit an entry came from, and the entry, or [None] for a miss. *)
val lookup : links -> string -> ML (option (string & entry))

val is_empty : links -> ML bool

(** Every file the linked units emitted into (section 12.9).  These names are
    taken: this run may not emit a file of the same name, or the target linker
    would see two compilation units with one name. *)
val link_homes : links -> ML (list string)

(** The header file of each linked unit that has one, in `--custard_link`
    order.  The C backend `#include`s these rather than re-declaring what they
    contain (section 42.2). *)
val link_headers : links -> ML (list string)

(** The global initializer of each linked unit that has one, in
    `--custard_link` order.  The unit holding the entry point calls these
    before its own (section 42.3). *)
val link_inits : links -> ML (list string)
