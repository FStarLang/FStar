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

(** Layout analysis: erasure, newtype collapse and cast elimination.

    This is phase 3 (and the corresponding part of phase 4) of Custard; see
    section 5 of doc/ref/custard.md.

    A layout is not just a tag: it records *which* source field survives in
    *which* target slot, because every constructor application, projection and
    pattern has to be rewritten accordingly.  Knowing only that
    [type foo = { a: prop; b: bool }] "is a newtype" does not say whether
    [Mkfoo a b] translates to [a] or to [b]. *)
module FStarC.Custard.Layout

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Custard.Syntax

(** Where a source field ends up in the target representation. *)
type slot =
  | S_erased            (** the field has no runtime representation *)
  | S_at of int         (** the field lives at target position i *)

type ctor_layout = {
  cl_name:   name;
  cl_tag:    option int;          (** [None] when the type has a single ctor *)
  cl_slots:  list slot;           (** one per *source* field, in source order *)
  cl_arity:  int;                 (** number of surviving fields *)
  cl_fields: list (string & cty); (** the surviving fields, in target order *)
}

type newtype_layout = {
  nt_ctor:  name;
  nt_field: string;
  nt_index: int;   (** index of the surviving field in the *source* field list *)
  nt_ty:    cty;   (** the payload type, in terms of the type's parameters *)
}

type layout =
  | L_erased                            (** no runtime representation at all *)
  | L_newtype of newtype_layout         (** exactly one field survives *)
  | L_struct  of list ctor_layout
  | L_abbrev  of cty                    (** a transparent abbreviation *)
  | L_opaque                            (** abstract or externally realized *)

val layout_to_string : layout -> ML string

(** [run prog] computes the layout of every type declaration in [prog] and
    rewrites the program accordingly: erased types and their fields, arguments
    and patterns are deleted, single-field types are collapsed to their
    payload, and casts that have become identities are removed. *)
val run : program -> ML program
