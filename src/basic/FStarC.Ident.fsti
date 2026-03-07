(*
   Copyright 2008-2014 Microsoft Research

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
module FStarC.Ident

open FStarC.Effect
open FStarC.Range.Type
open FStarC.Class.Show
open FStarC.Class.HasRange
open FStarC.Class.Deq
open FStarC.Class.Ord
open FStarC.Class.PP

(** A (short) identifier for a local name.
 *  e.g. x in `fun x -> ...` *)
[@@ PpxDerivingYoJson; PpxDerivingShow ]
new val ident : Type0

// type ident

(** A module path *)
[@@ PpxDerivingYoJson; PpxDerivingShow ]
type path = list string

(** A module path, as idents *)
[@@ PpxDerivingYoJson; PpxDerivingShow ]
type ipath = list ident

(** A long identifier for top-level, fully-qualified names.
    e.g. Prims.string. Essentially a list of idents where
    the last one denotes a name, and all the others denote a
    module path that qualifies the name. *)
[@@ PpxDerivingYoJson; PpxDerivingShow ]
new val lident : Type0

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type lid = lident

(** Create an ident *)
val mk_ident            : (string & range) -> ident

(** Set the range on an ident *)
val set_id_range        : range -> ident -> ident

(** The prefix for reserved identifiers *)
val reserved_prefix     : string

(** Generating fresh names, uses GenSym. *)
val gen'                : string -> range -> ML ident
val gen                 : range -> ML ident

(* Return the name in an lid *)
val ident_of_lid        : lident -> ident

(** Obtain the range of an ident *)
val range_of_id         : ident -> range

(** Create an ident with a dummyRange (avoid if possible) *)
val id_of_text          : string -> ident

(** Print an ident *)
val string_of_id        : ident -> string

(** Print a path as A.B.C *)
val text_of_path        : path -> string

(** Turn a string of shape A.B.C into a path *)
val path_of_text        : string -> path

(** Turn a namespace, a list of idents, into a path *)
val path_of_ns          : ipath -> ML path

(** Turn an lid into a path *)
val path_of_lid         : lident -> ML path

(** Return the namespace of an lid (not including its name).
    e.g. ns_of_lid Prims.string = [Prims] *)
val ns_of_lid           : lident -> ipath

(** Return an lid as a path (containing the name itself).
    e.g. ids_of_lid Prims.string = [Prims; string] *)
val ids_of_lid          : lident -> ipath

(** Create an lid from a ipath and a name *)
val lid_of_ns_and_id    : ipath -> ident -> ML lident

(* Create a lid from an indent, with an empty path *)
val id_as_lid           : ident -> ML lident

(** Create an lid from a ipath (last ident is the name) *)
val lid_of_ids          : ipath -> ML lident

(** Create an lid from a string, separating it by "." *)
val lid_of_str          : string -> ML lident

(** Create an lid from a (string) path and a range *)
val lid_of_path         : path -> range -> ML lident

(** Print an lid. This is O(1). *)
val text_of_lid         : lident -> string

(** Equality of lidents *)
val lid_equals          : lident -> lident -> bool

(** Equality of idents *)
val ident_equals        : ident -> ident -> bool

(** Obtain the range of an lid *)
val range_of_lid        : lident -> range

(** Set the range on an lid *)
val set_lid_range       : lident -> range -> lident

(** Add a component to an lid *)
val lid_add_suffix      : lident -> string -> ML lident

(* Similar to string_of_lid, but separates with "_" instead of "." *)
val ml_path_of_lid      : lident -> ML string

(** Print an lid. This is O(1). *)
val string_of_lid       : lident -> string

(** Qualify an ident by a module. Similar to lid_add_suffix, but the
    range is taken from the ident instead. *)
val qual_id             : lident -> ident -> ML lident

(** Print the namespace portion of an lid. This is O(1). *)
val nsstr               : lident -> string

(* Showable instances *)
instance val showable_ident  : showable ident
instance val showable_lident : showable lident
instance val pretty_ident    : pretty ident
instance val pretty_lident   : pretty lident
instance val hasrange_ident  : hasRange ident
instance val hasrange_lident : hasRange lident
instance val deq_ident  : deq ident
instance val deq_lident : deq lident
instance val ord_ident  : ord ident
instance val ord_lident : ord lident
