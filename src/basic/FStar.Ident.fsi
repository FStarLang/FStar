#light "off"
module FStar.Ident

open FStar.Range

(** A (short) identifier for a local name.
 *  e.g. x in `fun x -> ...` *)
type ident

(** A module path *)
type path = list<string>

(** A module path, as idents *)
type ipath = list<ident>

(** Create an ident *)
val mk_ident            : (string * range) -> ident

(** Obtain the range of an ident *)
val range_of_id         : ident -> range

(** Create an ident with a dummyRange (avoid if possible) *)
val id_of_text          : string -> ident

(** The prefix for reserved identifiers *)
val reserved_prefix     : string

(** Set the range on an ident *)
val set_id_range        : range -> ident -> ident

(** Equality of idents *)
val ident_equals        : ident -> ident -> bool

(** Print an ident *)
val text_of_id          : ident -> string





(** Gensym, generating fresh names *)
val reset_gensym        : unit -> unit
val next_id             : unit -> int
val gen'                : string -> range -> ident
val gen                 : range -> ident

(** Turn a string of shape A.B.C into a path *)
val path_of_text        : string -> path

(** Turn a namespace, a list of idents, into a path *)
val path_of_ns          : ipath -> path





(** A long identifier for top-level, fully-qualified names.
    e.g. Prims.string. Essentially a list of idents where
    the last one denotes a name, and all the others denote a
    module path that qualifies the name. *)
type lident
type lid = lident

(** Obtain the range of an lid *)
val range_of_lid        : lident -> range

(* Return the name in an lid *)
val ident_of_lid        : lident -> ident

(** Equality of lidents *)
val lid_equals          : lident -> lident -> bool

(** Turn an lid into a path *)
val path_of_lid         : lident -> path

(** Return an lid as a path (containing the name itself).
    e.g. ids_of_lid Prims.string = [Prims; string] *)
val ids_of_lid          : lident -> ipath

(** Return the namespace of an lid (not including its name).
    e.g. ns_of_lid Prims.string = [Prims] *)
val ns_of_lid           : lident -> ipath

(** Create an lid from a ipath and a name *)
val lid_of_ns_and_id    : ipath -> ident -> lident

(** Create an lid from a ipath (last ident is the name) *)
val lid_of_ids          : ipath -> lident

(** Create an lid from a string, separating it by "." *)
val lid_of_str          : string -> lident

(** Create an lid from a (string) path and a range *)
val lid_of_path         : path -> range -> lident

(** Set the range on an lid *)
val set_lid_range       : lident -> range -> lident

(** Add a component to an lid *)
val lid_add_suffix      : lident -> string -> lident

(** Qualify an ident by a module. Similar to lid_add_suffix, but the
    range is taken from the ident instead. *)
val qual_id             : lident -> ident -> lident

(** Print an lid. This is O(1). *)
val string_of_lid       : lident -> string

(** Print the namespace portion of an lid. This is O(1). *)
val nsstr               : lident -> string

(** Print a path as A.B.C *)
val text_of_path        : path -> string

(* Similar to string_of_lid, but separates with "_" instead of "." *)
val ml_path_of_lid      : lident -> string
