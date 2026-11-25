(* Types shared across the fstar-depgraph tool. *)

type loc = {
  l_file : string;   (* file name as recorded in the checked file *)
  l_line : int;
  l_col  : int;
  l_end_line : int;
  l_end_col  : int;
}

(* Why a definition is considered "implicitly live" even if nothing refers
   to it syntactically. *)
type liveness_hint =
  | Explicit_root         (* in a root module *)
  | Smt_pattern           (* lemma with an SMT pattern: used by the solver *)
  | Typeclass_instance    (* resolved by instance search *)
  | Tactic_or_plugin      (* [@@plugin], tactics, splices *)
  | Attribute_marked      (* referenced from an attribute *)
  | Generated             (* projector / discriminator / auto-generated *)
  | Effect_member         (* part of an effect declaration *)
  | Exported_by_interface (* val in an .fsti with no other use *)

type def = {
  d_lid       : string;                 (* fully qualified name *)
  d_module    : string;                 (* owning module *)
  d_name      : string;                 (* short name *)
  d_kind      : string;                 (* let / val / type / datacon / ... *)
  d_quals     : string list;
  d_impl_loc  : loc option;             (* location in the .fst *)
  d_decl_loc  : loc option;             (* location in the .fsti *)
  d_refs      : string list;            (* lids referenced by this definition *)
  d_hints     : liveness_hint list;
  d_private   : bool;
  d_generated : bool;
}

type modul = {
  m_name       : string;
  m_iface_file : string option;
  m_impl_file  : string option;
  m_defs       : string list;           (* lids, in source order *)
  m_decl_deps  : string list;           (* module deps recorded in .checked *)
  m_is_root    : bool;
}
