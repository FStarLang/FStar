(* Loading .checked files and extracting module- and definition-level
   dependence information. *)

open Types

module SS = FStarC_Syntax_Syntax
module I  = FStarC_Ident
module RO = FStarC_Range_Ops

let ( ^/ ) a b = Filename.concat a b

(* ------------------------------------------------------------------ *)
(* small helpers over the F* runtime representations                    *)
(* ------------------------------------------------------------------ *)

let of_flist (l : 'a Prims.list) : 'a list = l

let opt_of = function
  | FStar_Pervasives_Native.Some x -> Some x
  | FStar_Pervasives_Native.None -> None

let str_of_lid (l : I.lident) : string = I.string_of_lid l

let loc_of_range (r : FStarC_Range_Type.range) : loc option =
  let f = RO.file_of_range r in
  if f = "" || f = "<dummy>" || f = "dummy" then None
  else
    let s = RO.start_of_range r and e = RO.end_of_range r in
    let line = Z.to_int (RO.line_of_pos s) in
    if line <= 0 then None
    else
      Some { l_file = f;
             l_line = line;
             l_col = Z.to_int (RO.col_of_pos s);
             l_end_line = Z.to_int (RO.line_of_pos e);
             l_end_col = Z.to_int (RO.col_of_pos e) }

(* ------------------------------------------------------------------ *)
(* well-known lids                                                      *)
(* ------------------------------------------------------------------ *)

let smtpat_lids = ["FStar.Pervasives.smt_pat"; "FStar.Pervasives.smt_pat_or"]
let tcinstance_lid = "FStar.Tactics.Typeclasses.tcinstance"
let tcresolve_lid = "FStar.Tactics.Typeclasses.tcresolve"
let plugin_lid = "FStar.Attributes.plugin"

(* ------------------------------------------------------------------ *)
(* indexing checked files and sources                                   *)
(* ------------------------------------------------------------------ *)

type index = {
  (* lowercase module name -> path of the .fst.checked  *)
  impl_checked : (string, string) Hashtbl.t;
  (* lowercase module name -> path of the .fsti.checked *)
  iface_checked : (string, string) Hashtbl.t;
  (* lowercase source basename (e.g. "fstarc.main.fst") -> real path *)
  sources : (string, string) Hashtbl.t;
}

let new_index () = {
  impl_checked = Hashtbl.create 1024;
  iface_checked = Hashtbl.create 1024;
  sources = Hashtbl.create 1024;
}

let rec walk_dir ~(recursive : bool) (dir : string) (f : string -> unit) : unit =
  match Sys.readdir dir with
  | exception _ -> ()
  | entries ->
    Array.iter (fun e ->
      let p = dir ^/ e in
      if Sys.is_directory p then (if recursive then walk_dir ~recursive p f)
      else f p) entries

(* "FStarC.Main.fst.checked" -> ("fstarc.main", false)
   "FStarC.Main.fsti.checked" -> ("fstarc.main", true) *)
let module_of_checked (base : string) : (string * bool) option =
  if Filename.check_suffix base ".fst.checked" then
    Some (String.lowercase_ascii (Filename.chop_suffix base ".fst.checked"), false)
  else if Filename.check_suffix base ".fsti.checked" then
    Some (String.lowercase_ascii (Filename.chop_suffix base ".fsti.checked"), true)
  else None

let index_checked_dir (ix : index) (dir : string) : unit =
  walk_dir ~recursive:true dir (fun p ->
    let base = Filename.basename p in
    match module_of_checked base with
    | Some (m, true) ->
      if not (Hashtbl.mem ix.iface_checked m) then Hashtbl.add ix.iface_checked m p
    | Some (m, false) ->
      if not (Hashtbl.mem ix.impl_checked m) then Hashtbl.add ix.impl_checked m p
    | None -> ())

let index_source_dir (ix : index) (dir : string) : unit =
  walk_dir ~recursive:true dir (fun p ->
    let base = Filename.basename p in
    if Filename.check_suffix base ".fst" || Filename.check_suffix base ".fsti" then begin
      let k = String.lowercase_ascii base in
      if not (Hashtbl.mem ix.sources k) then Hashtbl.add ix.sources k p
    end)

let find_source (ix : index) (file : string) : string option =
  let k = String.lowercase_ascii (Filename.basename file) in
  match Hashtbl.find_opt ix.sources k with
  | Some p -> Some p
  | None -> if Sys.file_exists file then Some file else None

(* ------------------------------------------------------------------ *)
(* per-sigelt extraction                                                *)
(* ------------------------------------------------------------------ *)

type raw_entry = {
  r_lids     : string list;        (* lids defined by this sigelt *)
  r_kind     : string;
  r_quals    : string list;
  r_loc      : loc option;
  r_refs     : string list;
  r_children : string list;        (* datacons of an inductive, actions of an effect *)
  r_generated : bool;
  r_attr_lids : string list;
}

let quals_of (se : SS.sigelt) : string list * bool =
  let generated = ref false in
  let qs =
    List.filter_map (fun (q : SS.qualifier) ->
      match q with
      | SS.Assumption -> Some "assume"
      | SS.New -> Some "new"
      | SS.Private -> Some "private"
      | SS.Unfold_for_unification_and_vcgen -> Some "unfold"
      | SS.Irreducible -> Some "irreducible"
      | SS.Inline_for_extraction -> Some "inline_for_extraction"
      | SS.NoExtract -> Some "noextract"
      | SS.Noeq -> Some "noeq"
      | SS.Unopteq -> Some "unopteq"
      | SS.TotalEffect -> Some "total"
      | SS.Logic -> Some "logic"
      | SS.Reifiable -> Some "reifiable"
      | SS.Reflectable _ -> Some "reflectable"
      | SS.Visible_default -> None
      | SS.Discriminator _ -> generated := true; Some "discriminator"
      | SS.Projector _ -> generated := true; Some "projector"
      | SS.RecordType _ -> Some "record"
      | SS.RecordConstructor _ -> Some "record_ctor"
      | SS.Action _ -> Some "action"
      | SS.ExceptionConstructor -> Some "exn"
      | SS.HasMaskedEffect -> None
      | SS.Effect -> Some "effect"
      | SS.OnlyName -> None
      | SS.InternalAssumption -> generated := true; Some "internal")
      (of_flist se.SS.sigquals)
  in
  (qs, !generated)

(* The generic visitor does not descend into patterns, so constructors that are
   only ever matched on would look unused. We pick them up from the Tm_match
   nodes the visitor does hand us. *)
let rec pat_fvs (acc : (string, unit) Hashtbl.t) (p : SS.pat) : unit =
  match p.SS.v with
  | SS.Pat_cons (fv, _, subs) ->
    let l = str_of_lid (SS.lid_of_fv fv) in
    if not (Hashtbl.mem acc l) then Hashtbl.add acc l ();
    List.iter (fun (sp, _) -> pat_fvs acc sp) (of_flist subs)
  | _ -> ()

let note_term (acc : (string, unit) Hashtbl.t) (t : SS.term) : unit =
  match t.SS.n with
  | SS.Tm_fvar fv ->
    let l = str_of_lid (SS.lid_of_fv fv) in
    if not (Hashtbl.mem acc l) then Hashtbl.add acc l ()
  | SS.Tm_match p ->
    List.iter (fun (pat, _, _) -> pat_fvs acc pat) (of_flist p.SS.brs)
  | _ -> ()

(* Collect every fvar lid occurring anywhere inside a sigelt. *)
let collect_fvars (se : SS.sigelt) : string list =
  let acc = Hashtbl.create 64 in
  let on_term (t : SS.term) : SS.term = note_term acc t; t in
  (try ignore (FStarC_Syntax_Visit.visit_sigelt false on_term (fun u -> u) se)
   with _ -> ());
  Hashtbl.fold (fun k () a -> k :: a) acc []

let collect_fvars_terms (ts : SS.term list) : string list =
  let acc = Hashtbl.create 16 in
  let on_term (t : SS.term) : SS.term = note_term acc t; t in
  List.iter (fun t -> try ignore (FStarC_Syntax_Visit.visit_term false on_term t) with _ -> ()) ts;
  Hashtbl.fold (fun k () a -> k :: a) acc []

(* Lids mentioned by qualifiers: a projector or discriminator refers to the
   data constructor it belongs to, an action to its effect, and so on. *)
let qual_lids (se : SS.sigelt) : string list =
  List.filter_map (fun (q : SS.qualifier) ->
    match q with
    | SS.Reflectable l -> Some (str_of_lid l)
    | SS.Discriminator l -> Some (str_of_lid l)
    | SS.Projector (l, _) -> Some (str_of_lid l)
    | SS.Action l -> Some (str_of_lid l)
    | _ -> None) (of_flist se.SS.sigquals)

let lbname_lid (lb : SS.letbinding) : string option =
  match lb.SS.lbname with
  | FStar_Pervasives.Inr fv -> Some (str_of_lid (SS.lid_of_fv fv))
  | FStar_Pervasives.Inl _ -> None

(* Turn one sigelt into zero or more raw entries. Sig_bundle is flattened. *)
let rec entries_of_sigelt (se : SS.sigelt) : raw_entry list =
  let quals, generated = quals_of se in
  let loc = loc_of_range se.SS.sigrng in
  let attrs = of_flist se.SS.sigattrs in
  let attr_lids = collect_fvars_terms attrs in
  let qlids = qual_lids se in
  let mk ?(children=[]) ?(gen=generated) kind lids refs =
    { r_lids = lids; r_kind = kind; r_quals = quals; r_loc = loc;
      r_refs = qlids @ refs; r_children = children; r_generated = gen;
      r_attr_lids = attr_lids }
  in
  match se.SS.sigel with
  | SS.Sig_bundle p ->
    (* Attach the bundle's location to nested sigelts that lack one. *)
    List.concat_map (fun se' ->
      let es = entries_of_sigelt se' in
      List.map (fun e -> if e.r_loc = None then { e with r_loc = loc } else e) es)
      (of_flist p.SS.ses)

  | SS.Sig_fail _ -> []   (* expected-failure test blocks: not real definitions *)

  | SS.Sig_inductive_typ p ->
    let lid = str_of_lid p.SS.lid in
    let refs = collect_fvars se in
    let children = List.map str_of_lid (of_flist p.SS.ds) in
    let mutuals = List.map str_of_lid (of_flist p.SS.mutuals) in
    [ mk ~children "type" [lid] (mutuals @ refs) ]

  | SS.Sig_datacon p ->
    let lid = str_of_lid p.SS.lid1 in
    let refs = collect_fvars se in
    let ty = str_of_lid p.SS.ty_lid in
    let projs = List.map str_of_lid (of_flist p.SS.proj_disc_lids) in
    [ mk ~children:projs "datacon" [lid] (ty :: refs) ]

  | SS.Sig_declare_typ p ->
    let lid = str_of_lid p.SS.lid2 in
    [ mk "val" [lid] (collect_fvars se) ]

  | SS.Sig_assume p ->
    [ mk "assume" [str_of_lid p.SS.lid3] (collect_fvars se) ]

  | SS.Sig_let p ->
    let (is_rec, lbs) = p.SS.lbs1 in
    let lbs = of_flist lbs in
    let kind = if is_rec then "let rec" else "let" in
    let single = (match lbs with [_] -> true | _ -> false) in
    (* Each let-binding in a mutually recursive group becomes its own node.
       For a singleton group the sigelt range already starts at the `let`
       keyword; for a mutual group we fall back to each binding's own
       position (snapped to column 0) so that the nodes are distinguishable. *)
    List.filter_map (fun (lb : SS.letbinding) ->
      match lbname_lid lb with
      | None -> None
      | Some lid ->
        let refs = collect_fvars_terms [lb.SS.lbtyp; lb.SS.lbdef] in
        let refs = qlids @ attr_lids @ refs @ collect_fvars_terms (of_flist lb.SS.lbattrs) in
        let l =
          if single then loc
          else match loc_of_range lb.SS.lbpos with
               | Some l -> Some { l with l_col = 0 }
               | None -> loc
        in
        Some { r_lids = [lid]; r_kind = kind; r_quals = quals; r_loc = l;
               r_refs = refs; r_children = []; r_generated = generated;
               r_attr_lids = attr_lids })
      lbs

  | SS.Sig_new_effect ed ->
    let lid = str_of_lid ed.SS.mname in
    [ mk "effect" [lid] (collect_fvars se) ]

  | SS.Sig_sub_effect sub ->
    let s = str_of_lid sub.SS.source and t = str_of_lid sub.SS.target in
    [ mk "sub_effect" [s ^ " ~> " ^ t] (s :: t :: collect_fvars se) ]

  | SS.Sig_effect_abbrev p ->
    [ mk "effect_abbrev" [str_of_lid p.SS.lid4] (collect_fvars se) ]

  | SS.Sig_splice p ->
    let lids = List.map str_of_lid (of_flist p.SS.lids2) in
    [ mk ~gen:true "splice" lids (collect_fvars se) ]

  | SS.Sig_pragma _ -> []

(* ------------------------------------------------------------------ *)
(* loading modules                                                      *)
(* ------------------------------------------------------------------ *)

type loaded = {
  lo_name    : string;
  lo_iface   : bool;
  lo_entries : raw_entry list;
  lo_deps    : string list;     (* lowercase module names *)
  lo_file    : string option;   (* source file recorded in the module *)
}

let load_checked (path : string) : loaded option =
  match FStarC_CheckedFiles.unsafe_raw_load_checked_file path with
  | FStar_Pervasives_Native.Some (_pd, deps, tcr) ->
    let m = tcr.FStarC_CheckedFiles.checked_module in
    let name = str_of_lid m.SS.name in
    let entries = List.concat_map entries_of_sigelt (of_flist m.SS.declarations) in
    let deps =
      of_flist deps
      |> List.filter_map (fun d ->
           (* deps are recorded as lowercase module names, without extension *)
           let d = String.lowercase_ascii d in
           if d = "source" || d = "interface" || d = "" then None else Some d)
      |> List.sort_uniq compare
    in
    let file =
      List.fold_left (fun acc e ->
        match acc, e.r_loc with
        | Some _, _ -> acc
        | None, Some l -> Some l.l_file
        | None, None -> None) None entries
    in
    Some { lo_name = name;
           lo_iface = m.SS.is_interface;
           lo_entries = entries;
           lo_deps = deps;
           lo_file = file }
  | _ -> None
