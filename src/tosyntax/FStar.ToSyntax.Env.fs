(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
#light "off"
// (c) Microsoft Corporation. All rights reserved

module FStar.ToSyntax.Env
open FStar.All


open FStar
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Util
open FStar.Syntax.Const
open FStar.Parser
open FStar.Ident
open FStar.Errors
module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module BU = FStar.Util

type local_binding = (ident * bv * bool)                  (* local name binding for name resolution, paired with an env-generated unique name and a boolean that is true when the variable has been introduced with let-mutable *)
type rec_binding   = (ident * lid * delta_depth)          (* name bound by recursive type and top-level let-bindings definitions only *)
type module_abbrev = (ident * lident)                     (* module X = A.B.C, where A.B.C is fully qualified and already resolved *)

type open_kind =                                          (* matters only for resolving names with some module qualifier *)
| Open_module                                             (* only opens the module, not the namespace *)
| Open_namespace                                          (* opens the whole namespace *)

type open_module_or_namespace = (lident * open_kind)      (* lident fully qualified name, already resolved. *)

type record_or_dc = {
  typename: lident; (* the namespace part applies to the constructor and fields as well *)
  constrname: ident;
  parms: binders;
  fields: list<(ident * typ)>;
  is_private_or_abstract: bool;
  is_record:bool
}

type scope_mod =
| Local_binding            of local_binding
| Rec_binding              of rec_binding
| Module_abbrev            of module_abbrev
| Open_module_or_namespace of open_module_or_namespace
| Top_level_def            of ident           (* top-level definition for an unqualified identifier x to be resolved as curmodule.x. *)
| Record_or_dc             of record_or_dc    (* to honor interleavings of "open" and record definitions *)

type string_set = set<string>

type exported_id_kind = (* kinds of identifiers exported by a module *)
| Exported_id_term_type (* term and type identifiers *)
| Exported_id_field     (* field identifiers *)
type exported_id_set = exported_id_kind -> ref<string_set>

type env = {
  curmodule:            option<lident>;                   (* name of the module being desugared *)
  curmonad:             option<ident>;                    (* current monad being desugared *)
  modules:              list<(lident * modul)>;           (* previously desugared modules *)
  scope_mods:           list<scope_mod>;                  (* toplevel or definition-local scope modifiers *)
  exported_ids:         BU.smap<exported_id_set>;         (* identifiers (stored as strings for efficiency)
                                                             reachable in a module, not shadowed by "include"
                                                             declarations. Used only to handle such shadowings,
                                                             not "private"/"abstract" definitions which it is
                                                             enough to just remove from the sigmap. Formally,
                                                             iden is in exported_ids[ModulA] if, and only if,
                                                             there is no 'include ModulB' (with ModulB.iden
                                                             defined or reachable) after iden in ModulA. *)
  trans_exported_ids:   BU.smap<exported_id_set>;         (* transitive version of exported_ids along the
                                                             "include" relation: an identifier is in this set
                                                             for a module if and only if it is defined either
                                                             in this module or in one of its included modules. *)
  includes:             BU.smap<(ref<(list<lident>)>)>;   (* list of "includes" declarations for each module. *)
  sigaccum:             sigelts;                          (* type declarations being accumulated for the current module *)
  sigmap:               BU.smap<(sigelt * bool)>;         (* bool indicates that this was declared in an interface file *)
  iface:                bool;                             (* whether or not we're desugaring an interface; different scoping rules apply *)
  admitted_iface:       bool;                             (* is it an admitted interface; different scoping rules apply *)
  expect_typ:           bool;                             (* syntactically, expect a type at this position in the term *)
  docs:                 BU.smap<Parser.AST.fsdoc>;        (* Docstrings of lids *)
  remaining_iface_decls:list<(lident*list<Parser.AST.decl>)>;  (* A map from interface names to their stil-to-be-processed top-level decls *)
  syntax_only:          bool;                             (* Whether next push should skip type-checking *)
}

type foundname =
  | Term_name of typ * bool // indicates if mutable
  | Eff_name  of sigelt * lident

let set_iface env b = {env with iface=b}
let iface e = e.iface
let set_admitted_iface e b = {e with admitted_iface=b}
let admitted_iface e = e.admitted_iface
let set_expect_typ e b = {e with expect_typ=b}
let expect_typ e = e.expect_typ
let all_exported_id_kinds: list<exported_id_kind> = [ Exported_id_field; Exported_id_term_type ]
let transitive_exported_ids env lid =
    let module_name = Ident.string_of_lid lid in
    match BU.smap_try_find env.trans_exported_ids module_name with
    | None -> []
    | Some exported_id_set -> !(exported_id_set Exported_id_term_type) |> BU.set_elements
let open_modules e = e.modules
let set_current_module e l = {e with curmodule=Some l}
let current_module env = match env.curmodule with
    | None -> failwith "Unset current module"
    | Some m -> m
let iface_decls env l =
    match env.remaining_iface_decls |>
          List.tryFind (fun (m, _) -> Ident.lid_equals l m) with
    | None -> None
    | Some (_, decls) -> Some decls
let set_iface_decls env l ds =
    let _, rest =
        FStar.List.partition
            (fun (m, _) -> Ident.lid_equals l m)
            env.remaining_iface_decls in
    {env with remaining_iface_decls=(l, ds)::rest}
let qual = qual_id
let qualify env id =
    match env.curmonad with
    | None -> qual (current_module env) id
    | Some monad -> mk_field_projector_name_from_ident (qual (current_module env) monad) id
let syntax_only env = env.syntax_only
let set_syntax_only env b = { env with syntax_only = b }
let new_sigmap () = BU.smap_create 100
let empty_env () = {curmodule=None;
                    curmonad=None;
                    modules=[];
                    scope_mods=[];
                    exported_ids=new_sigmap();
                    trans_exported_ids=new_sigmap();
                    includes=new_sigmap();
                    sigaccum=[];
                    sigmap=new_sigmap();
                    iface=false;
                    admitted_iface=false;
                    expect_typ=false;
                    docs=new_sigmap();
                    remaining_iface_decls=[];
                    syntax_only=false}

let sigmap env = env.sigmap
let has_all_in_scope env =
  List.existsb (fun (m, _) ->
    lid_equals m Const.all_lid) env.modules

let set_bv_range bv r =
    let id = {bv.ppname with idRange=r} in
    {bv with ppname=id}

let bv_to_name bv r = bv_to_name (set_bv_range bv r)

let unmangleMap = [("op_ColonColon", "Cons", Delta_constant, Some Data_ctor);
                   ("not", "op_Negation", Delta_equational, None)]

let unmangleOpName (id:ident) : option<(term * bool)> =
  let t =
  find_map unmangleMap (fun (x,y,dd,dq) ->
    if (id.idText = x) then Some (S.fvar (lid_of_path ["Prims"; y] id.idRange) dd dq)
    else None)
  in
  match t with
  | Some v -> Some (v, false)
  | None -> None

type cont_t<'a> =
    | Cont_ok of 'a  (* found *)
    | Cont_fail      (* not found, do not retry *)
    | Cont_ignore    (* not found, retry *)

let option_of_cont (k_ignore: unit -> option<'a>) = function
    | Cont_ok a -> Some a
    | Cont_fail -> None
    | Cont_ignore -> k_ignore ()

(* Unqualified identifier lookup *)

let find_in_record ns id record cont =
 let typename' = lid_of_ids (ns @ [record.typename.ident]) in
 if lid_equals typename' record.typename
 then
      let fname = lid_of_ids (record.typename.ns @ [id]) in
      let find = BU.find_map record.fields (fun (f, _) ->
        if id.idText = f.idText
        then Some record
        else None)
      in
      match find with
      | Some r -> cont r
      | None -> Cont_ignore
 else
      Cont_ignore

let get_exported_id_set (e: env) (mname: string) : option<(exported_id_kind -> ref<string_set>)> =
    BU.smap_try_find e.exported_ids mname

let get_trans_exported_id_set (e: env) (mname: string) : option<(exported_id_kind -> ref<string_set>)> =
    BU.smap_try_find e.trans_exported_ids mname

let string_of_exported_id_kind = function
    | Exported_id_field -> "field"
    | Exported_id_term_type -> "term/type"

let find_in_module_with_includes
    (eikind: exported_id_kind)
    (find_in_module: lident -> cont_t<'a>)
    (find_in_module_default: cont_t<'a>)
    env
    (ns: lident)
    (id: ident)
    : cont_t<'a> =
  let idstr = id.idText in
  let rec aux = function
  | [] ->
    find_in_module_default
  | modul :: q ->
    let mname = modul.str in
    let not_shadowed = match get_exported_id_set env mname with
    | None -> true
    | Some mex ->
      let mexports = !(mex eikind) in
      BU.set_mem idstr mexports
    in
    let mincludes = match BU.smap_try_find env.includes mname with
    | None -> []
    | Some minc -> !minc
    in
    let look_into =
     if not_shadowed
     then find_in_module (qual modul id)
     else Cont_ignore
    in
    begin match look_into with
    | Cont_ignore ->
      aux (mincludes @ q)
    | _ ->
      look_into
    end
  in aux [ ns ]

let is_exported_id_field = function
  | Exported_id_field -> true
  | _ -> false

let try_lookup_id''
  env
  (id: ident)
  (eikind: exported_id_kind)
  (k_local_binding: local_binding -> cont_t<'a>)
  (k_rec_binding:   rec_binding   -> cont_t<'a>)
  (k_record: (record_or_dc) -> cont_t<'a>)
  (find_in_module: lident -> cont_t<'a>)
  (lookup_default_id: cont_t<'a> -> ident -> cont_t<'a>)
  =
    let check_local_binding_id : local_binding -> bool = function
      (id', _, _) -> id'.idText=id.idText
    in
    let check_rec_binding_id : rec_binding -> bool = function
      (id', _, _) -> id'.idText=id.idText
    in
    let curmod_ns = ids_of_lid (current_module env) in
    let proc = function
      | Local_binding l
        when check_local_binding_id l ->
        k_local_binding l

      | Rec_binding r
        when check_rec_binding_id r ->
        k_rec_binding r

      | Open_module_or_namespace (ns, _) ->
        find_in_module_with_includes eikind find_in_module Cont_ignore env ns id

      | Top_level_def id'
        when id'.idText = id.idText ->
        (* indicates a global definition shadowing previous
        "open"s. If the definition is not actually found by the
        [lookup_default_id] finder, then it may mean that we are in a
        module and the [val] was already declared, with the actual
        [let] not defined yet, so we must not fail, but ignore. *)
        lookup_default_id Cont_ignore id

      | Record_or_dc r
        when (is_exported_id_field eikind) ->
        find_in_module_with_includes Exported_id_field (
            fun lid ->
            let id = lid.ident in
            find_in_record lid.ns id r k_record
        ) Cont_ignore env (lid_of_ids curmod_ns) id

      | _ ->
        Cont_ignore
    in
    let rec aux = function
      | a :: q ->
        option_of_cont (fun _ -> aux q) (proc a)
      | [] ->
        option_of_cont (fun _ -> None) (lookup_default_id Cont_fail id)

    in aux env.scope_mods

let found_local_binding r (id', x, mut) =
    (bv_to_name x r, mut)

let find_in_module env lid k_global_def k_not_found =
    begin match BU.smap_try_find (sigmap env) lid.str with
        | Some sb -> k_global_def lid sb
        | None -> k_not_found
    end

let try_lookup_id env (id:ident) =
  match unmangleOpName id with
  | Some f -> Some f
  | _ ->
    try_lookup_id'' env id Exported_id_term_type (fun r -> Cont_ok (found_local_binding id.idRange r)) (fun _ -> Cont_fail) (fun _ -> Cont_ignore) (fun i -> find_in_module env i (fun _ _ -> Cont_fail) Cont_ignore) (fun _ _ -> Cont_fail)

(* Unqualified identifier lookup, if lookup in all open namespaces failed. *)

let lookup_default_id
    env
    (id: ident)
    (k_global_def: lident -> sigelt * bool -> cont_t<'a>)
    (k_not_found: cont_t<'a>)
  =
  let find_in_monad = match env.curmonad with
  | Some _ ->
    let lid = qualify env id in
    begin match BU.smap_try_find (sigmap env) lid.str with
    | Some r -> Some (k_global_def lid r)
    | None -> None
    end
  | None -> None
  in
  match find_in_monad with
  | Some v -> v
  | None ->
    let lid = qual (current_module env) id in
    find_in_module env lid k_global_def k_not_found

let module_is_defined env lid =
    (match env.curmodule with
     | None -> false
     | Some m -> lid_equals lid (current_module env)) ||
    List.existsb (fun x -> lid_equals lid (fst x)) env.modules

let resolve_module_name env lid (honor_ns: bool) : option<lident> =
    let nslen = List.length lid.ns in
    let rec aux = function
        | [] ->
          if module_is_defined env lid
          then Some lid
          else None

        | Open_module_or_namespace (ns, Open_namespace) :: q
          when honor_ns ->
          let new_lid = lid_of_path (path_of_lid ns @ path_of_lid lid) (range_of_lid lid)
          in
          if module_is_defined env new_lid
          then
               Some new_lid
          else aux q

        | Module_abbrev (name, modul) :: _
          when nslen = 0 && name.idText = lid.ident.idText ->
          Some modul

        | _ :: q ->
          aux q

    in
    aux env.scope_mods

(** Forbid self-references to current module (#451) *)

let fail_if_curmodule env ns_original ns_resolved =
  if lid_equals ns_resolved (current_module env)
  then
    if lid_equals ns_resolved FStar.Syntax.Const.prims_lid
    then () // disable this check for Prims, because of Prims.unit, etc.
    else raise (Error (BU.format1 "Reference %s to current module is forbidden (see GitHub issue #451)" ns_original.str, range_of_lid ns_original))
  else ()

let fail_if_qualified_by_curmodule env lid =
  match lid.ns with
  | [] -> ()
  | _ ->
    let modul_orig = lid_of_ids lid.ns in
    begin match resolve_module_name env modul_orig true with
    | Some modul_res -> fail_if_curmodule env modul_orig modul_res
    | _ -> ()
    end

let namespace_is_open env lid =
  List.existsb (function
                | Open_module_or_namespace (ns, Open_namespace) -> lid_equals lid ns
                | _ -> false) env.scope_mods

let shorten_module_path env ids is_full_path =
  // FIXME this could be faster (module_is_defined and namespace_is_open are slow)
  let rec aux revns id =
    let lid = FStar.Ident.lid_of_ns_and_id (List.rev revns) id in
    if namespace_is_open env lid
    then Some (List.rev (id :: revns), [])
    else match revns with
         | [] -> None
         | ns_last_id :: rev_ns_prefix ->
           aux rev_ns_prefix ns_last_id |>
             BU.map_option (fun (stripped_ids, rev_kept_ids) ->
                            (stripped_ids, id :: rev_kept_ids)) in
  if is_full_path && module_is_defined env (FStar.Ident.lid_of_ids ids)
  then (ids, []) // FIXME is that right? If m is defined then all names in m are accessible?
  else match List.rev ids with
       | [] -> ([], [])
       | ns_last_id :: ns_rev_prefix ->
         match aux ns_rev_prefix ns_last_id with
         | None -> ([], ids)
         | Some (stripped_ids, rev_kept_ids) -> (stripped_ids, List.rev rev_kept_ids)

let shorten_lid env lid =
  let (_, short) = shorten_module_path env lid.ns true in
  lid_of_ns_and_id short lid.ident

(* Generic name resolution. *)

let resolve_in_open_namespaces''
  env
  lid
  (eikind: exported_id_kind)
  (k_local_binding: local_binding -> cont_t<'a>)
  (k_rec_binding:   rec_binding   -> cont_t<'a>)
  (k_record: (record_or_dc) -> cont_t<'a>)
  (f_module: lident -> cont_t<'a>)
  (l_default: cont_t<'a> -> ident -> cont_t<'a>)
  : option<'a> =
  match lid.ns with
  | _ :: _ ->
    begin match resolve_module_name env (set_lid_range (lid_of_ids lid.ns) (range_of_lid lid)) true with
    | None -> None
    | Some modul ->
        option_of_cont (fun _ -> None) (find_in_module_with_includes eikind f_module Cont_fail env modul lid.ident)
    end
  | [] ->
    try_lookup_id'' env lid.ident eikind k_local_binding k_rec_binding k_record f_module l_default

let cont_of_option (k_none: cont_t<'a>) = function
    | Some v -> Cont_ok v
    | None -> k_none

let resolve_in_open_namespaces'
  env
  lid
  (k_local_binding: local_binding -> option<'a>)
  (k_rec_binding:   rec_binding   -> option<'a>)
  (k_global_def: lident -> (sigelt * bool) -> option<'a>)
  : option<'a> =
  let k_global_def' k lid def = cont_of_option k (k_global_def lid def) in
  let f_module lid' = let k = Cont_ignore in find_in_module env lid' (k_global_def' k) k in
  let l_default k i = lookup_default_id env i (k_global_def' k) k in
  resolve_in_open_namespaces'' env lid Exported_id_term_type (fun l -> cont_of_option Cont_fail (k_local_binding l)) (fun r -> cont_of_option Cont_fail (k_rec_binding r)) (fun _ -> Cont_ignore) f_module l_default

let fv_qual_of_se = fun se -> match se.sigel with
    | Sig_datacon(_, _, _, l, _, _) ->
      let qopt = BU.find_map se.sigquals (function
          | RecordConstructor (_, fs) -> Some (Record_ctor(l, fs))
          | _ -> None) in
      begin match qopt with
        | None -> Some Data_ctor
        | x -> x
      end
    | Sig_declare_typ (_, _, _) ->  //TODO: record projectors?
      None
    | _ -> None

let lb_fv lbs lid =
     BU.find_map lbs  (fun lb ->
        let fv = right lb.lbname in
        if S.fv_eq_lid fv lid then Some fv else None) |> must

let ns_of_lid_equals (lid: lident) (ns: lident) =
    List.length lid.ns = List.length (ids_of_lid ns) &&
    lid_equals (lid_of_ids lid.ns) ns

let try_lookup_name any_val exclude_interf env (lid:lident) : option<foundname> =
  let occurrence_range = Ident.range_of_lid lid in

  let k_global_def source_lid = function
      | (_, true) when exclude_interf -> None
      | (se, _) ->
        begin match se.sigel with
          | Sig_inductive_typ _ ->   Some (Term_name(S.fvar source_lid Delta_constant None, false))
          | Sig_datacon _ ->         Some (Term_name(S.fvar source_lid Delta_constant (fv_qual_of_se se), false))
          | Sig_let((_, lbs), _, _) ->
            let fv = lb_fv lbs source_lid in
            Some (Term_name(S.fvar source_lid fv.fv_delta fv.fv_qual, false))
          | Sig_declare_typ(lid, _, _) ->
            let quals = se.sigquals in
            if any_val //only in scope in an interface (any_val is true) or if the val is assumed
            || quals |> BU.for_some (function Assumption -> true | _ -> false)
            then let lid = Ident.set_lid_range lid (Ident.range_of_lid source_lid) in
                 let dd = if U.is_primop_lid lid
                          || (ns_of_lid_equals lid FStar.Syntax.Const.prims_lid && quals |> BU.for_some (function Projector _ | Discriminator _ -> true | _ -> false))
                          then Delta_equational
                          else Delta_constant in
                 begin match BU.find_map quals (function Reflectable refl_monad -> Some refl_monad | _ -> None) with //this is really a M?.reflect
                 | Some refl_monad ->
                        let refl_const = S.mk (Tm_constant (FStar.Const.Const_reflect refl_monad)) None occurrence_range in
                        Some (Term_name (refl_const, false))
                 | _ -> Some (Term_name(fvar lid dd (fv_qual_of_se se), false))
                 end
            else None
          | Sig_new_effect_for_free (ne) | Sig_new_effect(ne) -> Some (Eff_name(se, set_lid_range ne.mname (range_of_lid source_lid)))
          | Sig_effect_abbrev _ ->   Some (Eff_name(se, source_lid))
          | _ -> None
        end in

  let k_local_binding r = Some (Term_name (found_local_binding (range_of_lid lid) r))
  in

  let k_rec_binding (id, l, dd) = Some (Term_name(S.fvar (set_lid_range l (range_of_lid lid)) dd None, false))
  in

  let found_unmangled = match lid.ns with
  | [] ->
    begin match unmangleOpName lid.ident with
    | Some f -> Some (Term_name f)
    | _ -> None
    end
  | _ -> None
  in

  match found_unmangled with
  | None -> resolve_in_open_namespaces'  env lid k_local_binding k_rec_binding k_global_def
  | x -> x

let try_lookup_effect_name' exclude_interf env (lid:lident) : option<(sigelt*lident)> =
  match try_lookup_name true exclude_interf env lid with
    | Some (Eff_name(o, l)) -> Some (o,l)
    | _ -> None
let try_lookup_effect_name env l =
    match try_lookup_effect_name' (not env.iface) env l with
        | Some (o, l) -> Some l
        | _ -> None
let try_lookup_effect_name_and_attributes env l =
    match try_lookup_effect_name' (not env.iface) env l with
        | Some ({ sigel = Sig_new_effect(ne) }, l) -> Some (l, ne.cattributes)
        | Some ({ sigel = Sig_new_effect_for_free(ne) }, l) -> Some (l, ne.cattributes)
        | Some ({ sigel = Sig_effect_abbrev(_,_,_,_,cattributes) }, l) -> Some (l, cattributes)
        | _ -> None
let try_lookup_effect_defn env l =
    match try_lookup_effect_name' (not env.iface) env l with
        | Some ({ sigel = Sig_new_effect(ne) }, _) -> Some ne
        | Some ({ sigel = Sig_new_effect_for_free(ne) }, _) -> Some ne
        | _ -> None
let is_effect_name env lid =
    match try_lookup_effect_name env lid with
        | None -> false
        | Some _ -> true
(* Same as [try_lookup_effect_name], but also traverses effect
abbrevs. TODO: once indexed effects are in, also track how indices and
other arguments are instantiated. *)
let try_lookup_root_effect_name env l =
    match try_lookup_effect_name' (not env.iface) env l with
	| Some ({ sigel = Sig_effect_abbrev (l', _, _, _, _) }, _) ->
	  let rec aux new_name =
	      match BU.smap_try_find (sigmap env) new_name.str with
	      | None -> None
	      | Some (s, _) ->
	        begin match s.sigel with
                | Sig_new_effect_for_free (ne)
		| Sig_new_effect(ne)
		  -> Some (set_lid_range ne.mname (range_of_lid l))
		| Sig_effect_abbrev (_, _, _, cmp, _) ->
                  let l'' = U.comp_effect_name cmp in
		  aux l''
	        | _ -> None
		end
	  in aux l'
	| Some (_, l') -> Some l'
	| _ -> None

let lookup_letbinding_quals env lid =
  let k_global_def lid = function
      | ({sigel = Sig_declare_typ(_, _, _); sigquals=quals }, _) ->
          Some quals
      | _ ->
          None in
  match resolve_in_open_namespaces' env lid (fun _ -> None) (fun _ -> None) k_global_def with
    | Some quals -> quals
    | _ -> []

let try_lookup_module env path =
  match List.tryFind (fun (mlid, modul) -> path_of_lid mlid = path) env.modules with
    | Some (_, modul) -> Some modul
    | None -> None

let try_lookup_let env (lid:lident) =
  let k_global_def lid = function
      | ({ sigel = Sig_let((_, lbs), _, _) }, _) ->
        let fv = lb_fv lbs lid in
        Some (fvar lid fv.fv_delta fv.fv_qual)
      | _ -> None in
  resolve_in_open_namespaces' env lid (fun _ -> None) (fun _ -> None) k_global_def

let try_lookup_definition env (lid:lident) =
    let k_global_def lid = function
      | ({ sigel = Sig_let(lbs, _, _) }, _) ->
        BU.find_map (snd lbs) (fun lb ->
            match lb.lbname with
                | Inr fv when S.fv_eq_lid fv lid ->
                  Some (lb.lbdef)
                | _ -> None)
      | _ -> None in
  resolve_in_open_namespaces' env lid (fun _ -> None) (fun _ -> None) k_global_def


let empty_include_smap : BU.smap<(ref<(list<lident>)>)> = new_sigmap()
let empty_exported_id_smap : BU.smap<exported_id_set> = new_sigmap()

let try_lookup_lid' any_val exclude_interf env (lid:lident) : option<(term * bool)> =
  match try_lookup_name any_val exclude_interf env lid with
    | Some (Term_name (e, mut)) -> Some (e, mut)
    | _ -> None
let try_lookup_lid (env:env) l = try_lookup_lid' env.iface false env l
let resolve_to_fully_qualified_name (env:env) (l:lident) =
    match try_lookup_lid env l with
    | None -> None
    | Some (e, _) ->
      match (Subst.compress e).n with
      | Tm_fvar fv -> Some fv.fv_name.v
      | _ -> None

let try_lookup_lid_no_resolve (env: env) l =
  let env' = {env with scope_mods = [] ; exported_ids=empty_exported_id_smap; includes=empty_include_smap }
  in
  try_lookup_lid env' l

let try_lookup_doc (env: env) (l:lid) =
  BU.smap_try_find env.docs l.str

let try_lookup_datacon env (lid:lident) =
  let k_global_def lid = function
      | ({ sigel = Sig_declare_typ(_, _, _); sigquals = quals }, _) ->
        if quals |> BU.for_some (function Assumption -> true | _ -> false)
        then Some (lid_as_fv lid Delta_constant None)
        else None
      | ({ sigel = Sig_datacon _ }, _) -> Some (lid_as_fv lid Delta_constant (Some Data_ctor))
      | _ -> None in
  resolve_in_open_namespaces' env lid (fun _ -> None) (fun _ -> None) k_global_def

let find_all_datacons env (lid:lident) =
  let k_global_def lid = function
      | ({ sigel = Sig_inductive_typ(_, _, _, _, datas, _) }, _) -> Some datas
      | _ -> None in
  resolve_in_open_namespaces' env lid (fun _ -> None) (fun _ -> None) k_global_def

//no top-level pattern in F*, so need to do this ugliness
let record_cache_aux_with_filter =
    let record_cache : ref<list<list<record_or_dc>>> = BU.mk_ref [[]] in
    let push () =
        record_cache := List.hd !record_cache::!record_cache in
    let pop () =
        record_cache := List.tl !record_cache in
    let peek () = List.hd !record_cache in
    let insert r = record_cache := (r::peek())::List.tl (!record_cache) in
    let commit () = match !record_cache with
        | hd::_::tl -> record_cache := hd::tl
        | _ -> failwith "Impossible" in
    (* remove private/abstract records *)
    let filter () =
        let rc = peek () in
        let () = pop () in
        let filtered = List.filter (fun r -> not r.is_private_or_abstract) rc in
        record_cache := filtered :: !record_cache
    in
    let aux =
    (push, pop, peek, insert, commit)
    in (aux, filter)

let record_cache_aux =
    let (aux, _) = record_cache_aux_with_filter in aux

let filter_record_cache =
    let (_, filter) = record_cache_aux_with_filter in filter

let push_record_cache =
    let push, _, _, _, _ = record_cache_aux in
    push

let pop_record_cache =
    let _, pop, _, _, _ = record_cache_aux in
    pop

let peek_record_cache =
    let _, _, peek, _, _ = record_cache_aux in
    peek

let insert_record_cache =
    let _, _, _, insert, _ = record_cache_aux in
    insert

let commit_record_cache =
    let _, _, _, _, commit = record_cache_aux in
    commit

let extract_record (e:env) (new_globs: ref<(list<scope_mod>)>) = fun se -> match se.sigel with
  | Sig_bundle(sigs, _) ->
    let is_record = BU.for_some (function
      | RecordType _
      | RecordConstructor _ -> true
      | _ -> false) in

    let find_dc dc =
      sigs |> BU.find_opt (function
        | { sigel = Sig_datacon(lid, _, _, _, _, _) } -> lid_equals dc lid
        | _ -> false) in

    sigs |> List.iter (function
      | { sigel = Sig_inductive_typ(typename, univs, parms, _, _, [dc]); sigquals = typename_quals } ->
        begin match must <| find_dc dc with
            | { sigel = Sig_datacon(constrname, _, t, _, _, _) } ->
                let formals, _ = U.arrow_formals t in
                let is_rec = is_record typename_quals in
                let formals' = formals |> List.collect (fun (x,q) ->
                        if S.is_null_bv x
                        || (is_rec && S.is_implicit q)
                        then []
                        else [(x,q)] )
                in
                let fields' = formals' |> List.map (fun (x,q) -> ((if is_rec then U.unmangle_field_name x.ppname else x.ppname), x.sort))
                in
                let fields = fields'
                in
                let record = {typename=typename;
                              constrname=constrname.ident;
                              parms=parms;
                              fields=fields;
                              is_private_or_abstract =
                                List.contains Private typename_quals ||
                                List.contains Abstract typename_quals;
                              is_record=is_rec} in
                (* the record is added to the current list of
                top-level definitions, to allow shadowing field names
                that were reachable through previous "open"s. *)
                let () = new_globs := Record_or_dc record :: !new_globs in
                (* the field names are added into the set of exported fields for "include" *)
                let () =
                  let add_field (id, _) =
                    let modul = (lid_of_ids constrname.ns).str in
                    match get_exported_id_set e modul with
                    | Some my_ex ->
                      let my_exported_ids = my_ex Exported_id_field in
                      let () = my_exported_ids := BU.set_add id.idText !my_exported_ids in
                      (* also add the projector name *)
                      let projname = (mk_field_projector_name_from_ident constrname id).ident.idText in
                      let () = my_exported_ids := BU.set_add projname !my_exported_ids in
                      ()
                    | None -> () (* current module was not prepared? should not happen *)
                  in
                  List.iter add_field fields'
                in
                insert_record_cache record
            | _ -> ()
        end
      | _ -> ())

  | _ -> ()

let try_lookup_record_or_dc_by_field_name env (fieldname:lident) =
  let find_in_cache fieldname =
//BU.print_string (BU.format1 "Trying field %s\n" fieldname.str);
    let ns, id = fieldname.ns, fieldname.ident in
    BU.find_map (peek_record_cache()) (fun record ->
      option_of_cont (fun _ -> None) (find_in_record ns id record (fun r -> Cont_ok r))
    ) in
  resolve_in_open_namespaces'' env fieldname Exported_id_field (fun _ -> Cont_ignore) (fun _ -> Cont_ignore) (fun r -> Cont_ok r)  (fun fn -> cont_of_option Cont_ignore (find_in_cache fn)) (fun k _ -> k)

let try_lookup_record_by_field_name env (fieldname:lident) =
    match try_lookup_record_or_dc_by_field_name env fieldname with
        | Some r when r.is_record -> Some r
        | _ -> None

let belongs_to_record env lid record =
    (* first determine whether lid is a valid record field name, and
    that it resolves to a record' type in the same module as record
    (even though the record types may be different.) *)
    match try_lookup_record_by_field_name env lid with
    | Some record'
      when text_of_path (path_of_ns record.typename.ns)
         = text_of_path (path_of_ns record'.typename.ns)
      ->
      (* now, check whether field belongs to record *)
      begin match find_in_record record.typename.ns lid.ident record (fun _ -> Cont_ok ()) with
      | Cont_ok _ -> true
      | _ -> false
      end
    | _ -> false

let try_lookup_dc_by_field_name env (fieldname:lident) =
    match try_lookup_record_or_dc_by_field_name env fieldname with
        | Some r -> Some (set_lid_range (lid_of_ids (r.typename.ns @ [r.constrname])) (range_of_lid fieldname), r.is_record)
        | _ -> None

let string_set_ref_new () = BU.mk_ref (BU.new_set BU.compare BU.hashcode)
let exported_id_set_new () =
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    function
    | Exported_id_term_type -> term_type_set
    | Exported_id_field -> field_set

let unique any_val exclude_if env lid =
  (* Disable name resolution altogether, thus lid is assumed to be fully qualified *)
  let filter_scope_mods = function
    | Rec_binding _
        -> true
    | _ -> false
  in
  let this_env = {env with scope_mods = List.filter filter_scope_mods env.scope_mods; exported_ids=empty_exported_id_smap; includes=empty_include_smap } in
  match try_lookup_lid' any_val exclude_if this_env lid with
    | None -> true
    | Some _ -> false

let push_scope_mod env scope_mod =
 {env with scope_mods = scope_mod :: env.scope_mods}

let push_bv' env (x:ident) is_mutable =
  let bv = S.gen_bv x.idText (Some x.idRange) tun in
  push_scope_mod env (Local_binding (x, bv, is_mutable)), bv

let push_bv_mutable env x =
  push_bv' env x true

let push_bv env x =
  push_bv' env x false

let push_top_level_rec_binding env (x:ident) dd =
  let l = qualify env x in
  if unique false true env l || Options.interactive ()
  then push_scope_mod env (Rec_binding (x,l,dd))
  else raise (Error ("Duplicate top-level names " ^ l.str, range_of_lid l))

let push_sigelt env s =
  let err l =
    let sopt = BU.smap_try_find (sigmap env) l.str in
    let r = match sopt with
      | Some (se, _) ->
        begin match BU.find_opt (lid_equals l) (lids_of_sigelt se) with
          | Some l -> Range.string_of_range <| range_of_lid l
          | None -> "<unknown>"
        end
      | None -> "<unknown>" in
    raise (Error (BU.format2 "Duplicate top-level names [%s]; previously declared at %s" (text_of_lid l) r, range_of_lid l)) in
  let globals = BU.mk_ref env.scope_mods in
  let env =
      let any_val, exclude_if = match s.sigel with
        | Sig_let _ -> false, true
        | Sig_bundle _ -> true, true
        | _ -> false, false in
      let lids = lids_of_sigelt s in
      begin match BU.find_map lids (fun l -> if not (unique any_val exclude_if env l) then Some l else None) with
        | Some l when not (Options.interactive ()) -> err l
        | _ -> extract_record env globals s; {env with sigaccum=s::env.sigaccum}
      end in
  let env = {env with scope_mods = !globals} in
  let env, lss = match s.sigel with
    | Sig_bundle(ses, _) -> env, List.map (fun se -> (lids_of_sigelt se, se)) ses
    | _ -> env, [lids_of_sigelt s, s] in
  lss |> List.iter (fun (lids, se) ->
    lids |> List.iter (fun lid ->
      (* the identifier is added into the list of global
      declarations, to allow shadowing of definitions that were
      formerly reachable by previous "open"s. *)
      let () = globals := Top_level_def lid.ident :: !globals in
      (* the identifier is added into the list of global identifiers
         of the corresponding module to shadow any "include" *)
      let modul = (lid_of_ids lid.ns).str in
      let () = match get_exported_id_set env modul with
      | Some f ->
        let my_exported_ids = f Exported_id_term_type in
        my_exported_ids := BU.set_add lid.ident.idText !my_exported_ids
      | None -> () (* current module was not prepared? should not happen *)
      in
      BU.smap_add (sigmap env) lid.str (se, env.iface && not env.admitted_iface)));
  let env = {env with scope_mods = !globals } in
  env

let push_namespace env ns =
  (* namespace resolution disabled, but module abbrevs enabled *)
  let (ns', kd) = match resolve_module_name env ns false with
  | None ->
     let modules = env.modules in
     if modules |> BU.for_some (fun (m, _) ->
      BU.starts_with (Ident.text_of_lid m ^ ".") (Ident.text_of_lid ns ^ "."))
     then (ns, Open_namespace)
     else raise (Error(BU.format1 "Namespace %s cannot be found" (Ident.text_of_lid ns), Ident.range_of_lid ns))
  | Some ns' ->
     let _ = fail_if_curmodule env ns ns' in
     (ns', Open_module)
  in
     push_scope_mod env (Open_module_or_namespace (ns', kd))

let push_include env ns =
    (* similarly to push_namespace in the case of modules, we allow
       module abbrevs, but not namespace resolution *)
    let ns0 = ns in
    match resolve_module_name env ns false with
    | Some ns ->
      let _ = fail_if_curmodule env ns0 ns in
      (* from within the current module, include is equivalent to open *)
      let env = push_scope_mod env (Open_module_or_namespace (ns, Open_module)) in
      (* update the list of includes *)
      let curmod = (current_module env).str in
      let () = match BU.smap_try_find env.includes curmod with
      | None -> ()
      | Some incl -> incl := ns :: !incl
      in
      (* the names of the included module and its transitively
         included modules shadow the names of the current module *)
      begin match get_trans_exported_id_set env ns.str with
      | Some ns_trans_exports ->
        let () = match (get_exported_id_set env curmod, get_trans_exported_id_set env curmod) with
        | (Some cur_exports, Some cur_trans_exports) ->
          let update_exports (k: exported_id_kind) =
            let ns_ex = ! (ns_trans_exports k) in
            let ex = cur_exports k in
            let () = ex := BU.set_difference (!ex) ns_ex in
            let trans_ex = cur_trans_exports k in
            let () = trans_ex := BU.set_union (!trans_ex) ns_ex in
            ()
          in
          List.iter update_exports all_exported_id_kinds
        | _ -> () (* current module was not prepared? should not happen *)
        in
        env
      | None ->
        (* module to be included was not prepared, so forbid the 'include'. It may be the case for modules such as FStar.ST, etc. *)
        raise (Error (BU.format1 "include: Module %s was not prepared" ns.str, Ident.range_of_lid ns))
      end
    | _ ->
      raise (Error (BU.format1 "include: Module %s cannot be found" ns.str, Ident.range_of_lid ns))

let push_module_abbrev env x l =
  (* both namespace resolution and module abbrevs disabled:
     in 'module A = B', B must be fully qualified *)
  if module_is_defined env l
  then let _ = fail_if_curmodule env l l in
       push_scope_mod env (Module_abbrev (x,l))
  else raise (Error(BU.format1 "Module %s cannot be found" (Ident.text_of_lid l), Ident.range_of_lid l))

let push_doc env (l:lid) (doc_opt:option<Parser.AST.fsdoc>) =
  match doc_opt with
  | None -> env
  | Some doc ->
    (match BU.smap_try_find env.docs l.str with
     | None -> ()
     | Some old_doc -> FStar.Errors.warn (range_of_lid l)
                        (BU.format3 "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                           (Ident.string_of_lid l) (Parser.AST.string_of_fsdoc old_doc)
                           (Parser.AST.string_of_fsdoc doc)));
    BU.smap_add env.docs l.str doc;
    env

let check_admits env =
  env.sigaccum |> List.iter (fun se -> match se.sigel with
    | Sig_declare_typ(l, u, t) ->
      begin match try_lookup_lid env l with
        | None ->
          if not (Options.interactive ()) then
            BU.print_string (BU.format2 "%s: Warning: Admitting %s without a definition\n" (Range.string_of_range (range_of_lid l)) (Print.lid_to_string l));
          let quals = Assumption :: se.sigquals in
          BU.smap_add (sigmap env) l.str ({ se with sigquals = quals },
                                          false)
        | Some _ -> ()
      end
    | _ -> ())

let finish env modul =
  modul.declarations |> List.iter (fun se ->
    let quals = se.sigquals in
    match se.sigel with
    | Sig_bundle(ses, _) ->
      if List.contains Private quals
      || List.contains Abstract quals
      then ses |> List.iter (fun se -> match se.sigel with
                | Sig_datacon(lid, _, _, _, _, _) -> BU.smap_remove (sigmap env) lid.str
                | _ -> ())

    | Sig_declare_typ(lid, _, _) ->
      if List.contains Private quals
      then BU.smap_remove (sigmap env) lid.str

    | Sig_let((_,lbs), _, _) ->
      if List.contains Private quals
      || List.contains Abstract quals
      then begin
           lbs |> List.iter (fun lb -> BU.smap_remove (sigmap env) (right lb.lbname).fv_name.v.str)
      end;
      if List.contains Abstract quals
      && not (List.contains Private quals)
      then lbs |> List.iter (fun lb ->
           let lid = (right lb.lbname).fv_name.v in
           let quals = Assumption :: quals in
           let decl = { se with sigel = Sig_declare_typ(lid, lb.lbunivs, lb.lbtyp);
                                sigquals = quals } in
           BU.smap_add (sigmap env) lid.str (decl, false))

    | _ -> ());
  (* update the sets of transitively exported names of this module by
     adding the unshadowed names defined only in the current module. *)
  let curmod = (current_module env).str in
  let () = match (get_exported_id_set env curmod, get_trans_exported_id_set env curmod) with
    | (Some cur_ex, Some cur_trans_ex) ->
      let update_exports eikind =
        let cur_ex_set = ! (cur_ex eikind) in
        let cur_trans_ex_set_ref = cur_trans_ex eikind in
        cur_trans_ex_set_ref := BU.set_union cur_ex_set (!cur_trans_ex_set_ref)
       in
       List.iter update_exports all_exported_id_kinds
    | _ -> ()
  in
  (* remove abstract/private records *)
  let () = filter_record_cache () in
  {env with
    curmodule=None;
    modules=(modul.name, modul)::env.modules;
    scope_mods = [];
    sigaccum=[];
  }

let stack: ref<(list<env>)> = BU.mk_ref []
let push env =
  push_record_cache();
  stack := env::!stack;
  {env with sigmap=BU.smap_copy (sigmap env); docs=BU.smap_copy env.docs}

let pop () =
  match !stack with
  | env::tl ->
    pop_record_cache();
    stack := tl;
    env
  | _ -> failwith "Impossible: Too many pops"

let commit_mark (env: env) =
  commit_record_cache();
  match !stack with
  | _::tl ->
    stack := tl;
    env
  | _ -> failwith "Impossible: Too many pops"

let mark x = push x
let reset_mark () = pop ()

let export_interface (m:lident) env =
//    printfn "Exporting interface %s" m.str;
    let sigelt_in_m se =
        match U.lids_of_sigelt se with
            | l::_ -> l.nsstr=m.str
            | _ -> false in
    let sm = sigmap env in
    let env = pop () in
    let keys = BU.smap_keys sm in
    let sm' = sigmap env in
    keys |> List.iter (fun k ->
    match BU.smap_try_find sm' k with
        | Some (se, true) when sigelt_in_m se ->
          BU.smap_remove sm' k;
//          printfn "Exporting %s" k;
          let se = match se.sigel with
            | Sig_declare_typ(l, u, t) ->
              { se with sigquals = Assumption::se.sigquals }
            | _ -> se in
          BU.smap_add sm' k (se, false)
        | _ -> ());
    env

let finish_module_or_interface env modul =
  if not modul.is_interface
  then check_admits env;
  finish env modul

let prepare_module_or_interface intf admitted env mname = (* AR: open the pervasives namespace *)
  let prep env =
    (* These automatically-prepended directives must be kept in sync with [dep.fs]. *)
    let open_ns =
      if lid_equals mname Const.prims_lid then
        []
      else if starts_with "FStar." (text_of_lid mname) then
        [ Const.prims_lid; Const.pervasives_lid; Const.fstar_ns_lid ]
      else
        [ Const.prims_lid; Const.pervasives_lid; Const.st_lid; Const.all_lid; Const.fstar_ns_lid ]
    in
    let open_ns =
      // JP: auto-deps is not aware of that. Fix it once [universes] is the default.
      if List.length mname.ns <> 0
      then let ns = Ident.lid_of_ids mname.ns in
           ns::open_ns //the namespace of the current module, if any, is implicitly in scope
      else open_ns in
    (* Create new empty set of exported identifiers for the current module, for 'include' *)
    let () = BU.smap_add env.exported_ids mname.str (exported_id_set_new ()) in
    (* Create new empty set of transitively exported identifiers for the current module, for 'include' *)
    let () = BU.smap_add env.trans_exported_ids mname.str (exported_id_set_new ()) in
    (* Create new empty list of includes for the current module *)
    let () = BU.smap_add env.includes mname.str (BU.mk_ref []) in
    {
      env with curmodule=Some mname;
      sigmap=env.sigmap;
      scope_mods = List.map (fun lid -> Open_module_or_namespace (lid, Open_namespace)) open_ns;
      iface=intf;
      admitted_iface=admitted }
  in

  match env.modules |> BU.find_opt (fun (l, _) -> lid_equals l mname) with
    | None ->
        prep env, false
    | Some (_, m) ->
        if not (Options.interactive ()) && (not m.is_interface || intf)
        then raise (Error(BU.format1 "Duplicate module or interface name: %s" mname.str, range_of_lid mname));
        //we have an interface for this module already; if we're not interactive then do not export any symbols from this module
        prep (push env), true //push a context so that we can pop it when we're done

let enter_monad_scope env mname =
  match env.curmonad with
  | Some mname' -> raise (Error ("Trying to define monad " ^ mname.idText ^ ", but already in monad scope " ^ mname'.idText, mname.idRange))
  | None -> {env with curmonad = Some mname}

let fail_or env lookup lid = match lookup lid with
  | None ->
    let opened_modules = List.map (fun (lid, _) -> text_of_lid lid) env.modules in
    let msg = BU.format1 "Identifier not found: [%s]" (text_of_lid lid) in
    let msg =
      if List.length lid.ns = 0
      then
       msg
      else
       let modul = set_lid_range (lid_of_ids lid.ns) (range_of_lid lid) in
       match resolve_module_name env modul true with
       | None ->
           let opened_modules = String.concat ", " opened_modules in
           BU.format3
           "%s\nModule %s does not belong to the list of modules in scope, namely %s"
           msg
           modul.str
           opened_modules
       | Some modul' when (not (List.existsb (fun m -> m = modul'.str) opened_modules)) ->
           let opened_modules = String.concat ", " opened_modules in
           BU.format4
           "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s"
           msg
           modul.str
           modul'.str
           opened_modules
       | Some modul' ->
           BU.format4
           "%s\nModule %s resolved into %s, definition %s not found"
           msg
           modul.str
           modul'.str
           lid.ident.idText
    in
    raise (Error (msg, range_of_lid lid))
  | Some r -> r

let fail_or2 lookup id = match lookup id with
  | None -> raise (Error ("Identifier not found [" ^id.idText^"]", id.idRange))
  | Some r -> r
