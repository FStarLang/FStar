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

module FStar.Parser.Env


open FStar
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Util
open FStar.Syntax.Const
open FStar.Parser
open FStar.Ident

module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util

type local_binding = (ident * bv * bool)                  (* local name binding for name resolution, paired with an env-generated unique name and a boolean that is true when the variable has been introduced with let-mutable *)
type rec_binding   = (ident * lid * delta_depth)          (* name bound by recursive type and top-level let-bindings definitions only *)
type module_abbrev = (ident * lident)                     (* module X = A.B.C, where A.B.C is fully qualified and already resolved *)

type open_kind =                                          (* matters only for resolving names with some module qualifier *)
| Open_module                                             (* only opens the module, not the namespace *)
| Open_namespace                                          (* opens the whole namespace *)

type open_module_or_namespace = (lident * open_kind)      (* lident fully qualified name, already resolved. *)

type record_or_dc = {
  typename: lident;
  constrname: lident;
  parms: binders;
  fields: list<(fieldname * typ)>;
  is_record:bool
}

type scope_mod =
| Local_binding            of local_binding
| Rec_binding              of rec_binding
| Module_abbrev            of module_abbrev
| Open_module_or_namespace of open_module_or_namespace
| Top_level_def            of ident           (* top-level definition for an unqualified identifier x to be resolved as curmodule.x. *)
| Record_or_dc             of record_or_dc    (* to honor interleavings of "open" and record definitions *)

type env = {
  curmodule:            option<lident>;                   (* name of the module being desugared *)
  curmonad:             option<ident>;                    (* current monad being desugared *)
  modules:              list<(lident * modul)>;           (* previously desugared modules *)
  scope_mods:           list<scope_mod>;                  (* toplevel or definition-local scope modifiers *)
  sigaccum:             sigelts;                          (* type declarations being accumulated for the current module *)
  sigmap:               Util.smap<(sigelt * bool)>;       (* bool indicates that this was declared in an interface file *)
  default_result_effect:lident;                           (* either Tot or ML, depending on the what kind of term we're desugaring *)
  iface:                bool;                             (* remove? whether or not we're desugaring an interface; different scoping rules apply *)
  admitted_iface:       bool;                             (* is it an admitted interface; different scoping rules apply *)
  expect_typ:           bool;                             (* syntactically, expect a type at this position in the term *)
}

type foundname =
  | Term_name of typ * bool // indicates if mutable
  | Eff_name  of sigelt * lident

// VALS_HACK_HERE

let open_modules e = e.modules
let current_module env = match env.curmodule with
    | None -> failwith "Unset current module"
    | Some m -> m
let qual = qual_id
let qualify env id =
    match env.curmonad with
    | None -> qual (current_module env) id
    | Some monad -> mk_field_projector_name_from_ident (qual (current_module env) monad) id
let new_sigmap () = Util.smap_create 100
let empty_env () = {curmodule=None;
                    curmonad=None;
                    modules=[];
                    scope_mods=[];
                    sigaccum=[];
                    sigmap=new_sigmap();
                    default_result_effect=Const.effect_Tot_lid;
                    iface=false;
                    admitted_iface=false;
                    expect_typ=false}
let sigmap env = env.sigmap
let has_all_in_scope env =
  List.existsb (fun (m, _) ->
    lid_equals m Const.all_lid) env.modules

let default_total env = {env with default_result_effect=Const.effect_Tot_lid}
let default_ml env =
  if has_all_in_scope env then
    { env with default_result_effect=Const.effect_ML_lid }
  else
    env


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
      let needs_constrname = not (field_projector_contains_constructor id.idText) in
      let constrname = record.constrname.ident in
      let fname =
       if needs_constrname
       then mk_field_projector_name_from_ident (lid_of_ids (ns @ [constrname])) id
       else lid_of_ids (ns @ [id])
      in
      let fname = set_lid_range fname id.idRange in
      let find =
      Util.find_map record.fields (fun (f, _) ->
        if lid_equals fname f
        then Some(record, fname)
        else None)
      in
      match find with
      | Some r -> cont r
      | None -> Cont_ignore

let try_lookup_id''
  env
  (id: ident)
  (k_local_binding: local_binding -> cont_t<'a>)
  (k_rec_binding:   rec_binding   -> cont_t<'a>)
  (k_record: (record_or_dc * fieldname) -> cont_t<'a>)
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
        let lid = qual ns id in
        find_in_module lid

      | Top_level_def id'
        when id'.idText = id.idText ->
        (* indicates a global definition shadowing previous
        "open"s. If the definition is not actually found by the
        [lookup_default_id] finder, then it may mean that we are in a
        module and the [val] was already declared, with the actual
        [let] not defined yet, so we must not fail, but ignore. *)
        lookup_default_id Cont_ignore id

      | Record_or_dc r ->
        find_in_record curmod_ns id r k_record

      | _ ->
        Cont_ignore
    in
    let rec aux = function
      | a :: q ->
        option_of_cont (fun _ -> aux q) (proc a)
      | [] ->
        option_of_cont (fun _ -> None) (lookup_default_id Cont_fail id)

    in aux env.scope_mods

let found_local_binding (id', x, mut) =
    (bv_to_name x id'.idRange, mut)

let find_in_module env lid k_global_def k_not_found =
    begin match Util.smap_try_find (sigmap env) lid.str with
        | Some sb -> k_global_def lid sb
        | None -> k_not_found
    end

let try_lookup_id env (id:ident) =
  match unmangleOpName id with
  | Some f -> Some f
  | _ ->
    try_lookup_id'' env id (fun r -> Cont_ok (found_local_binding r)) (fun _ -> Cont_fail) (fun _ -> Cont_ignore) (fun i -> find_in_module env i (fun _ _ -> Cont_fail) Cont_ignore) (fun _ _ -> Cont_fail)

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
    begin match Util.smap_try_find (sigmap env) lid.str with
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
    lid_equals lid (current_module env) ||
    List.existsb (fun x -> lid_equals lid (fst x)) env.modules

let resolve_module_name env lid : option<lident> =
    let nslen = List.length lid.ns in
    let rec aux = function
        | [] ->
          if module_is_defined env lid
          then Some lid
          else None

        | Open_module_or_namespace (ns, Open_namespace) :: q ->
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

(* Generic name resolution. *)

let resolve_in_open_namespaces''
  env
  lid
  (k_local_binding: local_binding -> cont_t<'a>)
  (k_rec_binding:   rec_binding   -> cont_t<'a>)
  (k_record: (record_or_dc * fieldname) -> cont_t<'a>)
  (f_module: cont_t<'a> -> lident -> cont_t<'a>)
  (l_default: cont_t<'a> -> ident -> cont_t<'a>)
  : option<'a> =
  match lid.ns with
  | _ :: _ ->
    begin match resolve_module_name env (set_lid_range (lid_of_ids lid.ns) (range_of_lid lid)) with
    | None -> None
    | Some modul ->
        let lid' = qual modul lid.ident in
        option_of_cont (fun _ -> None) (f_module Cont_fail lid')
    end
  | [] ->
    try_lookup_id'' env lid.ident k_local_binding k_rec_binding k_record (f_module Cont_ignore) l_default

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
  let f_module k lid' = find_in_module env lid' (k_global_def' k) k in
  let l_default k i = lookup_default_id env i (k_global_def' k) k in
  resolve_in_open_namespaces'' env lid (fun l -> cont_of_option Cont_fail (k_local_binding l)) (fun r -> cont_of_option Cont_fail (k_rec_binding r)) (fun _ -> Cont_ignore) f_module l_default

let fv_qual_of_se = function
    | Sig_datacon(_, _, _, l, _, quals, _, _) ->
      let qopt = Util.find_map quals (function
          | RecordConstructor fs -> Some (Record_ctor(l, fs))
          | _ -> None) in
      begin match qopt with
        | None -> Some Data_ctor
        | x -> x
      end
    | Sig_declare_typ (_, _, _, quals, _) ->  //TODO: record projectors?
      None
    | _ -> None

let lb_fv lbs lid = 
     Util.find_map lbs  (fun lb -> 
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
        begin match se with
          | Sig_inductive_typ _ ->   Some (Term_name(S.fvar source_lid Delta_constant None, false))
          | Sig_datacon _ ->         Some (Term_name(S.fvar source_lid Delta_constant (fv_qual_of_se se), false))
          | Sig_let((_, lbs), _, _, _) ->
            let fv = lb_fv lbs source_lid in
            Some (Term_name(S.fvar source_lid fv.fv_delta fv.fv_qual, false))
          | Sig_declare_typ(lid, _, _, quals, _) ->
            if any_val //only in scope in an interface (any_val is true) or if the val is assumed
            || quals |> Util.for_some (function Assumption -> true | _ -> false)
            then let lid = Ident.set_lid_range lid (Ident.range_of_lid source_lid) in
                 let dd = if Util.is_primop_lid lid
                          || (ns_of_lid_equals lid FStar.Syntax.Const.prims_lid && quals |> Util.for_some (function Projector _ | Discriminator _ -> true | _ -> false))
                          then Delta_equational
                          else Delta_constant in
                 begin match Util.find_map quals (function Reflectable refl_monad -> Some refl_monad | _ -> None) with //this is really a M?.reflect
                 | Some refl_monad ->
                        let refl_const = S.mk (Tm_constant (FStar.Const.Const_reflect refl_monad)) None occurrence_range in
                        Some (Term_name (refl_const, false))
                 | _ -> Some (Term_name(fvar lid dd (fv_qual_of_se se), false))
                 end
            else None
          | Sig_new_effect_for_free (ne, _) | Sig_new_effect(ne, _) -> Some (Eff_name(se, set_lid_range ne.mname (range_of_lid source_lid)))
          | Sig_effect_abbrev _ ->   Some (Eff_name(se, source_lid))
          | _ -> None
        end in

  let k_local_binding r = Some (Term_name (found_local_binding r))
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
let try_lookup_effect_defn env l =
    match try_lookup_effect_name' (not env.iface) env l with
        | Some (Sig_new_effect(ne, _), _) -> Some ne
        | Some (Sig_new_effect_for_free(ne, _), _) -> Some ne
        | _ -> None
let is_effect_name env lid =
    match try_lookup_effect_name env lid with
        | None -> false
        | Some _ -> true

let lookup_letbinding_quals env lid =
  let k_global_def lid = function
      | (Sig_declare_typ(lid, _, _, quals, _), _) -> Some quals
      | _ -> None in
  match resolve_in_open_namespaces' env lid (fun _ -> None) (fun _ -> None) k_global_def with
    | Some quals -> quals
    | _ -> []

let try_lookup_module env path =
  match List.tryFind (fun (mlid, modul) -> path_of_lid mlid = path) env.modules with
    | Some (_, modul) -> Some modul
    | None -> None

let try_lookup_let env (lid:lident) =
  let k_global_def lid = function
      | (Sig_let((_, lbs), _, _, _), _) -> 
        let fv = lb_fv lbs lid in
        Some (fvar lid fv.fv_delta fv.fv_qual)
      | _ -> None in
  resolve_in_open_namespaces' env lid (fun _ -> None) (fun _ -> None) k_global_def

let try_lookup_definition env (lid:lident) = 
    let k_global_def lid = function
      | (Sig_let(lbs, _, _, _), _) ->
        Util.find_map (snd lbs) (fun lb -> 
            match lb.lbname with 
                | Inr fv when S.fv_eq_lid fv lid ->
                  Some (lb.lbdef)
                | _ -> None)
      | _ -> None in
  resolve_in_open_namespaces' env lid (fun _ -> None) (fun _ -> None) k_global_def


let try_lookup_lid' any_val exclude_interf env (lid:lident) : option<(term * bool)> =
  match try_lookup_name any_val exclude_interf env lid with
    | Some (Term_name (e, mut)) -> Some (e, mut)
    | _ -> None
let try_lookup_lid (env:env) l = try_lookup_lid' env.iface false env l

let try_lookup_datacon env (lid:lident) =
  let k_global_def lid = function
      | (Sig_declare_typ(_, _, _, quals, _), _) ->
        if quals |> Util.for_some (function Assumption -> true | _ -> false)
        then Some (lid_as_fv lid Delta_constant None)
        else None
      | (Sig_datacon _, _) -> Some (lid_as_fv lid Delta_constant (Some Data_ctor))
      | _ -> None in
  resolve_in_open_namespaces' env lid (fun _ -> None) (fun _ -> None) k_global_def

let find_all_datacons env (lid:lident) =
  let k_global_def lid = function
      | (Sig_inductive_typ(_, _, _, _, _, datas, _, _), _) -> Some datas
      | _ -> None in
  resolve_in_open_namespaces' env lid (fun _ -> None) (fun _ -> None) k_global_def

//no top-level pattern in F*, so need to do this ugliness
let record_cache_aux = 
    let record_cache : ref<list<list<record_or_dc>>> = Util.mk_ref [[]] in
    let push () =
        record_cache := List.hd !record_cache::!record_cache in
    let pop () = 
        record_cache := List.tl !record_cache in
    let peek () = List.hd !record_cache in
    let insert r = record_cache := (r::peek())::List.tl (!record_cache) in
    let commit () = match !record_cache with 
        | hd::_::tl -> record_cache := hd::tl
        | _ -> failwith "Impossible" in
    (push, pop, peek, insert, commit) 
    
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

let extract_record (e:env) (new_globs: ref<(list<scope_mod>)>) = function
  | Sig_bundle(sigs, _, _, _) ->
    let is_rec = Util.for_some (function
      | RecordType _
      | RecordConstructor _ -> true
      | _ -> false) in

    let find_dc dc =
      sigs |> Util.find_opt (function
        | Sig_datacon(lid, _, _, _, _, _, _, _) -> lid_equals dc lid
        | _ -> false) in

    sigs |> List.iter (function
      | Sig_inductive_typ(typename, univs, parms, _, _, [dc], tags, _) ->
        begin match must <| find_dc dc with
            | Sig_datacon(constrname, _, t, _, _, _, _, _) ->
                let formals, _ = U.arrow_formals t in
                let is_rec = is_rec tags in 
                let fields = formals |> List.collect (fun (x,q) ->
                        if S.is_null_bv x
                        || (is_rec && S.is_implicit q)
                        then []
                        else [(mk_field_projector_name_from_ident constrname (if is_rec then Util.unmangle_field_name x.ppname else x.ppname), x.sort)]) in
                let record = {typename=typename;
                              constrname=constrname;
                              parms=parms;
                              fields=fields;
                              is_record=is_rec} in
                (* the record is added to the current list of
                top-level definitions, to allow shadowing field names
                that were reachable through previous "open"s. *)
                let () = new_globs := Record_or_dc record :: !new_globs in
                insert_record_cache record
            | _ -> ()
        end
      | _ -> ())

  | _ -> ()

let try_lookup_record_or_dc_by_field_name env (fieldname:lident) =
  let needs_constrname = not (field_projector_contains_constructor fieldname.ident.idText) in
  let find_in_cache fieldname =
//Util.print_string (Util.format1 "Trying field %s\n" fieldname.str);
    let ns, id = fieldname.ns, fieldname.ident in
    Util.find_map (peek_record_cache()) (fun record ->
      option_of_cont (fun _ -> None) (find_in_record ns id record (fun r -> Cont_ok r))
    ) in
  resolve_in_open_namespaces'' env fieldname (fun _ -> Cont_ignore) (fun _ -> Cont_ignore) (fun r -> Cont_ok r)  (fun k fn -> cont_of_option k (find_in_cache fn)) (fun k _ -> k)

let try_lookup_record_by_field_name env (fieldname:lident) =
    match try_lookup_record_or_dc_by_field_name env fieldname with 
        | Some (r, f) when r.is_record -> Some (r,f)
        | _ -> None

let try_lookup_projector_by_field_name env (fieldname:lident) = 
    match try_lookup_record_or_dc_by_field_name env fieldname with 
        | Some (r, f) -> Some (f, r.is_record)
        | _ -> None

let qualify_field_to_record env (recd:record_or_dc) (f:lident) =
  let qualify fieldname =
    let ns, fieldname = fieldname.ns, fieldname.ident in
    let constrname = recd.constrname.ident in
    let fname = mk_field_projector_name_from_ident (lid_of_ids (ns @ [constrname])) fieldname in
    Util.find_map recd.fields (fun (f, _) ->
      if lid_equals fname f
      then Some(fname)
      else None) in
  resolve_in_open_namespaces'' env f (fun _ -> Cont_ignore) (fun _ -> Cont_ignore) (fun r -> Cont_ok (snd r)) (fun k fn -> cont_of_option k (qualify fn)) (fun k _ -> k)

let unique any_val exclude_if env lid =
  let this_env = {env with scope_mods=[]} in
  match try_lookup_lid' any_val exclude_if env lid with
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
  if unique false true env l
  then push_scope_mod env (Rec_binding (x,l,dd))
  else raise (Error ("Duplicate top-level names " ^ l.str, range_of_lid l))

let push_sigelt env s =
  let err l =
    let sopt = Util.smap_try_find (sigmap env) l.str in
    let r = match sopt with
      | Some (se, _) ->
        begin match Util.find_opt (lid_equals l) (lids_of_sigelt se) with
          | Some l -> Range.string_of_range <| range_of_lid l
          | None -> "<unknown>"
        end
      | None -> "<unknown>" in
    raise (Error (Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (text_of_lid l) r, range_of_lid l)) in
  let globals = ref env.scope_mods in
  let env =
      let any_val, exclude_if = match s with
        | Sig_let _ -> false, true
        | Sig_bundle _ -> true, true
        | _ -> false, false in
      let lids = lids_of_sigelt s in
      begin match Util.find_map lids (fun l -> if not (unique any_val exclude_if env l) then Some l else None) with
        | None -> extract_record env globals s; {env with sigaccum=s::env.sigaccum}
        | Some l -> err l
      end in
  let env = {env with scope_mods = !globals} in
  let env, lss = match s with
    | Sig_bundle(ses, _, _, _) -> env, List.map (fun se -> (lids_of_sigelt se, se)) ses
    | _ -> env, [lids_of_sigelt s, s] in
  lss |> List.iter (fun (lids, se) ->
    lids |> List.iter (fun lid ->
      (* the identifier is added into the list of global
      declarations, to allow shadowing of definitions that were
      formerly reachable by previous "open"s. *)
      let () = globals := Top_level_def lid.ident :: !globals in
      Util.smap_add (sigmap env) lid.str (se, env.iface && not env.admitted_iface)));
  let env = {env with scope_mods = !globals } in
  env

let push_namespace env ns =
  let (ns', kd) = match resolve_module_name env ns with (* NOTE: can be replaced with "module_is_defined", to disable module name resolution *)
  | None ->
     let modules = env.modules in
     if modules |> Util.for_some (fun (m, _) ->
      Util.starts_with (Ident.text_of_lid m ^ ".") (Ident.text_of_lid ns ^ "."))
     then (ns, Open_namespace)
     else raise (Error(Util.format1 "Namespace %s cannot be found" (Ident.text_of_lid ns), Ident.range_of_lid ns))
  | Some ns' ->
     (ns', Open_module)
  in
     push_scope_mod env (Open_module_or_namespace (ns', kd))

let push_module_abbrev env x l =
  match resolve_module_name env l with (* NOTE: can be replaced with "module_is_defined", to disable module name resolution *)
  | None -> raise (Error(Util.format1 "Module %s cannot be found" (Ident.text_of_lid l), Ident.range_of_lid l))
  | Some modul -> push_scope_mod env (Module_abbrev (x,modul))

let check_admits env =
  env.sigaccum |> List.iter (fun se -> match se with
    | Sig_declare_typ(l, u, t, quals, r) ->
      begin match try_lookup_lid env l with
        | None ->
          Util.print_string (Util.format2 "%s: Warning: Admitting %s without a definition\n" (Range.string_of_range (range_of_lid l)) (Print.lid_to_string l));
          Util.smap_add (sigmap env) l.str (Sig_declare_typ(l, u, t, Assumption::quals, r), false)
        | Some _ -> ()
      end
    | _ -> ())

let finish env modul =
  modul.declarations |> List.iter (function
    | Sig_bundle(ses, quals, _, _) ->
      if List.contains Private quals
      || List.contains Abstract quals
      then ses |> List.iter (function
                | Sig_datacon(lid, _, _, _, _, _, _, _) -> Util.smap_remove (sigmap env) lid.str
                | _ -> ())

    | Sig_declare_typ(lid, _, _, quals, _) ->
      if List.contains Private quals
      then Util.smap_remove (sigmap env) lid.str
    
    | Sig_let((_,lbs), r, _, quals) ->
      if List.contains Private quals
      || List.contains Abstract quals
      then begin
           lbs |> List.iter (fun lb -> Util.smap_remove (sigmap env) (right lb.lbname).fv_name.v.str)
      end;
      if List.contains Abstract quals
      && not (List.contains Private quals)
      then lbs |> List.iter (fun lb -> 
           let lid = (right lb.lbname).fv_name.v in
           let decl = Sig_declare_typ(lid, lb.lbunivs, lb.lbtyp, Assumption::quals, r) in
           Util.smap_add (sigmap env) lid.str (decl, false))

    | _ -> ());
  {env with
    curmodule=None;
    modules=(modul.name, modul)::env.modules;
    scope_mods = [];
    sigaccum=[];
  }

type env_stack_ops = { 
    push: env -> env;
    mark: env -> env;
    reset_mark: env -> env;
    commit_mark: env -> env;
    pop:env -> env
}

let stack_ops = 
    let stack = Util.mk_ref [] in 
    let push env = 
        push_record_cache();
        stack := env::!stack;
        {env with sigmap=Util.smap_copy (sigmap env)} in
    let pop env = match !stack with 
        | env::tl -> 
         pop_record_cache();
         stack := tl;
         env
        | _ -> failwith "Impossible: Too many pops" in
    let commit_mark env = 
        commit_record_cache();
        match !stack with 
         | _::tl -> stack := tl; env
         | _ -> failwith "Impossible: Too many pops" in
    { push=push; 
      pop=pop;
      mark=push;
      reset_mark=pop;
      commit_mark=commit_mark;}

let push (env:env) = stack_ops.push env
let mark env = stack_ops.mark env
let reset_mark env = stack_ops.reset_mark env
let commit_mark env = stack_ops.commit_mark env
let pop env = stack_ops.pop env

let export_interface (m:lident) env =
//    printfn "Exporting interface %s" m.str;
    let sigelt_in_m se = 
        match Util.lids_of_sigelt se with 
            | l::_ -> l.nsstr=m.str
            | _ -> false in
    let sm = sigmap env in 
    let env = pop env in 
    let keys = Util.smap_keys sm in
    let sm' = sigmap env in 
    keys |> List.iter (fun k ->
    match Util.smap_try_find sm' k with 
        | Some (se, true) when sigelt_in_m se ->  
          Util.smap_remove sm' k;
//          printfn "Exporting %s" k;
          let se = match se with 
            | Sig_declare_typ(l, u, t, q, r) -> Sig_declare_typ(l, u, t, Assumption::q, r)
            | _ -> se in 
          Util.smap_add sm' k (se, false)
        | _ -> ());
    env

let finish_module_or_interface env modul =
  if not modul.is_interface
  then check_admits env;
  finish env modul

let prepare_module_or_interface intf admitted env mname =
  let prep env =
    (* These automatically-prepended directives must be kept in sync with [dep.fs]. *)
    let open_ns =
      if lid_equals mname Const.prims_lid then
        []
      else if starts_with "FStar." (text_of_lid mname) then
        [ Const.prims_lid; Const.fstar_ns_lid ]
      else
        [ Const.prims_lid; Const.st_lid; Const.all_lid; Const.fstar_ns_lid ]
    in
    let open_ns =
      // JP: auto-deps is not aware of that. Fix it once [universes] is the default.
      if List.length mname.ns <> 0
      then let ns = Ident.lid_of_ids mname.ns in
           ns::open_ns //the namespace of the current module, if any, is implicitly in scope
      else open_ns in
    {
      env with curmodule=Some mname;
      sigmap=env.sigmap;
      scope_mods = List.map (fun lid -> Open_module_or_namespace (lid, Open_namespace)) open_ns;
      iface=intf;
      admitted_iface=admitted;
      default_result_effect=
        (if lid_equals mname Const.all_lid || has_all_in_scope env
         then Const.effect_ML_lid
         else Const.effect_Tot_lid) } in

  match env.modules |> Util.find_opt (fun (l, _) -> lid_equals l mname) with
    | None -> prep env, false
    | Some (_, m) ->
      if not m.is_interface || intf
      then raise (Error(Util.format1 "Duplicate module or interface name: %s" mname.str, range_of_lid mname));
      //we have an interface for this module already; if we're not interactive then do not export any symbols from this module
      prep (push env), true //push a context so that we can pop it when we're done
      
let enter_monad_scope env mname =
  match env.curmonad with
  | Some mname' -> raise (Error ("Trying to define monad " ^ mname.idText ^ ", but already in monad scope " ^ mname'.idText, mname.idRange))
  | None -> {env with curmonad = Some mname}

let fail_or env lookup lid = match lookup lid with
  | None ->
    let opened_modules = List.map (fun (lid, _) -> text_of_lid lid) env.modules in
    let msg = Util.format1 "Identifier not found: [%s]" (text_of_lid lid) in
    let msg =
      if List.length lid.ns = 0
      then
       msg
      else
       let modul = set_lid_range (lid_of_ids lid.ns) (range_of_lid lid) in
       match resolve_module_name env modul with
       | None ->
           let opened_modules = String.concat ", " opened_modules in
           Util.format3
           "%s\nModule %s does not belong to the list of modules in scope, namely %s"
           msg
           modul.str
           opened_modules
       | Some modul' when (not (List.existsb (fun m -> m = modul'.str) opened_modules)) ->
           let opened_modules = String.concat ", " opened_modules in
           Util.format4
           "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s"
           msg
           modul.str
           modul'.str
           opened_modules
       | Some modul' ->
           Util.format4
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
