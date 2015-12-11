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

module FStar.Parser.DesugarEnv


open FStar
open FStar.Util
open FStar.Absyn
open FStar.Absyn.Syntax
open FStar.Absyn.Util
open FStar.Absyn.Const
open FStar.Parser

type binding =
  | Binding_typ_var of ident
  | Binding_var of ident
  | Binding_let of lident
  | Binding_tycon of lident

type kind_abbrev = lident * list<either<btvdef, bvvdef>> * Syntax.knd
type env = {
  curmodule: option<lident>;
  modules:list<(lident * modul)>;  (* previously desugared modules *)
  open_namespaces: list<lident>; (* fully qualified names, in order of precedence *)
  sigaccum:sigelts;              (* type declarations being accumulated for the current module *)
  localbindings:list<(either<btvdef,bvvdef> * binding)>;  (* local name bindings for name resolution, paired with an env-generated unique name *)
  recbindings:list<binding>;     (* names bound by recursive type and top-level let-bindings definitions only *)
  phase:AST.level;
  sigmap: list<Util.smap<(sigelt * bool)>>; (* bool indicates that this was declared in an interface file *)
  default_result_effect:typ -> Range.range -> comp;
  iface:bool;
  admitted_iface:bool;
}

let open_modules e = e.modules
let current_module env = match env.curmodule with
    | None -> failwith "Unset current module"
    | Some m -> m
let qual lid id = set_lid_range (lid_of_ids (lid.ns @ [lid.ident;id])) id.idRange
let qualify env id = qual (current_module env) id
let qualify_lid env lid =
  let cur = current_module env in
  set_lid_range (lid_of_ids (cur.ns @ [cur.ident] @ lid.ns @ [lid.ident])) (range_of_lid lid)
let new_sigmap () = Util.smap_create 100
let empty_env () = {curmodule=None;
                    modules=[];
                    open_namespaces=[];
                    sigaccum=[];
                    localbindings=[];
                    recbindings=[];
                    phase=AST.Un;
                    sigmap=[new_sigmap()];
                    default_result_effect=Util.ml_comp;
                    iface=false;
                    admitted_iface=false}
let sigmap env = List.hd env.sigmap
let default_total env = {env with default_result_effect=(fun t _ -> mk_Total t)}
let default_ml env = {env with default_result_effect=Util.ml_comp}

let range_of_binding = function
  | Binding_typ_var id
  | Binding_var id -> id.idRange
  | Binding_let lid
  | Binding_tycon lid -> range_of_lid lid

let try_lookup_typ_var env (id:ident) =
  let fopt = List.tryFind (fun (_, b) -> match b with
    | Binding_typ_var id'
    | Binding_var id' -> id.idText=id'.idText
    | _ -> false) env.localbindings in
  match fopt with
    | Some (Inl bvd, Binding_typ_var _) ->
      Some (bvd_to_typ (set_bvd_range bvd id.idRange) kun)
    | _ -> None

let resolve_in_open_namespaces env lid (finder:lident -> option<'a>) : option<'a> =
  let aux (namespaces:list<lident>) : option<'a> =
    match finder lid with
        | Some r -> Some r
        | _ ->
            let ids = ids_of_lid lid in
            find_map namespaces (fun (ns:lident) ->
                let full_name = lid_of_ids (ids_of_lid ns @ ids) in
                finder full_name) in
  aux (current_module env::env.open_namespaces)

let unmangleMap = [("op_ColonColon", "Cons");
                   ("not", "op_Negation")]

let unmangleOpName (id:ident) =
  find_map unmangleMap (fun (x,y) ->
    if (id.idText = x) then Some (lid_of_path ["Prims"; y] id.idRange)
    else None)

let try_lookup_id' env (id:ident) =
  match unmangleOpName id with
    | Some l -> Some (l, mk_Exp_fvar(fv l, None) None id.idRange)
    | _ ->
      let found = find_map env.localbindings (function
        | Inl _, Binding_typ_var id' when (id'.idText=id.idText) -> Some (Inl ())
        | Inr bvd, Binding_var id' when (id'.idText=id.idText) -> Some (Inr (lid_of_ids [id'], bvd_to_exp (set_bvd_range bvd id.idRange) tun))
        | _ -> None) in
      match found with
        | Some (Inr x) -> Some x
        | _ -> None

let try_lookup_id env id =
  match try_lookup_id' env id with
    | Some(_, e) -> Some e
    | None -> None

type occurrence =
  | OSig of sigelt
  | OLet of lident
  | ORec of lident
let range_of_occurrence = function
  | OLet l
  | ORec l -> range_of_lid l
  | OSig se -> Util.range_of_sigelt se

type foundname =
  | Exp_name of occurrence * exp
  | Typ_name of occurrence * typ
  | Eff_name of occurrence * lident
  | Knd_name of occurrence * lident

let fv_qual_of_se = function
    | Sig_datacon(_, _, (l, _, _), quals, _, _) ->
      let qopt = Util.find_map quals (function
          | RecordConstructor fs -> Some (Record_ctor(l, fs))
          | _ -> None) in
      begin match qopt with
        | None -> Some Data_ctor
        | x -> x
      end
    | Sig_val_decl (_, _, quals, _) ->  //TODO: record projectors?
      None
    | _ -> None

let try_lookup_name any_val exclude_interf env (lid:lident) : option<foundname> =
  (* Resolve using, in order,
     1. rec bindings
     2. sig bindings in current module
     3. each open namespace, in reverse order *)
  let find_in_sig lid  =
    match Util.smap_try_find (sigmap env) lid.str with
      | Some (_, true) when exclude_interf -> None
      | None -> None
      | Some (se, _) ->
        begin match se with
          | Sig_typ_abbrev _
          | Sig_tycon _ -> Some (Typ_name(OSig se, ftv lid kun))
          | Sig_kind_abbrev _ -> Some(Knd_name(OSig se, lid))
          | Sig_new_effect(ne, _) -> Some (Eff_name(OSig se, set_lid_range ne.mname (range_of_lid lid)))
          | Sig_effect_abbrev _ -> Some(Eff_name(OSig se, lid))
          | Sig_datacon _ -> Some (Exp_name(OSig se, fvar (fv_qual_of_se se) lid (range_of_lid lid)))
          | Sig_let _ -> Some (Exp_name(OSig se,  fvar None lid (range_of_lid lid)))
          | Sig_val_decl(_, _, quals, _) ->
            if any_val || quals |> Util.for_some (function Assumption -> true | _ -> false)
            then Some (Exp_name(OSig se, fvar (fv_qual_of_se se) lid (range_of_lid lid)))
            else None
          | _ -> None
        end in

  let found_id = match lid.ns with
    | [] ->
      begin match try_lookup_id' env (lid.ident) with
        | Some (lid, e) -> Some (Exp_name(OLet lid, e))
        | None ->
          let recname = qualify env lid.ident in
          Util.find_map env.recbindings (function
            | Binding_let l when lid_equals l recname -> Some (Exp_name(ORec l, Util.fvar None recname (range_of_lid recname)))
            | Binding_tycon l when lid_equals l recname  -> Some(Typ_name(ORec l, ftv recname kun))
            | _ -> None)
      end
    | _ -> None in

  match found_id with
    | Some _ -> found_id
    | _ -> resolve_in_open_namespaces env lid find_in_sig

let try_lookup_typ_name' exclude_interf env (lid:lident) : option<typ> =
  match try_lookup_name true exclude_interf env lid with
    | Some (Typ_name(_, t)) -> Some t
    | Some (Eff_name(_, l)) -> Some (Util.ftv l mk_Kind_unknown)
    | _ -> None
let try_lookup_typ_name env l = try_lookup_typ_name' (not env.iface) env l

let try_lookup_effect_name' exclude_interf env (lid:lident) : option<(occurrence*lident)> =
  match try_lookup_name true exclude_interf env lid with
    | Some (Eff_name(o, l)) -> Some (o,l)
    | _ -> None
let try_lookup_effect_name env l =
    match try_lookup_effect_name' (not env.iface) env l with
        | Some (o, l) -> Some l
        | _ -> None
let try_lookup_effect_defn env l =
    match try_lookup_effect_name' (not env.iface) env l with
        | Some (OSig (Sig_new_effect(ne, _)), _) -> Some ne
        | _ -> None
let is_effect_name env lid =
    match try_lookup_effect_name env lid with
        | None -> false
        | Some _ -> true

let try_resolve_typ_abbrev env lid =
  let find_in_sig lid =
    match Util.smap_try_find (sigmap env) lid.str with
      | Some (Sig_typ_abbrev(lid, tps, k, def, _, _), _) ->
        let t = mk_Typ_meta(Meta_named(Util.close_with_lam tps def, lid)) in
        Some t
      | _ -> None in
  resolve_in_open_namespaces env lid find_in_sig

let lookup_letbinding_quals env lid =
  let find_in_sig lid =
    match Util.smap_try_find (sigmap env) lid.str with
      | Some (Sig_val_decl(lid, _, quals, _), _) -> Some quals
      | _ -> None in
  match resolve_in_open_namespaces env lid find_in_sig with
    | Some quals -> quals
    | _ -> []

let try_lookup_module env path =
  match List.tryFind (fun (mlid, modul) -> path_of_lid mlid = path) env.modules with
    | Some (_, modul) -> Some modul
    | None -> None

let try_lookup_let env (lid:lident) =
  let find_in_sig lid =
    match Util.smap_try_find (sigmap env) lid.str with
      | Some (Sig_let _, _) -> Some (fvar None lid (range_of_lid lid))
      | _ -> None in
  resolve_in_open_namespaces env lid find_in_sig

let try_lookup_lid' any_val exclude_interf env (lid:lident) : option<exp> =
  match try_lookup_name any_val exclude_interf env lid with
    | Some (Exp_name(_, e)) -> Some e
    | _ -> None
let try_lookup_lid (env:env) l = try_lookup_lid' env.iface false env l

let try_lookup_datacon env (lid:lident) =
  let find_in_sig lid =
    match Util.smap_try_find (sigmap env) lid.str with
      | Some (Sig_val_decl(_, _, quals, _), _) ->
        if quals |> Util.for_some (function Assumption -> true | _ -> false)
        then Some (fv lid)
        else None
      | Some (Sig_datacon _, _) -> Some (fv lid)
      | _ -> None in
  resolve_in_open_namespaces env lid find_in_sig

let find_all_datacons env (lid:lident) =
  let find_in_sig lid =
    match Util.smap_try_find (sigmap env) lid.str with
      | Some (Sig_tycon(_, _, _, _, datas, _, _), _) -> Some datas
      | _ -> None in
  resolve_in_open_namespaces env lid find_in_sig

type record_or_dc = {
  typename: lident;
  constrname: lident;
  parms: binders;
  fields: list<(fieldname * typ)>;
  is_record:bool
}

//no top-level pattern in F*, so need to do this ugliness
let record_cache_aux = 
    let record_cache : ref<list<list<record_or_dc>>> = Util.mk_ref [[]] in
    let push () =
        record_cache := List.hd !record_cache::!record_cache in
    let pop () = 
        record_cache := List.tl !record_cache in
    let peek () = List.hd !record_cache in
    let insert r = record_cache := (r::peek())::List.tl (!record_cache) in
    (push, pop, peek, insert) 
    
let push_record_cache = 
    let push, _, _, _ = record_cache_aux in
    push

let pop_record_cache = 
    let _, pop, _, _ = record_cache_aux in
    pop

let peek_record_cache = 
    let _, _, peek, _ = record_cache_aux in
    peek

let insert_record_cache = 
    let _, _, _, insert = record_cache_aux in
    insert

let extract_record (e:env) = function
  | Sig_bundle(sigs, _, _, _) ->
    let is_rec = Util.for_some (function
      | RecordType _
      | RecordConstructor _ -> true
      | _ -> false) in

    let find_dc dc =
      sigs |> Util.find_opt (function
        | Sig_datacon(lid, _, _, _, _, _) -> lid_equals dc lid
        | _ -> false) in

    sigs |> List.iter (function
      | Sig_tycon(typename, parms, _, _, [dc], tags, _) ->
        begin match must <| find_dc dc with
            | Sig_datacon(constrname, t, _, _, _, _) ->
                let formals = match Util.function_formals t with
                    | Some (x, _) -> x
                    | _ -> [] in
                let is_rec = is_rec tags in 
                let fields = formals |> List.collect (fun b -> match b with
                    | Inr x, q ->
                        if is_null_binder b  
                        || (is_rec && q = Some Implicit)
                        then []
                        else [(qual constrname (if is_rec then Util.unmangle_field_name x.v.ppname else x.v.ppname), x.sort)]
                    | _ -> []) in
                let record = {typename=typename;
                              constrname=constrname;
                              parms=parms;
                              fields=fields;
                              is_record=is_rec} in
                insert_record_cache record
            | _ -> ()
        end
      | _ -> ())

  | _ -> ()

let try_lookup_record_or_dc_by_field_name env (fieldname:lident) =
  let maybe_add_constrname ns c =
    let rec aux ns = match ns with
      | [] -> [c]
      | [c'] -> if c'.idText = c.idText then [c] else [c';c]
      | hd::tl -> hd::aux tl in
    aux ns in
  let find_in_cache fieldname =
//Util.print_string (Util.format1 "Trying field %s\n" fieldname.str);
    let ns, fieldname = fieldname.ns, fieldname.ident in
    Util.find_map (peek_record_cache()) (fun record ->
      let constrname = record.constrname.ident in
      let ns = maybe_add_constrname ns constrname in
      let fname = lid_of_ids (ns@[fieldname]) in
      Util.find_map record.fields (fun (f, _) ->
        if lid_equals fname f
        then Some(record, fname)
        else None)) in
  resolve_in_open_namespaces env fieldname find_in_cache

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
    let fname = lid_of_ids (ns@[constrname]@[fieldname]) in
    Util.find_map recd.fields (fun (f, _) ->
      if lid_equals fname f
      then Some(fname)
      else None) in
  resolve_in_open_namespaces env f qualify

let find_kind_abbrev env l =
  match try_lookup_name true (not env.iface) env l with
    | Some (Knd_name(_, l)) -> Some l
    | _ -> None

let is_kind_abbrev env l =
  match find_kind_abbrev env l with
    | None -> false
    | Some _ -> true

let unique_name any_val exclude_if env lid =
  match try_lookup_lid' any_val exclude_if env lid with
    | None ->
      begin match find_kind_abbrev env lid with
        | None -> true
        | Some _ -> false
      end
    | Some _ -> false

let unique_typ_name env lid =
  match try_lookup_typ_name' true env lid with
    | None -> true
    | Some a -> false

let unique any_val exclude_if env lid =
  let this_env = {env with open_namespaces=[]} in
  unique_name any_val exclude_if this_env lid && unique_typ_name this_env lid

let gen_bvd = function
  | Binding_typ_var id -> Inl (mkbvd(id, genident (Some id.idRange)))
  | Binding_var id -> Inr (mkbvd(id, genident (Some id.idRange)))
  | _ -> failwith "Tried to generate a bound variable for a type constructor"

let push_bvvdef env x =
  let b = Binding_var x.ppname in
  {env with localbindings=(Inr x, b)::env.localbindings}

let push_btvdef env x =
  let b = Binding_typ_var x.ppname in
  {env with localbindings=(Inl x, b)::env.localbindings}

let push_local_binding env b =
  let bvd = gen_bvd b in
  {env with localbindings=(bvd, b)::env.localbindings}, bvd

let push_local_tbinding env a =
  match push_local_binding env (Binding_typ_var a) with
    | env, Inl x -> env, x
    | _ -> failwith "impossible"

let push_local_vbinding env b =
  match push_local_binding env (Binding_var b) with
    | env, Inr x ->
      env, x
    | _ -> failwith "impossible"

let push_rec_binding env b = match b with
  | Binding_let lid
  | Binding_tycon lid ->
    if unique false true env lid
    then {env with recbindings=b::env.recbindings}
    else raise (Error ("Duplicate top-level names " ^ lid.str, range_of_lid lid))
  | _ -> failwith "Unexpected rec_binding"

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
  let env =
      let any_val, exclude_if = match s with
        | Sig_let _ -> false, true
        | Sig_bundle _ -> true, true
        | _ -> false, false in
      let lids = lids_of_sigelt s in
      begin match Util.find_map lids (fun l -> if not (unique any_val exclude_if env l) then Some l else None) with
        | None -> extract_record env s; {env with sigaccum=s::env.sigaccum}
        | Some l -> err l
      end in
  let env, lss = match s with
    | Sig_bundle(ses, _, _, _) -> env, List.map (fun se -> (lids_of_sigelt se, se)) ses
    | _ -> env, [lids_of_sigelt s, s] in
  lss |> List.iter (fun (lids, se) ->
    lids |> List.iter (fun lid ->
      Util.smap_add (sigmap env) lid.str (se, env.iface && not env.admitted_iface)));
  env

let push_namespace env lid =
  {env with open_namespaces = lid::env.open_namespaces}

let is_type_lid env lid =
  let aux () = match try_lookup_typ_name' false env lid with
    | Some _ -> true
    | _ -> false in
  if lid.ns=[]
  then match try_lookup_id env lid.ident with //bound variables can shadow type names
    | Some _ -> false
    | _ -> aux()
  else aux ()


let check_admits nm env =
  let warn = not (!Options.admit_fsi |> Util.for_some (fun l -> nm.str = l)) in
  env.sigaccum |> List.iter (fun se -> match se with
    | Sig_val_decl(l, t, quals, r) ->
      begin match try_lookup_lid env l with
        | None ->
          if warn then Util.print_string (Util.format2 "%s: Warning: Admitting %s without a definition\n" (Range.string_of_range (range_of_lid l)) (Print.sli l));
          Util.smap_add (sigmap env) l.str (Sig_val_decl(l, t, Assumption::quals, r), false)
        | Some _ -> ()
      end
    | _ -> ())

let finish env modul =
  modul.declarations |> List.iter (function
    | Sig_bundle(ses, quals, _, _) ->
      if List.contains Private quals
      then ses |> List.iter (function
                | Sig_datacon(lid, _, _, _, _, _) -> Util.smap_remove (sigmap env) lid.str
                | _ -> ())
    | Sig_val_decl(lid, _, quals, _) ->
      if List.contains Private quals
      then Util.smap_remove (sigmap env) lid.str
    | _ -> ());
  {env with
    curmodule=None;
    modules=(modul.name, modul)::env.modules;
    open_namespaces=[];
    sigaccum=[];
    localbindings=[];
    recbindings=[];
    phase=AST.Un}

let push (env:env) =
    push_record_cache();
    {env with
        sigmap=Util.smap_copy (sigmap env)::env.sigmap;}

let mark env = push env
let reset_mark env = {env with sigmap=List.tl env.sigmap}
let commit_mark env = match env.sigmap with
    | hd::_::tl -> {env with sigmap=hd::tl}
    | _ -> failwith "Impossible"
let pop env = match env.sigmap with
    | _::maps ->
        pop_record_cache();
        {env with
            sigmap=maps}
    | _ -> failwith "No more modules to pop"

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
            | Sig_val_decl(l, t, q, r) -> Sig_val_decl(l, t, Assumption::q, r)
            | _ -> se in 
          Util.smap_add sm' k (se, false)
        | _ -> ());
    env

let finish_module_or_interface env modul =
  if not modul.is_interface
  then check_admits modul.name env;
  finish env modul

let prepare_module_or_interface intf admitted env mname =
  let prep env =
    (* These automatic directives must be kept in sync with [dep.fs]. *)
    let open_ns = if      lid_equals mname Const.prims_lid then []
                  else if lid_equals mname Const.st_lid    then [Const.prims_lid]
                  else if lid_equals mname Const.all_lid   then [Const.prims_lid; Const.st_lid]
                  else [Const.prims_lid; Const.st_lid; Const.all_lid; Const.fstar_ns_lid] in
    {env with curmodule=Some mname; sigmap=env.sigmap; open_namespaces = open_ns; iface=intf; admitted_iface=admitted} in

  match env.modules |> Util.find_opt (fun (l, _) -> lid_equals l mname) with
    | None -> prep env, false
    | Some (_, m) ->
      if not m.is_interface || intf
      then raise (Error(Util.format1 "Duplicate module or interface name: %s" mname.str, range_of_lid mname));
      //we have an interface for this module already; if we're not interactive then do not export any symbols from this module
      prep (push env), true //push a context so that we can pop it when we're done

let enter_monad_scope env mname =
  let curmod = current_module env in
  let mscope = lid_of_ids (curmod.ns@[curmod.ident; mname]) in
  {env with
    curmodule=Some mscope;
    open_namespaces=curmod::env.open_namespaces}

let exit_monad_scope env0 env =
  {env with
    curmodule=env0.curmodule;
    open_namespaces=env0.open_namespaces}

let fail_or env lookup lid = match lookup lid with
  | None ->
    let r = match try_lookup_name true false env lid with
      | None -> None
      | Some (Knd_name(o, _))
      | Some (Eff_name(o, _))
      | Some (Typ_name(o, _))
      | Some (Exp_name(o, _)) -> Some (range_of_occurrence o) in
    let msg = match r with
      | None -> ""
      | Some r -> Util.format1 "(Possible clash with related name at %s)" (Range.string_of_range r) in
    raise (Error (Util.format2 "Identifier not found: [%s] %s" (text_of_lid lid) msg, range_of_lid lid))
  | Some r -> r

let fail_or2 lookup id = match lookup id with
  | None -> raise (Error ("Identifier not found [" ^id.idText^"]", id.idRange))
  | Some r -> r

