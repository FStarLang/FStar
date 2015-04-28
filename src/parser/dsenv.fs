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

module Microsoft.FStar.Parser.DesugarEnv


open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util
open Microsoft.FStar.Absyn.Const
open Microsoft.FStar.Parser
    
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
  kind_abbrevs:list<kind_abbrev>;
  recbindings:list<binding>;     (* names bound by recursive type and top-level let-bindings definitions only *)
  phase:AST.level;
  sigmap: Util.smap<(sigelt * bool)>; (* bool indicates that this was declared in an interface file *)
  effect_names:list<lident>;
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
let empty_env () = {curmodule=None; 
                    modules=[]; 
                    open_namespaces=[];
                    sigaccum=[]; 
                    localbindings=[]; 
                    recbindings=[];
                    kind_abbrevs=[];
                    phase=AST.Un;
                    sigmap=Util.smap_create(100);
                    effect_names=[];
                    default_result_effect=Util.ml_comp;
                    iface=false;
                    admitted_iface=false}

let total env = {env with default_result_effect=(fun t _ -> mk_Total t)}
let ml env = {env with default_result_effect=Util.ml_comp}

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
    | Some l -> Some (l, mk_Exp_fvar(fv l, false) None id.idRange)
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
 
let try_lookup_name any_val exclude_interf env (lid:lident) : option<foundname> = 
  (* Resolve using, in order, 
     1. rec bindings
     2. sig bindings in current module
     3. each open namespace, in reverse order *)
  let find_in_sig lid  = 
    match Util.smap_try_find env.sigmap lid.str with 
      | Some (_, true) when exclude_interf -> None
      | None -> None
      | Some (se, _) -> 
        begin match se with 
          | Sig_typ_abbrev _
          | Sig_tycon _ -> Some (Typ_name(OSig se, ftv lid kun))
          | Sig_datacon _ ->  Some (Exp_name(OSig se,  fvar true lid (range_of_lid lid)))
          | Sig_let _ -> Some (Exp_name(OSig se,  fvar false lid (range_of_lid lid)))
          | Sig_val_decl(_, _, quals, _) ->
            if any_val || quals |> Util.for_some (function Assumption -> true | _ -> false)
            then Some (Exp_name(OSig se, fvar false lid (range_of_lid lid)))
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
            | Binding_let l when lid_equals l recname -> Some (Exp_name(ORec l, Util.fvar false recname (range_of_lid recname)))
            | Binding_tycon l when lid_equals l recname  -> Some(Typ_name(ORec l, ftv recname kun))
            | _ -> None)
      end
    | _ -> None in

  match found_id with 
    | Some _ -> found_id
    | _ -> resolve_in_open_namespaces env lid find_in_sig

let try_lookup_typ_name' exclude_interf env (lid:lident) : option<typ> = 
  match try_lookup_name true exclude_interf env lid with 
    | None -> None
    | Some (Exp_name _) -> None//Util.print_string ("Resolved name " ^lid.str^ " as an exp\n");None
    | Some (Typ_name(_, t)) -> Some t
let try_lookup_typ_name env l = try_lookup_typ_name' (not env.iface) env l

let is_effect_name env lid = 
  let find_in_sig lid = 
    match Util.smap_try_find env.sigmap lid.str with 
      | Some (Sig_tycon(_, _, _, _, _, tags, _), _) 
      | Some (Sig_typ_abbrev (_, _, _, _, tags, _), _) -> 
        if Util.for_some (function Effect -> true | _ -> false) tags
        then Some (ftv lid kun)
        else None 
      | Some (Sig_monads(_, _, _, lids), _) -> 
        if lids |> Util.for_some (lid_equals lid)
        then Some (ftv lid kun)
        else None
      | _ -> None in
  env.effect_names |> Util.for_some (lid_equals lid)
  || resolve_in_open_namespaces env lid find_in_sig |> Util.is_some 
 
let try_resolve_typ_abbrev env lid = 
  let find_in_sig lid = 
    match Util.smap_try_find env.sigmap lid.str with 
      | Some (Sig_typ_abbrev(lid, tps, k, def, _, _), _) -> 
        let t = mk_Typ_meta(Meta_named(Util.close_with_lam tps def, lid)) in
        Some t
      | _ -> None in
  resolve_in_open_namespaces env lid find_in_sig

let lookup_letbinding_quals env lid = 
  let find_in_sig lid = 
    match Util.smap_try_find env.sigmap lid.str with 
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
    match Util.smap_try_find env.sigmap lid.str with 
      | Some (Sig_let _, _) -> Some (fvar false lid (range_of_lid lid))
      | _ -> None in
  resolve_in_open_namespaces env lid find_in_sig
          
let try_lookup_lid' any_val exclude_interf env (lid:lident) : option<exp> = 
  match try_lookup_name any_val exclude_interf env lid with 
    | None -> None
    | Some (Typ_name _) -> None//Util.print_string ("Resolved name " ^lid.str^ " as a type\n"); None
    | Some (Exp_name(_, e)) -> Some e
let try_lookup_lid (env:env) l = try_lookup_lid' env.iface false env l

let try_lookup_datacon env (lid:lident) = 
  let find_in_sig lid = 
    match Util.smap_try_find env.sigmap lid.str with 
      | Some (Sig_val_decl(_, _, quals, _), _) -> 
        if quals |> Util.for_some (function Assumption -> true | _ -> false)
        then Some (fv lid)
        else None
      | Some (Sig_datacon _, _) -> Some (fv lid)
      | _ -> None in
  resolve_in_open_namespaces env lid find_in_sig

let find_all_datacons env (lid:lident) = 
  let find_in_sig lid = 
    match Util.smap_try_find env.sigmap lid.str with 
      | Some (Sig_tycon(_, _, _, _, datas, _, _), _) -> Some datas
      | _ -> None in
  resolve_in_open_namespaces env lid find_in_sig

type record = {
  typename: lident;
  constrname: lident;
  parms: binders;
  fields: list<(fieldname * typ)>
}
let record_cache : ref<list<record>> = Util.mk_ref []

let extract_record (e:env) = function 
  | Sig_bundle(sigs, _, _) -> 
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
        if is_rec tags
        then match must <| find_dc dc with 
            | Sig_datacon(constrname, t, _, _, _, _) -> 
                let formals = match Util.function_formals t with 
                    | Some (x, _) -> x 
                    | _ -> [] in
                let fields = formals |> List.collect (fun b -> match b with
                    | Inr x, _ ->  
                        if is_null_binder b 
                        then []
                        else [(qual constrname (Util.unmangle_field_name x.v.ppname), x.sort)]
                    | _ -> []) in
                let record = {typename=typename;
                              constrname=constrname;
                              parms=parms;
                              fields=fields} in 
                record_cache := record::!record_cache 
            | _ -> ()
        else () 
      | _ -> ())

  | _ -> ()

let try_lookup_record_by_field_name env (fieldname:lident) = 
  let maybe_add_constrname ns c = 
    let rec aux ns = match ns with
      | [] -> [c]
      | [c'] -> if c'.idText = c.idText then [c] else [c';c]
      | hd::tl -> hd::aux tl in 
    aux ns in
  let find_in_cache fieldname = 
//Util.print_string (Util.format1 "Trying field %s\n" fieldname.str);
    let ns, fieldname = fieldname.ns, fieldname.ident in
    Util.find_map (!record_cache) (fun record -> 
      let constrname = record.constrname.ident in
      let ns = maybe_add_constrname ns constrname in 
      let fname = lid_of_ids (ns@[fieldname]) in
      Util.find_map record.fields (fun (f, _) -> 
        if lid_equals fname f
        then Some(record, fname)
        else None)) in
  resolve_in_open_namespaces env fieldname find_in_cache

let qualify_field_to_record env (recd:record) (f:lident) = 
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
  List.tryFind (fun (l', _, _) -> 
    let res = lid_equals l l' in
    //printfn "Comparing kind abbrevs %s and %s ... %b\n" l.str l'.str res;
    res) env.kind_abbrevs

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
      
let push_kind_abbrev env (lid, parms, k) = 
  if unique true false env lid 
  then {env with kind_abbrevs=(lid, parms, k)::env.kind_abbrevs}
  else raise (Error ("Duplicate top-level names " ^ lid.str, range_of_lid lid))

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
    let sopt = Util.smap_try_find env.sigmap l.str in
    let r = match sopt with 
      | Some (se, _) ->
        begin match Util.find_opt (lid_equals l) (lids_of_sigelt se) with
          | Some l -> Range.string_of_range <| range_of_lid l
          | None -> "<unknown>"
        end
      | None -> "<unknown>" in
    raise (Error (Util.format2 "Duplicate top-level names [%s]; previously declared at %s" (text_of_lid l) r, range_of_lid l)) in
  let env = match s with 
    | Sig_monads _ -> env
    | _ -> 
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
    | Sig_bundle(ses, _, _) -> env, List.map (fun se -> (lids_of_sigelt se, se)) ses
    | Sig_monads _ -> 
      let lids = lids_of_sigelt s in
      let env = {env with effect_names=lids@env.effect_names} in 
      env, []
    | _ -> env, [lids_of_sigelt s, s] in
  lss |> List.iter (fun (lids, se) -> 
    lids |> List.iter (fun lid -> 
      Util.smap_add env.sigmap lid.str (se, env.iface && not env.admitted_iface)));
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
          Util.smap_add env.sigmap l.str (Sig_val_decl(l, t, Assumption::quals, r), false)
        | Some _ -> ()
      end
    | _ -> ())

let finish env modul = 
  {env with 
    curmodule=None;
    modules=(modul.name, modul)::env.modules; 
    open_namespaces=[];
    sigaccum=[];
    localbindings=[];
    recbindings=[];
    phase=AST.Un}

let finish_module_or_interface env modul = 
  if not modul.is_interface 
  then check_admits modul.name env;
  finish env modul

let prepare_module_or_interface intf admitted env mname =
  let prep env = 
    let open_ns = if lid_equals mname Const.prims_lid then [] else Const.prims_lid::env.effect_names in
    {env with curmodule=Some mname; open_namespaces = open_ns; iface=intf; admitted_iface=admitted} in
  match env.modules |> Util.find_opt (fun (l, _) -> lid_equals l mname) with
    | None -> prep env
    | Some (_, m) -> 
      if intf 
      then raise (Error(Util.format1 "Duplicate module or interface name: %s" mname.str, range_of_lid mname));
      prep env 
//      let vals = m.declarations |> List.filter (function 
//        | Sig_val_decl _ -> true
//        | _ -> false) in
//      prep ({env with sigaccum=m.declarations})

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

