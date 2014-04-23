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

type env = {
  curmodule: option<lident>;
  modules:list<(lident * modul)>;  (* previously desugared modules *)
  open_namespaces: list<lident>; (* fully qualified names, in order of precedence *)
  sigaccum:sigelts;              (* type declarations being accumulated for the current module *)
  localbindings:list<(either<btvdef,bvvdef> * binding)>;  (* local name bindings for name resolution, paired with an env-generated unique name *)
  recbindings:list<binding>;     (* names bound by recursive type and top-level let-bindings definitions only *)
  phase:AST.level;
  sigmap: Util.smap<sigelt>;
}

let fail_or lookup lid = match lookup lid with 
  | None -> raise (Error ("Identifier not found: [" ^(text_of_lid lid)^"]", range_of_lid lid))
  | Some r -> r

let fail_or2 lookup id = match lookup id with 
  | None -> raise (Error ("Identifier not found [" ^id.idText^"]", id.idRange))
  | Some r -> r

let open_modules e = e.modules
let current_module env = match env.curmodule with 
    | None -> failwith "Unset current module"
    | Some m -> m
let qual lid id = set_lid_range (lid_of_ids (lid.ns @ [lid.ident;id])) id.idRange
let qualify env id = qual (current_module env) id
let empty_env () = {curmodule=None; 
                    modules=[]; 
                    open_namespaces=[];
                    sigaccum=[]; 
                    localbindings=[]; 
                    recbindings=[];
                    phase=AST.Un;
                    sigmap=Util.smap_create(100)}

let prepare_module env mname = 
  let open_ns = if lid_equals mname Const.prims_lid then [] else [Const.prims_lid] in
  {env with curmodule=Some mname; open_namespaces = open_ns}

let range_of_binding = function
  | Binding_typ_var id
  | Binding_var id -> id.idRange
  | Binding_let lid
  | Binding_tycon lid -> range_of_lid lid
            
let try_lookup_typ_var env (id:ident) =
  let fopt = List.tryFind (fun (_, b) -> match b with 
    | Binding_typ_var id' -> id.idText=id'.idText 
    | _ -> false) env.localbindings in
  match fopt with 
    | Some (Inl bvd, _) -> 
      Some (bvd_to_typ (set_bvd_range bvd id.idRange) Kind_unknown)
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

let try_lookup_typ_name env (lid:lident) : option<typ> = 
  (* Resolve using, in order, 
     1. rec bindings
     2. sig bindings in current module
     3. each open namespace, in order *)
  let find_rec () = match lid.ns with 
    | [] -> 
      let n = lid.ident in
      let qlid = qualify env n in 
      find_map env.recbindings
        (function 
          | Binding_tycon lid' -> 
            if lid_equals qlid lid'
            then Some (ftv qlid)
            else None
          | _ -> None)
    | _ -> None in

  let find_in_sig lid = 
    match Util.smap_try_find env.sigmap lid.str with 
      | Some (Sig_tycon _) 
      | Some (Sig_typ_abbrev _) -> Some (ftv <| lid)
      | _ -> None in
  
  match find_rec () with 
    | None -> resolve_in_open_namespaces env lid find_in_sig
    | r -> r


let unmangleMap = [("op_ColonColon", "Cons");
                   ("not", "_op_Negation")]
      
let unmangleOpName (id:ident) = 
  find_map unmangleMap (fun (x,y) -> 
    if (id.idText = x) then Some (lid_of_path ["Prims"; y] id.idRange)
    else None)
    
let try_lookup_id env (id:ident) =
  match unmangleOpName id with 
    | Some l -> Some <| ewithpos (Exp_fvar(fv l, false)) id.idRange
    | _ -> 
      find_map env.localbindings (function 
        | Inr bvd, Binding_var id' when (id'.idText=id.idText) -> Some (bvd_to_exp (set_bvd_range bvd id.idRange) Typ_unknown)
        | _ -> None)
        
let try_lookup_module env path = 
  match List.tryFind (fun (mlid, modul) -> path_of_lid mlid = path) env.modules with
    | Some (_, modul) -> Some modul
    | None -> None

let try_lookup_let env (lid:lident) = 
  let find_in_sig lid = 
    match Util.smap_try_find env.sigmap lid.str with 
      | Some (Sig_let _) -> Some (fvar lid (range_of_lid lid))
      | _ -> None in
  resolve_in_open_namespaces env lid find_in_sig
          
let try_lookup_lid env (lid:lident) = 
  let find_in_sig lid  = 
    match Util.smap_try_find env.sigmap lid.str with 
      | Some (Sig_datacon _)
      | Some (Sig_val_decl _)
      | Some (Sig_logic_function _)
      | Some (Sig_let _) -> 
        Some (fvar lid (range_of_lid lid))
      | _ -> 
        None in

  let found_id = match lid.ns with
    | [] -> 
      begin match try_lookup_id env (lid.ident) with 
        | Some e -> Some e
        | None -> 
          let recname = qualify env lid.ident in
          Util.find_map env.recbindings (function
            | Binding_let l when lid_equals l recname -> Some (Util.fvar recname (range_of_lid recname))
            | _ -> None)
      end
    | _ -> None in
  
  match found_id with 
    | Some _ -> found_id
    | _ -> resolve_in_open_namespaces env lid find_in_sig

let try_lookup_datacon env (lid:lident) = 
  let find_in_sig lid = 
    match Util.smap_try_find env.sigmap lid.str with 
      | Some (Sig_logic_function _)
      | Some (Sig_datacon _) -> Some <| fv lid
      | _ -> None in
  resolve_in_open_namespaces env lid find_in_sig

type record = {
  typename: lident;
  constrname: lident;
  parms: list<tparam>;
  fields: list<(fieldname * typ)>
}
let record_cache : ref<list<record>> = Util.mk_ref []

let extract_record env = function 
  | Sig_bundle sigs -> 
    let is_rec = Util.for_some (function 
      | Logic_record -> true
      | _ -> false) in
    
    let find_dc dc = 
      sigs |> Util.find_opt (function 
        | Sig_datacon(lid, _, _) -> lid_equals dc lid 
        | _ -> false) in
    
    sigs |> List.iter (function 
      | Sig_tycon(typename, parms, _, _, [dc], tags) when is_rec tags -> 
        begin match must <| find_dc dc with 
          | Sig_datacon(constrname, t, _) -> 
              let fields = 
                (fst <| collect_formals t) |> List.collect (function
                  | Inr(Some x, t) -> [(qual constrname x.ppname, t)]
                  | _ -> []) in
              let record = {typename=typename;
                            constrname=constrname;
                            parms=parms;
                            fields=fields} in 
              record_cache := record::!record_cache 
          | _ -> ()
        end 
      | _ -> ())

  | _ -> ()

let try_lookup_record_by_field_name env (fieldname:lident) = 
  let find_in_cache fieldname = 
    let ns, fieldname = fieldname.ns, fieldname.ident in
    Util.find_map (!record_cache) (fun record -> 
      let constrname = record.constrname.ident in
      let fname = lid_of_ids (ns@[constrname]@[fieldname]) in
      Util.find_map record.fields (fun (f, _) -> 
        if lid_equals fname f
        then Some(record, fname)
        else None)) in
  resolve_in_open_namespaces env fieldname find_in_cache

let qualify_field_to_record env (record:record) (f:lident) = 
  let qualify fieldname =  
    let ns, fieldname = fieldname.ns, fieldname.ident in
    let constrname = record.constrname.ident in
    let fname = lid_of_ids (ns@[constrname]@[fieldname]) in
    Util.find_map record.fields (fun (f, _) -> 
      if lid_equals fname f
      then Some(fname)
      else None) in
  resolve_in_open_namespaces env f qualify
    
let unique_name env lid = 
  match try_lookup_lid env lid with
    | None -> true
    | Some _ -> false
      
let unique_typ_name env lid = 
  match try_lookup_typ_name env lid with
    | None -> true
    | Some a -> false

let unique env lid = 
  let this_env = {env with open_namespaces=[]} in
  unique_name this_env lid && unique_typ_name this_env lid
      
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
    if unique env lid
    then {env with recbindings=b::env.recbindings}
    else raise (Error ("Duplicate top-level names " ^ lid.str, range_of_lid lid))
  | _ -> failwith "Unexpected rec_binding"
    
let push_sigelt env s = 
  let err l = raise (Error ("Duplicate top-level names " ^ (text_of_lid l), range_of_lid l)) in
  let env = match Util.find_map (lids_of_sigelt s) (fun l -> if not (unique env l) then Some l else None) with 
    | None -> 
      extract_record env s;
      {env with sigaccum=s::env.sigaccum}
    | Some l -> 
      err l in 
  let lss = match s with 
    | Sig_bundle ses -> List.map (fun se -> (lids_of_sigelt se, se)) ses
    | Sig_val_decl(_, _, None) -> [] 
    | _ -> [lids_of_sigelt s, s] in
  lss |> List.iter (fun (lids, se) -> 
    lids |> List.iter (fun lid -> 
      Util.smap_add env.sigmap lid.str se));
  env
    
let push_namespace env lid = 
  {env with open_namespaces = lid::env.open_namespaces}

let is_type_lid env lid = 
  match try_lookup_typ_name env lid with
    | Some _ -> true
    | _ -> false

let finish_module env modul = 
  env.sigaccum |> List.iter (fun se -> match se with
    | Sig_val_decl(l, t, None) -> 
      begin match try_lookup_lid env l with 
        | None -> 
          Util.print_string (Util.format2 "%s: Warning: Admitting %s without a definition\n" (Range.string_of_range (range_of_lid l)) (Print.sli l));
          Util.smap_add env.sigmap l.str se
        | Some _ -> ()
      end
    | _ -> ());
  {env with 
    curmodule=None;
    modules=(modul.name, modul)::env.modules; 
    open_namespaces=[];
    sigaccum=[];
    localbindings=[];
    recbindings=[];
    phase=AST.Un}


