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
  interf:bool
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
                    interf=false}

let total env = {env with default_result_effect=(fun t _ -> Total t)}
let ml env = {env with default_result_effect=Util.ml_comp}

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

let try_lookup_typ_name' exclude_interf env (lid:lident) : option<typ> = 
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
      | Some (Sig_tycon _, i) 
      | Some (Sig_typ_abbrev _, i) when not (i && exclude_interf) -> Some (ftv <| lid)
      | _ -> None in
  
  match find_rec () with 
    | None -> resolve_in_open_namespaces env lid find_in_sig
    | r -> r

let try_lookup_typ_name env l = try_lookup_typ_name' (not env.interf) env l

let is_effect_name env lid = 
  let find_in_sig lid = 
    match Util.smap_try_find env.sigmap lid.str with 
      | Some (Sig_tycon(_, _, _, _, _, tags, _), _) 
      | Some (Sig_typ_abbrev (_, _, _, _, tags, _), _) -> 
        if List.contains Logic_effect tags
        then Some (ftv <| lid)
        else None 
      | _ -> None in
  resolve_in_open_namespaces env lid find_in_sig |> Util.is_some

let try_resolve_typ_abbrev env lid = 
  let find_in_sig lid = 
    match Util.smap_try_find env.sigmap lid.str with 
      | Some (Sig_typ_abbrev(lid, tps, k, def, _, _), _) -> 
        let t = withkind Kind_unknown <| Typ_meta(Meta_named(Util.close_with_lam tps def, lid)) in
        Some t
      | _ -> None in
  resolve_in_open_namespaces env lid find_in_sig
   
let unmangleMap = [("op_ColonColon", "Cons");
                   ("not", "op_Negation")]
      
let unmangleOpName (id:ident) = 
  find_map unmangleMap (fun (x,y) -> 
    if (id.idText = x) then Some (lid_of_path ["Prims"; y] id.idRange)
    else None)
    
let try_lookup_id env (id:ident) =
  match unmangleOpName id with 
    | Some l -> Some <|  Exp_fvar(fv l, false)
    | _ -> 
      find_map env.localbindings (function 
        | Inr bvd, Binding_var id' when (id'.idText=id.idText) -> Some (bvd_to_exp (set_bvd_range bvd id.idRange) tun)
        | _ -> None)
       
let try_lookup_module env path = 
  match List.tryFind (fun (mlid, modul) -> path_of_lid mlid = path) env.modules with
    | Some (_, modul) -> Some modul
    | None -> None

let try_lookup_let env (lid:lident) = 
  let find_in_sig lid = 
    match Util.smap_try_find env.sigmap lid.str with 
      | Some (Sig_let _, _) -> Some (fvar lid (range_of_lid lid))
      | _ -> None in
  resolve_in_open_namespaces env lid find_in_sig
          
let try_lookup_lid' any_val exclude_interf env (lid:lident) : option<exp> = 
  let find_in_sig lid  = 
    match Util.smap_try_find env.sigmap lid.str with 
      | Some (_, true) when exclude_interf -> None
      | Some (Sig_datacon _, _)
      | Some (Sig_logic_function _, _)
      | Some (Sig_let _, _) -> 
        Some (fvar lid (range_of_lid lid))
      | Some (Sig_val_decl(_, _, aopt, _, _), _) ->
          begin match aopt with 
            | Some Assumption -> Some (fvar lid (range_of_lid lid))
            | _ when any_val -> Some (fvar lid (range_of_lid lid))
            | _ -> None
          end
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

let try_lookup_lid env l = try_lookup_lid' false false env l

let try_lookup_datacon env (lid:lident) = 
  let find_in_sig lid = 
    match Util.smap_try_find env.sigmap lid.str with 
      | Some (Sig_logic_function _, _)
      | Some (Sig_datacon _, _) -> Some <| fv lid
      | _ -> None in
  resolve_in_open_namespaces env lid find_in_sig

type record = {
  typename: lident;
  constrname: lident;
  parms: list<tparam>;
  fields: list<(fieldname * typ)>
}
let record_cache : ref<list<record>> = Util.mk_ref []

let extract_record (env:env) = function 
  | Sig_bundle(sigs, _) -> 
    let is_rec = Util.for_some (function 
      | Logic_record -> true
      | _ -> false) in
    
    let find_dc dc = 
      sigs |> Util.find_opt (function 
        | Sig_datacon(lid, _, _, _) -> lid_equals dc lid 
        | _ -> false) in
    
    sigs |> List.iter (function 
      | Sig_tycon(typename, parms, _, _, [dc], tags, _) ->
        if is_rec tags
        then match must <| find_dc dc with 
            | Sig_datacon(constrname, t, _, _) -> 
                let fields = 
                  (fst <| collect_formals t) |> List.collect (function
                    | Inr(Some x, t, _) -> [(qual constrname x.ppname, t)]
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
    | Sig_bundle(ses, _) -> env, List.map (fun se -> (lids_of_sigelt se, se)) ses
    | Sig_monads _ -> 
      let lids = lids_of_sigelt s in
      let env = {env with effect_names=lids@env.effect_names} in 
      env, []
    | _ -> env, [lids_of_sigelt s, s] in
  lss |> List.iter (fun (lids, se) -> 
    lids |> List.iter (fun lid -> 
      Util.smap_add env.sigmap lid.str (se, env.interf)));
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


let check_admits env = 
  env.sigaccum |> List.iter (fun se -> match se with
    | Sig_val_decl(l, t, None, ltags, r) -> 
      begin match try_lookup_lid env l with 
        | None -> 
          Util.print_string (Util.format2 "%s: Warning: Admitting %s without a definition\n" (Range.string_of_range (range_of_lid l)) (Print.sli l));
          Util.smap_add env.sigmap l.str (Sig_val_decl(l, t, Some Assumption, ltags, r), false)
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
  then check_admits env;
  finish env modul

let prepare_module_or_interface intf (env:env) mname =
  let prep env = 
    let open_ns = if lid_equals mname Const.prims_lid then [] else Const.prims_lid::env.effect_names in
    {env with curmodule=Some mname; open_namespaces = open_ns; interf=intf} in
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