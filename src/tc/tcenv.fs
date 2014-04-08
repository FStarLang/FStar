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

module Microsoft.FStar.Tc.Env

open Microsoft.FStar
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util
open Microsoft.FStar.Absyn.Const
open Microsoft.FStar.Util
open Microsoft.FStar.Profiling 
   
type binding =
  | Binding_var of bvvdef * typ
  | Binding_typ of btvdef * kind
  | Binding_sig of sigelt 

type sigtable = Util.smap<sigelt>
let default_table_size = 200
let strlid_of_sigelt se = text_of_lid <| lid_of_sigelt se
let signature_to_sigtables s = 
  let ht = Util.smap_create default_table_size in
  let _ = List.iter (fun se -> 
    let key = strlid_of_sigelt se in
    Util.smap_add ht key se) s in
  ht
      
let modules_to_sigtables mods = 
  signature_to_sigtables (List.collect (fun (_,m) -> m.declarations) mods)

type level = 
  | Expr
  | Type
  | Kind

type env = {
  range:Range.range;             (* the source location of the term being checked *)
  curmodule: lident;             (* Name of this module *)
  gamma:list<binding>;           (* Local typing environment and signature elements *)
  modules:list<modul>;           (* already fully type checked modules *)
  expected_typ:option<typ>;      (* type expected by the context *)
  level:level;                   (* current term being checked is at level *)
  sigtab:sigtable                (* a dictionary of long-names to sigelts *)
}

let rec add_sigelt env se = match se with 
  | Sig_bundle ses -> add_sigelts env ses
  | _ -> Util.smap_add env.sigtab (strlid_of_sigelt se) se
and add_sigelts (env:env) ses = 
  ses |> List.iter (add_sigelt env)

let initial_env module_lid =
  { range=Syntax.dummyRange;
    curmodule=module_lid;
    gamma= [];
    modules= [];
    expected_typ=None;
    level=Expr;
    sigtab=Util.smap_create default_table_size
  }

let set_level env level = {env with level=level}
let is_level env level = env.level=level
let modules env = env.modules
let current_module env = env.curmodule
let set_current_module env lid = {env with curmodule=lid} 
let set_range e r = {e with range=r}
let get_range e = e.range
let find_in_sigtab env lid = Util.smap_try_find env.sigtab (text_of_lid lid)

exception Not_found_binding of env * either<typ,exp>

let lookup_bvvdef env (bvvd:bvvdef) : option<typ> = 
  Util.find_map env.gamma (function
    | Binding_var (id, t) when (Util.bvd_eq id bvvd) -> Some t
    | _ -> None) 
      
let lookup_bvar env bv = 
  match lookup_bvvdef env bv.v with
    | None -> raise (Not_found_binding(env, Inr (Util.bvar_to_exp bv)))
    | Some t -> t 
    
let lookup_qname env (lid:lident)  = 
  if lid.nsstr = (current_module env).nsstr 
  then Util.find_map env.gamma (function 
    | Binding_sig s -> if lid_equals lid (lid_of_sigelt s) then Some s else None
    | _ -> None) 
  else match find_in_sigtab env lid with
    | Some se -> Some se 
    | None -> None
    
let lookup_val_decl (env:env) lid = 
  match lookup_qname env lid with
    | Some (Sig_val_decl(_, t)) -> t
    | _ -> raise (Not_found_binding (env, Inr (Util.fvar lid (range_of_lid lid))))

let lookup_lid env lid = 
  let not_found () = raise (Not_found_binding(env, Inr(Util.fvar lid (range_of_lid lid)))) in
  let mapper = function
    | Sig_datacon(_, t)  
    | Sig_logic_function(_, t, _)
    | Sig_val_decl (_, t) 
    | Sig_let([(_, t, _)], _) -> Some t 
    | Sig_let(lbs, _) -> 
        Util.find_map lbs (fun (lid', t, e) -> 
            if lid_equals lid lid' 
            then Some t
            else None) 
    | _ -> None
  in
    match Util.bind_opt (lookup_qname env lid) mapper with 
      | Some t -> t
      | None -> not_found ()
      
let is_datacon env lid = 
  match lookup_qname env lid with
    | Some (Sig_datacon (_, t)) -> true
    | _ -> false

let is_logic_function env lid =
  match lookup_qname env lid with 
    | Some (Sig_logic_function (_, t, _)) -> true
    | _ -> false
    
let is_logic_data env lid = 
  match lookup_qname env lid with 
    | Some (Sig_tycon(_, _, _, _, _, tags)) -> 
        Util.for_some (fun t -> t=Logic_data) tags 
    | _ -> false
  
let is_logic_array env lid =
  match lookup_qname env lid with 
    | Some (Sig_tycon(_, _, _, _, _, tags)) -> 
        Util.for_some (function 
            | Logic_array _ -> true 
            | _ -> false) tags 
    | _ -> false

let is_record env lid =
  match lookup_qname env lid with 
    | Some (Sig_tycon(_, _, _, _, _, tags)) -> 
        Util.for_some (fun t -> t=Logic_record) tags 
    | _ -> false

let lookup_datacons_of_typ (env:env) lid = 
  match lookup_qname env lid with 
    | Some (Sig_tycon(_, _, _, _, datas, _)) -> Some (List.map (fun l -> (l, lookup_lid env l)) datas)
    | _ -> None
    
let lookup_typ_abbrev env lid =
  match lookup_qname env lid with 
    | Some (Sig_typ_abbrev (lid, tps, _, t)) -> Some (Util.close_with_lam tps t)
    | _ -> None
        
let lookup_btvdef env (btvd:btvdef): option<kind> = 
  Util.find_map env.gamma (function
    | Binding_typ (id, k) when Util.bvd_eq id btvd -> Some k
    | _ -> None)  
    
let lookup_btvar env btv = 
  match lookup_btvdef env btv.v with
    | None -> raise (Not_found_binding(env, Inl (Typ_btvar btv)))
    | Some k -> k 

let lookup_typ_lid env (ftv:lident) : kind = 
  match lookup_qname env ftv with
    | Some (Sig_tycon (lid, tps, k, _, _, _)) 
    | Some (Sig_typ_abbrev (lid, tps, k, _)) -> 
      Util.close_kind tps k
    | _ ->
      raise (Not_found_binding(env, Inl (Util.ftv ftv)))

let lookup_operator env (opname:ident) = 
  let primName = lid_of_path ["Prims"; ("_dummy_" ^ opname.idText)] dummyRange in
    lookup_lid env primName
      
let rec push_sigelt env s : env = 
  match s with 
    | Sig_bundle(ses) -> List.fold_left push_sigelt env ses 
    | _ -> {env with gamma=Binding_sig s::env.gamma}
        
let push_local_binding env b = {env with gamma=b::env.gamma}
      
let uvars_in_env env = List.collect (function
  | Binding_var(_, t) -> Util.uvars_in_typ t
  | Binding_typ(_, k) -> Util.uvars_in_kind k
  | _ -> []) env.gamma

let push_module env (m:modul) = 
    add_sigelts env m.exports;
    {env with 
      modules=m::env.modules; 
      gamma=[];
      expected_typ=None}

let set_expected_typ env t = {env with expected_typ = Some t}
let expected_typ env = env.expected_typ
let clear_expected_typ env = {env with expected_typ=None}, env.expected_typ

let fold_env env f a = List.fold_right (fun e a -> f a e) env.gamma a

let idents env : (list<btvdef> * list<bvvdef>) = 
  fold_env env (fun (tvs, xvs) b -> match b with 
    | Binding_var(x, _) -> (tvs, x::xvs)
    | Binding_typ(a, _) -> (a::tvs, xvs)
    | _ -> (tvs, xvs)) ([],[])

let lidents env : list<lident> =
  let keys = List.fold_left (fun keys -> function 
    | Binding_sig s -> Util.lids_of_sigelt s@keys
    | _ -> keys) [] env.gamma in
  Util.smap_fold env.sigtab (fun _ v keys -> Util.lids_of_sigelt v@keys) keys  
    
let quantifier_pattern_env env t = 
  let vars, _ = Util.collect_forall_xt t in
  let vars = match vars with 
    | [] -> fst (Util.collect_exists_xt t)
    | _ -> vars in
  List.fold_left (fun env -> function
    | Inr (x, t) -> push_local_binding env (Binding_var(x, t))
    | Inl (a, k) -> push_local_binding env (Binding_typ(a, k))) env vars 
