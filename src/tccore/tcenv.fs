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

module FStar.Tcenv

open Absyn
open AbsynUtils
open Util
open Const
open Profiling

let lid_ctr = new_counter "lookup_lid"
let bvar_ctr = new_counter "lookup_bvar"
let btvar_ctr = new_counter "lookup_btvar"
let vd_ctr = new_counter "lookup_val_decl"
let fvar_ctr = new_counter "lookup_fvar"
let tc_ctr = new_counter "lookup_typ_const"
let ta_ctr = new_counter "lookup_typ_abbrev"

type binding =
  | Binding_var of ident * typ
  | Binding_typ of ident * kind
  | Binding_match of exp * exp
  | Binding_tmatch of btvar * typ

type sigtable = HashMultiMap<string, sigelt>

let rec strlid_of_sigelt se = match se with
  | Sig_tycon_kind(lid, _, _, _, _, _)
  | Sig_typ_abbrev(lid, _, _, _)
  | Sig_record_typ(lid, _, _, _, _)
  | Sig_datacon_typ(lid, _, _, _, _, _, _, _)
  | Sig_logic_function(lid, _, _)
  | Sig_extern_value(_, lid, _)
  | Sig_query(lid, _)
  | Sig_ghost_assume(lid, _, _)
  | Sig_value_decl(lid, _) -> Sugar.text_of_lid lid
  | Sig_extern_typ(eref, s) -> strlid_of_sigelt s
  | _ -> raise Impos

let is_sig_typ = function
    Sig_tycon_kind _
  | Sig_typ_abbrev _
  | Sig_record_typ _
  | Sig_extern_typ _ -> true
  | _ -> false

let signature_to_sigtables s =
  let ht = Hashtbl.create 100 in
  let ht_typ = Hashtbl.create 100 in
  let _ = List.iter (fun se ->
                       let key = (strlid_of_sigelt se) in
                         if is_sig_typ se then Hashtbl.add ht_typ key se
                         else Hashtbl.add ht key se) s in
    ht, ht_typ

let modules_to_sigtables mods =
  signature_to_sigtables (List.concat (List.map (fun (_,m) -> m.signature) mods))

type phase = | TC | DEREFINE
type env = {
  range:Range.range;
  phase:phase;
  curmodule: lident;             (* Name of this module---the "principal" subscript *)
  gamma:list<binding>;           (* Main typing environment *)
  externs: signature;            (* Extern declarations accumulated from other modules *)
  e_signature: signature;        (* Type and data constructors for this module *)
  curunit: lident;               (* the name of the current top-level function unit *)
  in_typ_decl: bool;             (* are we currently checking a type declaration*)
  modules:list<lident * modul>;  (* already fully type checked modules *)
  expected_typ:option<typ>;
  recall_expected_typ:option<typ>;
  expected_kind:option<kind>;
  expect_tyapps:bool;
  current_value:option<exp>;
  solver:option<solver>;
  kind_level:bool;
  sigtab:sigtable;
  sigtab_typ:sigtable;
  extern_typ:bool;
  expand_externs:bool;
  object_invariants:bool;
  skip_kinding:bool;
  uvars:list<uvar>;
  annot:option<string>;
}
and solver = {solver_toggle_caching: unit -> unit;
              solver_query: env -> typ -> bool;
              solver_query_equiv: env -> exp -> exp -> bool;
              solver_discharge_proof: env -> typ -> option<exp>}

let add_sigelts_to_env (env:env) ses =
  let _ = List.iter (fun se ->
                       let key = (strlid_of_sigelt se) in
                         if is_sig_typ se then Hashtbl.add env.sigtab_typ key se
                         else Hashtbl.add env.sigtab key se) ses in
    ()

let in_tc_phase env = env.phase=TC
let set_tc_phase env = {env with phase=TC}
let in_derefinement_phase env = env.phase = DEREFINE
let set_derefinement_phase env = {env with phase=DEREFINE}


let mk_env () =
  { range=Absyn.dummyRange;
    phase=TC;
    curmodule=asLid [];
    curunit=asLid [];
    in_typ_decl=false;
    gamma= [];
    externs=[];
    e_signature= [];
    modules= [];
    expected_typ=None;
    recall_expected_typ=None;
    expected_kind=None;
    expect_tyapps= false;
    current_value=None;
    solver=None;
    kind_level=false;
    sigtab=Hashtbl.create 100;
    sigtab_typ=Hashtbl.create 300;
    extern_typ=false;
    expand_externs=true;
    object_invariants=false;
    skip_kinding=false;
    uvars=[];
    annot=None;
  }

let empty_env =  mk_env ()

let set_kind_level env = {env with kind_level=true}
let is_kind_level env = env.kind_level

let set_solver env s = {env with solver = Some s}
let use_solver env = match env.solver with None -> false | Some _ -> true
let get_solver env = env.solver
let clear_solver env = {env with solver = None}

let modules env = env.modules
let signature env = env.e_signature
let current_module env = env.curmodule
let set_current_module env lid = {env with curmodule=lid}

let current_unit env = env.curunit
let set_current_unit env lid = {env with curunit=lid}

let set_in_typ_decl env = {env with in_typ_decl=true}
let in_typ_decl env = env.in_typ_decl
let clear_in_typ_decl env = {env with in_typ_decl=false}

(* let W t = withsort t Kind_unknown *)
let set_range e r = {e with range=r}
let get_range e = e.range

let initial_env module_lid solver =
  let ds_env = DesugarEnv.initial_env [] module_lid in
  let open_mods = DesugarEnv.open_modules ds_env in
  let sigtab, sigtab_typ = modules_to_sigtables open_mods in
    {range=Absyn.dummyRange;
     phase=TC;
     curmodule = DesugarEnv.current_module ds_env;
     curunit=asLid [];
     in_typ_decl=false;
     gamma=[];
     externs=[];
     e_signature=[];
     modules=open_mods;
     expected_typ=None;
     recall_expected_typ=None;
     expect_tyapps = false;
     expected_kind=None;
     current_value=None;
     solver=Some solver;
     kind_level=false;
     sigtab=sigtab;
     sigtab_typ=sigtab_typ;
     extern_typ=false;
     expand_externs=true;
     object_invariants=false;
     skip_kinding=false;
     uvars=[];
     annot=None
    }

let find_in_sigtabs env key =
  match Hashtbl.tryfind env.sigtab key with
    | Some s -> Some s
    | None -> Hashtbl.tryfind env.sigtab_typ key
let find_in_sigtab env key =  Hashtbl.tryfind env.sigtab key
let find_in_sigtab_typ env key =  Hashtbl.tryfind env.sigtab_typ key

exception Not_found_binding of env * Disj<typ',exp'>
exception Assertion_failure

let assert_eq v1 v2 =
  if v1=v2 then ()
  else
    (printfn "%A" v1;
     printfn "%A" v2;
     raise Assertion_failure)

let lookup_bvar_ident env (rn:ident) : option<typ> =
  try
    let b = List.find
      (function
         | Binding_var (id, t) when id.idText = rn.idText -> true
         | _ -> false) env.gamma in
      match b with
          Binding_var (_,t) -> Some t
        | _ -> raise Impos
  with _ -> None

let lookup_bvar env bv =
  let rn:ident = (bvar_real_name bv) in
    match lookup_bvar_ident env rn with
      | None -> raise (Not_found_binding(env, Inr (Exp_bvar bv)))
      | Some t -> t

let lookup_val_decl env lid =
  let find_vd path = function
    | Sig_extern_value(_, lid, _)
    | Sig_value_decl (lid, _) when (Sugar.path_of_lid lid)=path -> true
    | _ -> false in
    try
      match List.find (find_vd (Sugar.path_of_lid lid)) (env.externs@env.e_signature) with
        | Sig_value_decl (_, t)
        | Sig_extern_value(_, _, t) -> t
        | _ -> raise Impos
    with
      | :? System.Collections.Generic.KeyNotFoundException ->
        raise (Not_found_binding (env, Inr (Exp_fvar (fvwithpos lid (Sugar.range_of_lid lid), None))))

let err_t s ftv = Inl (Typ_const (fvwithsort ftv s, None))
let err_e s fv = Inr (Exp_fvar (fvwithsort fv s, None))

let lookup_qname env (lid:lident) pred err =
  let err () = raise (Not_found_binding (env, err lid)) in
  let rec finder lid = function
      [] -> None
    | hd::tl -> match pred lid hd with
        | None -> finder lid tl
        | Some x -> Some x in
  let module_name, id = Util.pfx lid.lid in
  let resultOpt =
    if Sugar.lid_equals (asLid module_name) env.curmodule then
      finder lid env.e_signature
    else
      let (_, modul) =
        (try
           List.find (fun (lid, modul) -> Sugar.lid_equals lid (asLid module_name)) env.modules
         with
             _ -> err ()) in
        finder lid modul.signature  in
    match resultOpt with
        None -> (match finder lid env.externs with
                     None -> err ()
                   | Some x -> x)
      | Some x -> x

let __datacon_typ_from_tparams allow_term_params tps t : (typ * list<tparam>) =
  let out = (t,[]) |> List.fold_right
      (fun tp (t, params) -> match tp with
         | Tparam_typ (bvd,k) -> twithsort (Typ_univ (bvd, k, [], t)) Kind_star, params
         | Tparam_term (bvd, bv_t) when allow_term_params ->
             let nbvd = mkbvd (pp_name bvd, genident None) in
             let nbv = ewithsort (Exp_bvar (bvd_to_bvar_s nbvd bv_t)) bv_t in
             let t = substitute_exp t bvd nbv in
               t, (Tparam_term(nbvd, bv_t)::params)
         | _ -> raise (NYI "Extraneous term indices")) tps in
    out

let dcon_type_from_tparams tps t =
  fst(__datacon_typ_from_tparams true tps t)

let lookup_lid env lid =
  let rec finder lid' = function
    | Sig_datacon_typ (lid, tps, t, _, aq, _, _, _) when Sugar.lid_equals lid lid' ->
        let t, _ = __datacon_typ_from_tparams false tps t in
          Some t
    | Sig_logic_function(lid, t, _)
    | Sig_extern_value(_, lid, t)
    | Sig_value_decl (lid, t) when Sugar.lid_equals lid lid' -> Some t
    | Sig_extern_typ (eref, s) as ss -> finder lid' s
    | _ -> None
  in
    lookup_qname env lid finder (err_e (Wt Typ_unknown))


let lookup_fvar env (fv:var<typ>) =
  let key = Sugar.text_of_lid fv.v in
  let rec extract = function
    | Sig_datacon_typ (lid, tps, t, _, aq, _, _, _) ->
        let t, _ = __datacon_typ_from_tparams false tps t in
          Some t
    | Sig_logic_function(lid, t, _)
    | Sig_extern_value (_, lid, t)
    | Sig_value_decl (lid, t) -> Some t
    | Sig_extern_typ(_, s) -> extract s
    | _ -> None in
    bind_opt (find_in_sigtabs env key) extract

let lookup_fvar_with_params env (fv:var<typ>) =
  let key = Sugar.text_of_lid fv.v in
  let rec extract = function
    | Sig_datacon_typ (lid, tps, t, _, aq, _, _, _) ->
        let out = __datacon_typ_from_tparams true tps t in
          Some out
    | Sig_logic_function(lid, t, _)
    | Sig_extern_value(_, lid, t)
    | Sig_value_decl (lid, t) -> Some (t, [])
    | Sig_extern_typ (_, s) -> extract s
    | _ -> None in
    bind_opt (find_in_sigtabs env key) extract

let is_datacon env (fv:var<typ>) =
  let key = Sugar.text_of_lid fv.v in
  let rec is_dc = function
    | Sig_logic_function _
    | Sig_datacon_typ _ -> true
    | Sig_extern_typ(_, s) -> is_dc s
    | _ -> false in
    match Hashtbl.tryfind env.sigtab key with
      | Some s -> is_dc s
      | None -> false

let is_logic_function env (fv:var<typ>) =
  let key = Sugar.text_of_lid fv.v in
  let rec is_lf = function
    | Sig_logic_function _ -> true
    | _ -> false in
    match Hashtbl.tryfind env.sigtab key with
      | Some s -> is_lf s
      | None -> false

let is_logic_data env (tc:lident) =
  let key = Sugar.text_of_lid tc in
  let rec is_ld = function
    | Sig_tycon_kind(_, _, _, _, _, tags) ->
        List.exists (fun t -> t=Sugar.Logic_data) tags
    | _ -> false in
    match Hashtbl.tryfind env.sigtab_typ key with
      | Some s -> is_ld s
      | None -> false

let is_logic_array env (tc:lident) =
  let key = Sugar.text_of_lid tc in
  let rec is_ld = function
    | Sig_tycon_kind(_, _, _, _, _, tags) ->
        List.exists (function Sugar.Logic_array _ -> true | _ -> false) tags
    | _ -> false in
  match Hashtbl.tryfind env.sigtab_typ key with
    | Some s -> is_ld s
    | None -> false

let is_record env (tc:lident) =
  let key = Sugar.text_of_lid tc in
  let rec is_rec = function
    | Sig_record_typ _ -> true
    | _ -> false in
    match Hashtbl.tryfind env.sigtab_typ key with
      | Some s -> is_rec s
      | None -> false


let is_prop env t =
  match get_tycon t with
    | Some (Typ_const (tc, _)) ->
        let lid = tc.v in
          (match Hashtbl.tryfind env.sigtab_typ (Sugar.text_of_lid lid) with
             | Some (Sig_tycon_kind(_, _, _, prop, _, _)) -> prop
             | _ -> false)
    | Some (Typ_btvar _) -> true
    | _ -> false

let lookup_field_name env fn =
  let rec finder full_lid = function
    | Sig_record_typ (_, tps, _, {v=Typ_record(fn_t_l, _)}, _) ->
        (try
           let (fn,t) = List.find
             (fun (fn,t) -> Sugar.lid_equals full_lid fn) fn_t_l in
             Some (tps, t)
         with
             _ -> None)
    | _ -> None
  in
    lookup_qname env fn finder (err_e (Wt Typ_unknown))

let field_name_exists env fn =
  try
    let _ = lookup_field_name env fn in
      true
  with
      Not_found_binding _ -> false

let tycon_kind_from_tparams tps k =
  let tyK = List.fold_right
          (fun tp k -> match tp with
             | Tparam_typ (a, k') ->  (Kind_tcon(Some a, k', k))
             | Tparam_term (x, t) ->  (Kind_dcon(Some x, t, k))) tps k in
    tyK

let lookup_record_typ env fn =
  let rec finder fn = function
    | Sig_record_typ (lident, tps, _, ({v=Typ_record(fn_t_l, _)} as t), eref) ->
        (try
           let _ = List.find
             (fun (fn',_) -> Sugar.lid_equals fn' fn) fn_t_l in
           let tK = tycon_kind_from_tparams tps t.sort in
           let var_abbrv = fvwithsort lident tK in
           let tabbrv = twithsort (Typ_const(var_abbrv, eref)) tK in
             Some (lident, tabbrv, tps, t)
         with
             _ -> None)
    | Sig_extern_typ(_, s) -> finder fn s
    | _ -> None
  in
    lookup_qname env fn finder (err_e (Wt Typ_unknown))

let genid_ctr = new_counter "LTA.genident"
let hash_ctr = new_counter "LTA.hashtbl.tryfind"
let extract_ctr = new_counter "LTA.extract"
let lookup_typ_abbrev =
  (* let cache = Hashtbl.create 1000 in *)
    fun env (ftv:var<kind>) ->
      let key = ftv.v.str in
      let rec extract = function
        | Sig_typ_abbrev (lid, [], _, t) -> Some ({t with p=ftv.p})
        | Sig_typ_abbrev (lid, tps, _, t) ->
            (* let benv, tps' =  *)
            (*   List.fold_right (fun tp (benv, tps) -> match tp with  *)
            (*                      | Tparam_typ (bvd, k) -> *)
            (*                          let newname = genid () in *)
            (*                          let bvd' = newname,newname in *)
            (*                            (bvd, bvd')::benv, Tparam_typ(bvd', k)::tps *)
            (*                      | Tparam_term (bvd, t) -> *)
            (*                          let newname = genid () in *)
            (*                          let bvd' = newname,newname in *)
            (*                            (bvd, bvd')::benv, Tparam_term(bvd', t)::tps) tps ([],[]) in *)
            (* let t' = freshen_typ t benv in *)
            let t =
              List.fold_right (fun tp out -> match tp with
                                 | Tparam_typ (bvd, k) ->
                                     twithinfo (Typ_tlam(bvd,k,out)) (Kind_tcon(Some bvd, k, out.sort)) ftv.p
                                 | Tparam_term (bvd, t) ->
                                     twithinfo (Typ_lam(bvd,t,out)) (Kind_dcon(Some bvd, t, out.sort)) ftv.p)
                tps {t with p=ftv.p} in
              Some(t)
        | Sig_extern_typ(eref, s) ->
            if env.expand_externs then extract s else None
        | _ -> None in
        (* match Hashtbl.tryfind cache key with  *)
        (*   | Some t -> t *)
        (*   | _ ->  *)
        match Hashtbl.tryfind env.sigtab_typ key with
          | None -> None
          | Some s ->
              let t = extract s in
                (* Hashtbl.add cache key t;  *)t

let rec lookup_record_typ_by_name env recname =
  let rec finder recname = function
    | Sig_record_typ (lident, tps, _, ({v=Typ_record(fn_t_l, _)} as t), eref) when Sugar.lid_equals lident recname ->
        let tK = tycon_kind_from_tparams tps t.sort in
        let var_abbrv = fvwithsort lident tK in
        let tabbrv = twithsort (Typ_const (var_abbrv, eref)) tK in
          Some (lident, tabbrv, tps, t)
    | Sig_extern_typ(_, s) -> finder recname s
    | Sig_typ_abbrev(lid, tps, k, t) when Sugar.lid_equals lid recname ->
        (* pr "^^^^Found type abbrev for %A\n" lid; *)
        let var_abbrv = fvwithsort recname k in
        let tabbrv = twithsort (Typ_const (var_abbrv, None)) k in
          (*           pr "Looking up type abbreviation for %s\n" (Pretty.str_of_lident lid); *)
          (match lookup_typ_abbrev env var_abbrv with
             | Some(t) ->
                 (* pr "^^^^^ Expanded abbrev %A\n" t; *)
                 let rec elim_affine_refinement t = match t.v with
                   | Typ_refine(_, t, _, _)
                   | Typ_affine t -> elim_affine_refinement t
                   | Typ_record _ -> Some (lid, tabbrv, [], t)
                   | Typ_const (v, _)  -> Some (lookup_record_typ_by_name env v.v)
                   | _ -> None in
                   elim_affine_refinement t
             | _ -> None)
    | _ -> None
  in
  lookup_qname env recname finder (err_e (Wt Typ_unknown))

let get_record_fields p env torig =
  let err topt = match topt with
    | None -> raise (Error (spr "Expected a record type; got %s" (Pretty.strTyp torig), p))
    | Some t -> raise (Error (spr "Expected a record type; got %s" (Pretty.strTyp t), p)) in
  let rec aux (tparams, eparams) t = match t.v with
    | Typ_record(fn_t_l, _) -> if not (List.isEmpty tparams) || not (List.isEmpty eparams) then
        raise (Error( "Unexpected parameters in a record type", p)) else fn_t_l
    | Typ_const (v, _) ->
        (match lookup_typ_abbrev env v with
           | Some (t) ->
               let tformals = [] in
                 (* if (List.length tparams <> 0) || (List.length eparams <> 0) *)
                 (* then (failwith (spr "Looking up record %s\n reached %s\ngot tparms=%s\n" (Pretty.strTyp torig) (Pretty.strTyp t) (String.concat ", " (List.map Pretty.strTyp tparams)))); *)
                 let t = instantiate_tparams t tformals tparams eparams in
                   aux ([],[]) t
           | None ->
               let (_, _, tformals, rectype) = lookup_record_typ_by_name env v.v in
                 (* TODO: Fix this, tparams and eparams can be interleaved now. *)
                 (* assert (List.length tformals = (List.length tparams + List.length eparams)); *)
                 let inst_rectype = instantiate_tparams rectype tformals tparams eparams in
                   (match inst_rectype.v with
                      | Typ_record(fn_t_l, _) -> fn_t_l
                      | _ -> err (Some inst_rectype) ))
    | Typ_refine(_, t, _, _)
    | Typ_affine t -> aux (tparams, eparams) t
    | Typ_app(t, t') -> aux  (t'::tparams, eparams) t
    | Typ_dep(t, e) -> aux (tparams,  e::eparams) t
    | _ -> err (Some t) in
  try aux ([],[]) torig
  with Not_found_binding _ -> err None


let lookup_btvar_ident env (rn:ident): option<kind> =
  try
    let b = List.find
      (function
         | Binding_typ (id, k) when id.idText = rn.idText -> true
         | _ -> false) env.gamma in
      match b with
          Binding_typ (_,k) -> Some k
        | _ -> raise Impos
  with _ -> None

let lookup_btvar env btv =
  let rn:ident = bvar_real_name btv in
    match lookup_btvar_ident env rn with
        None -> raise (Not_found_binding(env, Inl (Typ_btvar btv)))
      | Some k -> k

let lookup_typ_lid env (ftv:lident) =
  let rec tycon_kind_from_sig = function
    | Sig_tycon_kind (lid, tps, k, _, _, _) ->
        tycon_kind_from_tparams tps k

    | Sig_record_typ (lid, tps, _, t, _)
    | Sig_typ_abbrev (lid, tps, _, t) ->
        tycon_kind_from_tparams tps t.sort

    | Sig_extern_typ(lang, s) -> tycon_kind_from_sig s

    | _ ->  Kind_unknown in
    match Hashtbl.tryfind env.sigtab_typ (Sugar.text_of_lid ftv) with
      | Some s -> tycon_kind_from_sig s
      | None ->  Kind_unknown

let lookup_typ_const env (ftv:var<kind>) = lookup_typ_lid env ftv.v

let lookup_operator env (opname:ident) =
  let primName = Wfv (Sugar.lid_of_path ["Prims"; ("_dummy_" ^ opname.idText)] dummyRange) in
    lookup_fvar env primName


let push_sigelt : env -> sigelt -> env =
  fun env s ->
    let lid = strlid_of_sigelt s in
    let _ =
      if is_sig_typ s then Hashtbl.add env.sigtab_typ lid s
      else Hashtbl.add env.sigtab lid s in
      {env with e_signature=s::env.e_signature}

let push_local_binding env b =
  let check_typ_unknown e =
    exp_fold_map
      (fun () () -> function
           Typ_unknown -> raise (Bad "Found unknown typ")
         | t -> (), t, None)
      (fun () () e -> match e with
           Exp_fvar (v, _) ->
             (match v.sort.v with
                | Typ_unknown -> raise (Bad "Found unknown typ")
                | _ -> (), e)
         | _ -> (), e)
      (fun _ e -> e)
      Absyn.ignore_env
      () () e in
  let uvars, b = match b with
    | Binding_var(x,t) -> uvars_in_typ t, b
    | Binding_match(e1, e2) ->
        (* let _ = pr ">>>>>>>>>Match:\n----%s\n----%s\n" (Pretty.strTyp e1.sort) (Pretty.strTyp e2.sort) in *)
          [], Binding_match(unascribe e1, unascribe e2)
    | Binding_tmatch(_, t2) -> (uvars_in_typ t2), b
    | _ -> [],b in
  let env = {env with gamma=b::env.gamma; uvars=uvars@env.uvars} in
    env

let push_local_binding_fast env b =
  let check_typ_unknown e =
    exp_fold_map
      (fun () () -> function
           Typ_unknown -> raise (Bad "Found unknown typ")
         | t -> (), t, None)
      (fun () () e -> match e with
           Exp_fvar (v, _) ->
             (match v.sort.v with
                | Typ_unknown -> raise (Bad "Found unknown typ")
                | _ -> (), e)
         | _ -> (), e)
      (fun _ e -> e)
      Absyn.ignore_env
      () () e in
  let b = match b with
    | Binding_match(e1, e2) -> Binding_match(unascribe e1, unascribe e2)
    | _ -> b in
  let env = {env with gamma=b::env.gamma} in
    env

let uvars_in_env env = List.concat (List.map uvars_in_uvar env.uvars)

let push_module : env -> modul -> env =
  fun env m ->
    let _ = add_sigelts_to_env env m.signature in
    let externs = List.filter (function
                                 | Sig_extern_value _
                                 | Sig_extern_typ _ -> true
                                 | _ -> false) m.signature in
      {env with
         modules=(m.name,m)::env.modules;
         externs=externs@env.externs;
         e_signature=[]}

let clear_current_state : env -> env =
  fun env ->
    let sigtab, sigtab_typ = modules_to_sigtables env.modules in
      {empty_env with
         modules=env.modules;
         sigtab=sigtab;
         sigtab_typ=sigtab_typ;
         e_signature=[]}

let set_expected_typ : env -> typ -> env =
  fun env t -> {env with expected_typ = Some t; recall_expected_typ=Some t}

let expected_typ : env -> option<typ> =
  fun env -> env.expected_typ

let clear_expected_typ : env -> (env * option<typ>) =
  fun env -> {env with expected_typ=None; recall_expected_typ=env.expected_typ}, env.expected_typ

let recall_expected_typ : env -> option<typ> =
  fun env -> env.recall_expected_typ

let set_expected_kind : env -> kind -> env =
  fun env t -> {env with expected_kind = Some t}

let expected_kind : env -> option<kind> =
  fun env -> env.expected_kind

let clear_expected_kind : env -> (env * option<kind>) =
  fun env -> {env with expected_kind=None}, env.expected_kind

(* open coding the monad here for efficiency *)
let stfold (e:env) (f:binding -> state<'s,unit>) state =
  let rec aux l state = match l with
    | [] -> ((), state)
    | hd::tl ->
        let _, state = f hd state in
          aux tl state
  in aux e.gamma state

(* open coding the monad here for efficiency *)
let stfoldr (e:env) (f:env -> binding -> state<'s,unit>) state =
  let rec aux l state = match l with
    | [] -> ((), state)
    | hd::tl ->
        let _, state = aux tl state in
          f {e with gamma=tl} hd state
  in aux e.gamma state

let fold_env : env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env f a -> List.fold_right (fun e a -> f a e) env.gamma a

let find env f =
  try
    let b = List.find f env.gamma in
      Some b
  with
    | :? System.Collections.Generic.KeyNotFoundException -> None


let set_expect_tyapps env = {env with expect_tyapps=true}
let clear_expect_tyapps env = {env with expect_tyapps=false}
let expect_tyapps env = env.expect_tyapps
let set_current_value env v = {env with current_value=Some v}
let current_value env = env.current_value
let clear_current_value env = {env with current_value=None}

let dump (env:env) = printfn "%A" env

let freevars_not_in_env env t =
  let ftvs, fxvs = freevarsTyp t in
  let tvs_not_in_env = (List.filter
       (fun tv -> match lookup_btvar_ident env (bvar_real_name tv) with
            None -> true
          | Some _ -> false) ftvs) in
  let xvs_not_in_env =
   (List.filter
      (fun xv -> match lookup_bvar_ident env (bvar_real_name xv) with
           None -> true
         | Some _ -> false) fxvs) in
    tvs_not_in_env, xvs_not_in_env

let expand_typ_once env t =
  let rec typ_const_and_params out t = match t.v with
      Typ_const (fv, _) -> Some ((fv, out), fun t -> t)
    | Typ_app (t1, t2) ->
        (match typ_const_and_params (Inl t2::out) t1 with
           | None -> None
           | Some (args, builder) -> Some (args, fun t' -> twithinfo (Typ_app(builder t', t2)) t.sort t.p))
    | Typ_dep (t1, e) ->
        (match typ_const_and_params (Inr e::out) t1 with
           | None -> None
           | Some (args, builder) -> Some (args, fun t' -> twithinfo (Typ_dep(builder t', e)) t.sort t.p))
    | _ -> None in
  let t = compress t in
  let c_parms_opt = typ_const_and_params [] t in
    match c_parms_opt with
      | None -> t
      | Some ((fv, actuals), builder) ->
          match lookup_typ_abbrev env fv with
              None -> t
            | Some (e_typ) ->
                (* builder e_typ *)
                let subst, typ =
                  List.fold_left
                    (fun (subst, typ) arg -> match typ.sort(* .u *), arg with
                       | Kind_tcon(None, _, k'), Inl t ->
                           subst, twithsort (Typ_app(typ, t)) k'
                       | Kind_tcon(Some a, k, k'), Inl t ->
                           (Inl(a, t)::subst), twithsort (Typ_app(typ, t)) k'
                       | Kind_dcon(None, _, k), Inr e ->
                           subst, twithsort (Typ_dep(typ, e)) k
                       | Kind_dcon(Some x, _, k), Inr e ->
                           (Inr (x, e)::subst), twithsort (Typ_dep(typ, e)) k
                       | _ -> raise (Err "Ill-formed typ abbrev application should be ruled out by kinding")) ([], e_typ) actuals in
                  substitute_l_typ_or_exp typ subst
                    (* | Some (formals, e_typ) ->  *)
                    (*     if List.length formals <> List.length actuals then  *)
                    (*       let msg = spr "Expand_typ failed on %s\nApplication of type constructor %s with an unexpected number of parameters"  *)
                    (*         (Pretty.strTyp t) (Sugar.text_of_lid fv.v) in *)
                    (*         raise (Err msg) *)
                    (*     else *)
                    (*       let fa = List.zip formals actuals in *)
                    (*       let subst = List.fold_left  *)
                    (*         (fun subst -> function *)
                    (*            | Tparam_typ(bvd, k), Inl t ->  *)
                    (*                (bvd, Inl t)::subst *)
                    (*            | Tparam_term(bvd, t), Inr e ->  *)
                    (*                (bvd, Inr e)::subst *)
                    (*            | _ -> raise (Err "Ill-formed typ abbrev application should be ruled out by kinding")) [] fa in *)
                    (*         substitute_l_typ_or_exp e_typ subst  *)

let rec expand_typ_until_pred env torig p =
  let rec simplify t = match t.v with
    | Typ_dep(t', e) ->
        let t' = simplify t' in
          (match t'.v with
             | Typ_lam _ -> simplify (open_typ_with_exp t' e)
             | _ -> twithinfo (Typ_dep(t', e)) t.sort t.p)
    | Typ_app(t1,t2) ->
        let t1 = simplify t1 in
          (match t1.v with
             | Typ_tlam _ -> simplify (open_typ_with_typ t1 t2)
             | _ -> twithinfo (Typ_app(t1,t2)) t.sort t.p)

    | _ -> t in
  let torig = simplify torig in
    if p torig then Some torig
    else
      let t = expand_typ_once env torig in
        if LanguagePrimitives.PhysicalEquality torig t
        then None
        else expand_typ_until_pred env (alpha_convert t) p

let rec expand_typ_until env torig lid =
  expand_typ_until_pred env torig (fun t ->
                                     match AbsynUtils.flattenTypAppsAndDeps t with
                                       | {v=Typ_const(tc,_)}, _ -> Sugar.lid_equals tc.v lid
                                       | _ -> false)

let rec expand_typ env torig =
  let t' = expand_typ_once env torig in
    if LanguagePrimitives.PhysicalEquality torig t'
    then torig
    else expand_typ env t'

let expand_typ_fix env t = expand_typ env t

let expand_typ_rec env t =
  let et () t = (), (expand_typ env (twithpos t dummyRange)).v in
  let ee () e = (), e in
    snd (descend_typ_map et ee () t)

let expand_exp_rec env e =
  let et () t = (), (expand_typ env (twithpos t dummyRange)).v in
  let ee () e = (), e in
    snd (descend_exp_map et ee () e)

let get_sigtab_keys env =
  let keys = Hashtbl.fold (fun key value out -> key::out) env.sigtab [] in
    Hashtbl.fold (fun key value out -> key::out) env.sigtab_typ keys

let set_extern_typ env = {env with extern_typ=true}
let extern_typ env = env.extern_typ
let clear_extern_typ env = {env with extern_typ=false}
let clear_expand_externs env = {env with expand_externs=false}
let set_expand_externs env = {env with expand_externs=true}

let patternEnv env t =
  let vars, _ = AbsynUtils.collect_forall_xt t in
  let vars = match vars with
    | [] -> fst (AbsynUtils.collect_exists_xt t)
    | _ -> vars in
  List.fold_left (fun env -> function
    | Inr (x, t) -> push_local_binding_fast env (Binding_var(x.realname, t))
    | Inl (a, k) -> push_local_binding_fast env (Binding_typ(a.realname, k))) env vars

let lookup_datatype (env:env) lid =
    match lookup_typ_lid env lid with
        | Kind_unknown -> None
        | _ ->
        let datacons =
            env.sigtab.Fold (fun key sigelt out -> match sigelt with
                                | Absyn.Sig_datacon_typ(_, _, _, _, _, Some lid', _, _) ->
                                    if Sugar.lid_equals lid lid'
                                    then sigelt::out
                                    else out
                                | _ -> out) [] in
            Some datacons

let bindings e =
  (e.gamma |> List.collect (function Binding_var(id, _) -> [id.idText] | Binding_typ(id, _) -> ["'"^id.idText] | _ -> []))
        |> String.concat ", "
