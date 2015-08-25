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

module FStar.Tcutil

open Absyn
open AbsynUtils
open Util
open Tcenv
open Profiling
open KindAbbrevs

let print_not_found = function
  | Not_found_binding (env, Inl t) ->
      Printf.printf "(Compiler bug?) Type name not found: %s\n" (Pretty.strTyp (twithpos t dummyRange))
  | Not_found_binding (env, Inr e) ->
      Printf.printf "(Compiler bug?) Variable not found: %s\n" (Pretty.strExp (ewithpos e dummyRange))

let handleable e = match e with
  | Error _ -> true && !Options.suppress_trace
  | Not_found_binding _ -> print_not_found e; false  (* all bindings should have been resolved already! *)
  | _ -> false

let handle_err warning ret e =
(*   if warning then Printf.printf "\nWARNING: " else Printf.printf "\nERROR: "; *)
  match e with
    | Not_found_binding (env, Inl t) ->
        Printf.printf "(Compiler bug?) Type name not found: %s\n" (Pretty.strTyp (twithpos t dummyRange));
//        Printf.printf "query %d\n" !Proof.queryCount;
        ret
    | Not_found_binding (env, Inr e) ->
        Printf.printf "(Compiler bug?) Variable not found: %s\n" (Pretty.strExp (ewithpos e dummyRange));
//        Printf.printf "query %d\n" !Proof.queryCount;
        ret
    | Error(msg, r) ->
        Util.err "%s : %s : %s\n" (Range.string_of_range r) (if warning then "Warning" else "Error") msg;
        ret
    | NYI s when warning ->
        Printf.printf "Not yet implemented feature: %s" s; ret
    | e when warning && not(!Options.proof_term_errs) -> (printfn "%A" e; ret)

let terr env t1 t2 exp =
  let msg =
    Printf.sprintf "Expected an expression of type:\n\n%s\n\nbut got (%s):\n\n%s"
      (Pretty.strTyp (expand_typ env t1))
      (Pretty.strExp exp)
      (Pretty.strTyp (expand_typ env t2)) in
    raise (Error (msg, exp.p))

let terr_p env t1 t2 p =
  let msg =
    Printf.sprintf "Expected an expression of type:\n\n%s\n\nbut got %s"
      (Pretty.strTyp (expand_typ env t1))
      (Pretty.strTyp (expand_typ env t2)) in
    raise (Error (msg, p))

type affines = list<bvvar>

let rec is_tuple_typ t = match t.v with
  | Typ_dtuple _ -> true
  | Typ_affine t
  | Typ_refine (_, t, _, _) -> is_tuple_typ t
  | _ -> false

let rec is_non_variable_value env e = match e.v with
  | Exp_fvar (fv,_) -> Tcenv.is_datacon env fv
  | Exp_constant _
  | Exp_abs _
  | Exp_tabs _ -> true
  | Exp_ascribed(e,_,_) -> is_non_variable_value env e
  | Exp_constr_app (_, _, _, el) -> List.for_all (is_non_variable_value env) el
  | _ -> false

(* let kind_equiv k k' = (unbox k)=(unbox k') *)

let kind_dominated k k' = match k(* .u *), k'(* .u *)with
  | Kind_star, Kind_star
  | Kind_affine, Kind_affine
  | Kind_star, Kind_affine -> true
  | _ -> false

(* This is a heuristic to determine the kind of tuple.
   Nik: TODO, remove the tuple type as a built-in. *)
let kind_lub k1 k2 = match (unbox k1)(* .u *), (unbox k2)(* .u *)with
  | b, Kind_affine
  | Kind_affine, b when base_kind b -> Kind_affine
  | Kind_affine, Kind_affine -> Kind_affine
  | Kind_star, Kind_star
  | Kind_star, Kind_prop
  | Kind_prop, Kind_star
  | Kind_prop, Kind_prop -> Kind_star
  | _ -> raise (Err (spr "Kind_lub is undefined for the specified kinds (%s,%s)" (Pretty.strKind k1) (Pretty.strKind k2)))

let rec kind_abstractable (p:Range.range) k = match k(* .u *)with
  | Kind_star
  | Kind_affine
  | Kind_prop
  | Kind_erasable -> true
  | Kind_dcon(_, _, k) -> kind_abstractable p k
  | (Kind_tcon _) ->
      #if JS
      #else
        if not !Options.js_warnings_only then
          warn "(%s) Got kind %s\nAbstraction over types with kind (k => k) may not be compilable to .NET, so your program may be unexecutable.\n"
            (Range.string_of_range p) (Pretty.strKind k);
      #endif
        true
  | _ -> false

let disjoint_affine_usages l =
  let rec nodups = function
    | []
    | [_] -> true
    | hd::tl ->
        if not (List.exists (bvar_eq hd) tl) then
          nodups tl
        else
          let msg = spr "Affine variable %s used more than once" (Pretty.strBvar hd) in
            raise (Err msg) in
    nodups l

let subtract l1 l2 =
  let rec sub out l a = match l with
    | [] -> out
    | hd::tl when bvar_eq hd a -> sub out tl a
    | hd::tl -> sub (hd::out) tl a in
    List.fold_left (sub []) l1 l2

let union l1 l2 =
  let add l a = if List.exists (bvar_eq a) l then l else a::l in
    List.fold_left add l1 l2

let union_ev (ev1:evidence) ev2 = ev1@ev2

let lookup_field_in_record_typ p env fn rt =
  let fn_t_l = Tcenv.get_record_fields p env rt in
    (match List.tryFind (fun (fn', t') -> Sugar.lid_equals fn' fn) fn_t_l with
         Some (fn', t') -> t'
       | _ -> let msg = spr "Field name %s is not a part of the type %s"
           (Sugar.text_of_lid fn) (Pretty.strTyp rt) in
           raise (Error(msg, p)))

let is_proof_typ_constr (t:typ) = match t.v with
  | Typ_const (v,_) ->Sugar.lid_equals v.v Const.pf_lid
  | _ -> false
let is_proof_typ (t:typ) = match t.v with
  | Typ_app (pf_typ, _) -> is_proof_typ_constr pf_typ
  | _ -> false
let maybe_eq_proof_typ (t:typ) = match t.v with
  | Typ_app (pf_typ, ({v=Typ_dep({v=Typ_dep(t1, _); sort=_; p=_}, _); sort=_; p=_}))
      when is_proof_typ_constr pf_typ -> true
  | _ -> false
let is_impl_typ_constr t = match t.v with
  | Typ_const (v,_) -> Sugar.lid_equals v.v Const.implies_lid
  | _ -> false
let impl_lhs t = match t.v with
  | Typ_app(imp, lhs) when is_impl_typ_constr imp -> Some lhs
  | _ -> None
let destruct_implication (t:typ) = match t.v with
  | Typ_app(pf_typ, {v=Typ_app(impl_l, rhs); sort=_; p=_}) when is_proof_typ_constr pf_typ ->
      (match impl_lhs impl_l with
           Some lhs -> Some (lhs, rhs)
         | _ -> None)
  | _ -> None

let is_lid t l = match t.v with
  | Typ_app({v=Typ_const(v,_); sort=_;p=_}, lhs) when Sugar.lid_equals v.v l ->  Some lhs
  | _ -> None
let destruct_pf_binop lid (t:typ) = match t.v with
  | Typ_app(pf_typ, {v=Typ_app(constr, rhs); sort=_; p=_}) when is_proof_typ_constr pf_typ ->
      (match is_lid constr lid with
           Some lhs -> Some (lhs, rhs)
         | _ -> None)
  | _ -> None
let is_pf_binop lid (t:typ) = match destruct_pf_binop lid t with
  | None -> false
  | _ -> true

let unwrap_pf (t:typ) = match t.v with
    Typ_app(pf_typ, t) when is_proof_typ_constr pf_typ -> t
  | _ -> raise Impos

let is_implication t = is_pf_binop Const.implies_lid t

let typing_const (env:Tcenv.env) = function
  | Sugar.Const_unit -> Const.unit_typ
  | Sugar.Const_bool _ -> Const.bool_typ
  | Sugar.Const_int32 _ ->
      if Options.js_runtime ()
      then Const.num_typ
      else Const.int_typ
  | Sugar.Const_string _ -> Const.string_typ
  | Sugar.Const_float _ ->
      if Options.js_runtime ()
      then Const.num_typ
      else Const.float_typ
  | _ -> raise (NYI "Unsupported constant")

open Tcenv

let push_tparams env tps =
  List.fold_left (fun env tp ->
                    let binding = match tp with
                      | Tparam_typ (x,k) -> Binding_typ (x.realname,k)
                      | Tparam_term (x, t) -> Binding_var (x.realname,t) in
                      push_local_binding env binding) env tps

let get_evidence e =
  let rec aux out e = match e.v with
    | Exp_ascribed (e, t, ev) -> aux (ev@out) e
    | _ -> out
  in aux [] e

let get_evidencel el = List.flatten (List.map get_evidence el)

let subtract_ev_exact (ev:evidence) ev' =
  let sub_one ev ev' =
    let f = function
       | Inr (e1,e2), Inr (e1',e2') -> e1===e1' && e2'===e2
       | Inl (t1,t2), Inl(t1',t2') -> t1===t1' && t2===t2'
     in
      List.filter (fun e -> not (f (ev', e))) ev in
    List.fold_left sub_one ev ev'

let subtract_ev (ev:evidence) (t_e_l:list<Disj<typ,exp>>) =
  let warn e = Printf.printf "Warning! Got a match binding with an unexpected LHS: %s" (Pretty.strExp e) in
  let aux ev = function
     | Inr e -> (match (unascribe e).v with
                    | Exp_bvar bv ->
                            List.filter (function
                                | Inr (bv', _) -> (match (unascribe bv').v with
                                            | Exp_bvar bv' -> not(bvar_eq bv bv')
                                            | _ -> warn bv'; true)
                                | Inl (t1, t2) -> true) ev
                    | _ -> warn e; ev)
     | Inl t -> (match t.v with
                    | Typ_btvar bv ->
                            List.filter (function
                                | Inr _ -> true
                                | Inl (t1, t2) -> (match t1.v with
                                            | Typ_btvar bv' -> not (bvar_eq bv bv')
                                            | _ -> true)) ev) in
    List.fold_left aux ev t_e_l

let collect_evidence e =
  (*   Printf.printf "Collecting evidence on expr %s\n" (Pretty.strExp e); *)
  let pat_vars_as_exp_l = function
      Pat_variant (_, _, _, bvs, _) -> List.map (fun bv -> (ewithsort (Exp_bvar bv) bv.sort)) bvs in
  let pat_tvars_as_typ_l = function
    | Pat_variant(_, tl, _, _, is_existential) when is_existential -> tl
    | _ -> [] in
  let add_ev e = function
    | [] -> e
    | ev -> ascribe e e.sort ev in
  let is_match_assumption ev (e, cn) = match ev with
    | Inl _ -> false
    | Inr (e1, e2) ->
    (*     Printf.printf "Checking if match assumption (%s,%s) = (%s,%s)?\n" (Pretty.strExp e1) (Pretty.strExp e2) (Pretty.strExp e) (Pretty.str_of_lident cn.v); *)
    match (unascribe e2).v with
      | Exp_constr_app(cn', _, _, _) when Sugar.lid_equals cn.v cn'.v -> equalsExp (unascribe e) (unascribe e1)
      | _ -> false in
  let is_boolean_assumption ev e = match ev with
    | Inl _ -> false
    | Inr (e1, e2) ->
        match (unascribe e2).v with
          | Exp_constant (Sugar.Const_bool _) -> equalsExp (unascribe e) (unascribe e1)
          | _ -> false in
  let ev =  match e.v with
    | Exp_ascribed _
    | Exp_gvar _
    | Exp_bvar _
    | Exp_fvar _
    | Exp_bot
    | Exp_constant _ -> []
    | Exp_primop(_, el)
    | Exp_extern_call(_, _, _, _, el)
    | Exp_constr_app (_, _, _, el) -> get_evidencel el
    | Exp_abs(bvd, t, e) -> subtract_ev (get_evidence e) [Inr (AbsynUtils.bvd_to_exp bvd t)]
    | Exp_tapp(e, _)
    | Exp_proj(e, _)
    | Exp_tabs(_, _, _, e) -> get_evidence e
    | Exp_app(e1, e2) -> union_ev (get_evidence e1) (get_evidence e2)
    | Exp_match (e, eqns, def) ->
        let result = union_ev
          (union_ev
             (List.flatten (List.map (fun (Pat_variant(cname, _, _, _, _) as pat, br) ->
                                        let evbranch = (get_evidence br) in
(*                                           Printf.printf "Got evidence from branch %s\n" (Pretty.strEv evbranch); *)
                                        let pat_vars = (pat_vars_as_exp_l pat) |> List.map (fun e -> Inr e) in
                                        let pat_vars = pat_vars @ ((pat_tvars_as_typ_l pat) |> List.map (fun t -> Inl t)) in
                                        let ev0 = subtract_ev evbranch pat_vars in
(*                                             Printf.printf "After subtracting pat vars %s\n" (Pretty.strEv ev0); *)
                                        let result = List.filter (fun ev -> not (is_match_assumption ev (e, AbsynUtils.Wfv cname))) ev0 in
(*                                               Printf.printf "After subtracting match assumption vars %s\n" (Pretty.strEv result); *)
                                              result) eqns))
             (get_evidence def))
          (get_evidence e) in
(*           Printf.printf "Collected evidence from match %s\n" (Pretty.strEv result); *)
          result
    | Exp_cond(e1, e2, e3) ->
        union_ev (List.filter (fun ev -> not(is_boolean_assumption ev e1)) (union_ev (get_evidence e1) (get_evidence e2))) (get_evidence e1)
    | Exp_recd (_, _, phantoms, fnl) -> List.flatten (List.map (fun (_, e) -> get_evidence e) fnl)
    | Exp_let(false, [bvd, t, e1], e2) ->
        union_ev
          (subtract_ev (get_evidence e2) [Inr (AbsynUtils.bvd_to_exp bvd t)])
          (get_evidence e1)
    | Exp_let(true, bvd_e_l, e2) ->
        union_ev (List.flatten (List.map (fun (bdv, t, e) -> get_evidence e) bvd_e_l)) (get_evidence e2)
  in
    add_ev e ev


let bot t = ewithsort (Exp_ascribed (ewithsort Exp_bot t, t, [])) t

let is_closure_typ env t = match (expand_typ env t).v with
    Typ_fun _
  | Typ_univ _ -> true
  | _ -> false

let is_boxed k = match k(* .u *)with
  | Kind_boxed _ -> true
  | _ -> false

let is_xvar_free (x:bvvdef) t =
  let _, xvs = freevarsTyp t in
(*     Printf.printf "Free variables of type (%s)\n [%s]\n" (Pretty.strTyp t) (String.concat "; " (List.map Pretty.strBvar xvs)); *)
    match List.tryFind (fun (bv:bvvar) -> (bvar_real_name bv).idText = x.realname.idText) xvs with
      | None -> false
      | _ -> true

let is_tvar_free (a:btvdef) t =
  let tvs, _ = freevarsTyp t in
    match List.tryFind (fun (bv:btvar) -> (bvar_real_name bv).idText = a.realname.idText) tvs with
      | None -> false
      | _ -> true

let reflexivity_var env =
  let axT = Tcenv.lookup_lid env Const.reflexivity_lid in
  let axVar = fvwithsort Const.reflexivity_lid axT in
    axVar

let eqT_of_typ env t =
  let eqK = Tcenv.lookup_typ_const env (AbsynUtils.Wftv Const.eq_lid) in
    (twithsort (Typ_app(twithsort (Typ_const (fvwithsort Const.eq_lid eqK,None)) eqK, t))
       (Kind_dcon(None, t, Kind_dcon(None, t, Kind_star))))

let unify uv t = Unionfind.change uv (Fixed (alpha_convert t)) (* NS: added alpha conversoin 9/2/11 *)

let check_unify (uv,(k:kind)) t =
  let occurs uv t =
    let uvs_typ uvs t = match t with
      | Typ_uvar(uv, _) -> uv::uvs, t
      | _ -> uvs, t in
    let uvs_exp uvs e = uvs, e in
    let uvs, _ = descend_typ_map uvs_typ uvs_exp [] t in
      List.exists (fun uv' -> Unionfind.equivalent uv uv') uvs
  in

    match Unionfind.find uv with
      | Uvar wf ->
          if wf t k
          then
            (if not (occurs uv t)
             then (unify uv t; None)
             else Some "Unification fails occurs check")
          else Some "Unification fails kinding check"
      | t -> (pr "Unexpected uvar in well-formedness check: %A\n" t; raise Impos)


type subst = list<(list<uvar*kind> * option<typ>)>
let unify_subst_vars (subst:subst) =
  let unify_eq_class (uvl, topt) = match uvl with
    | [] -> raise (NYI "Unexpected empty equivalence class")
    | (uv,_)::tl  ->
        List.iter (fun (uv',_) -> Unionfind.union uv uv') tl;
        match topt with
          | None -> ()
          | Some t -> unify uv t in
    List.iter unify_eq_class subst

let mkTypApp t1 t2 = match t1.sort(* .u *)with
  | Kind_tcon(_, _, k2) ->
      twithsort (Typ_app(t1, t2)) (open_kind t1.sort t2)
  | _ -> raise Impos

let mkTypDep t v = match t.sort(* .u *)with
  | Kind_dcon(_, _, k2) ->
      twithsort (Typ_dep(t, v)) (open_kind_with_exp t.sort v)
  | _ -> raise Impos

let rec reduce_typ_delta_beta tenv t =
  let rec aux t =
    let t = expand_typ tenv t in
      match t.v with
        | Typ_dep(t1orig, e) ->
            let t1 = aux t1orig in
              (match t1.v with
                 | Typ_lam(x, t1_a, t1_r) ->
                     let t1_r' = substitute_exp t1_r x e in
                       aux t1_r'
                 | _ ->
                     if t1orig===t1
                     then t
                     else twithinfo (Typ_dep(t1, e)) t.sort t.p)
        | Typ_app(t1orig, t2orig) ->
            let t1 = aux t1orig in
            let t2 = aux t2orig in
              (match t1.v with
                 | Typ_tlam(a, t1_a, t1_r) ->
                     let t1_r' = substitute t1_r a t2 in
                       aux t1_r'
                 | _ ->
                     if t1orig===t1 && t2orig===t2
                     then t
                     else twithinfo (Typ_app(t1, t2)) t.sort t.p)
        | _ -> t in
    aux t

let rtdb tenv t =
  let rec rtdb i tenv t =
    let rec aux smap t =
      let t = expand_typ tenv t in
        match t.v with
          | Typ_dep(t1orig, e) ->
              let smap, t1 = aux smap t1orig in
                (match t1.v with
                   | Typ_lam(x, t1_a, t1_r) ->
                       let smap = Inr(x,(substitute_exp_typ_or_exp_l e smap))::smap in
                         aux smap t1_r
                   | _ ->
                       if t1orig===t1
                       then smap, t
                       else smap, twithinfo (Typ_dep(t1, e)) t.sort t.p)
          | Typ_app(t1orig, t2orig) ->
              let smap, t1 = aux smap t1orig  in
              let smap, t2 = aux smap t2orig in
                (match t1.v with
                   | Typ_tlam(a, t1_a, t1_r) ->
                       let smap = Inl(a, (substitute_l_typ_or_exp t2 smap))::smap in
                         aux smap t1_r
                   | _ ->
                       if t1orig===t1 && t2orig===t2
                       then smap, t
                       else smap, twithinfo (Typ_app(t1, t2)) t.sort t.p)
          | _ -> smap, t in
    let smap, t = aux [] t in
      match smap with
        | [] -> (* pr "rtdb %d noop\n" i; *)
            t
        | _ ->
            (* pr "rtdb %d subst %d\n" i (List.length smap);  *)
            rtdb (i+1) tenv (substitute_l_typ_or_exp t smap) in
    rtdb 0 tenv t

let generalize_with_constraints env forms t e : (list<formula> * typ * exp) =
  if not (is_value e) then forms, t, e
  else
    let find uv sub = List.tryFind (fun (uv', _) -> Unionfind.equivalent uv uv') sub in
    let uvars_in_env = Tcenv.uvars_in_env env in
    let is_uvar_in_env uv = match List.tryFind (fun uv' -> Unionfind.equivalent uv uv') uvars_in_env with
      | None -> false
      | Some _ -> true in
    let subst_and_collect_uvars_typ sub () t = match t with
      | Typ_uvar (uv, k) ->
          (match find uv sub with
             | Some (_,tv) -> sub, tv, None
             | _ ->
                 if is_uvar_in_env uv then sub, t, None
                 else
                   let fn = new_bvd None in
                   let btv = (Typ_btvar (bvwithinfo fn k dummyRange))  in
                     (uv, btv)::sub, btv, None)
      | _ -> sub, t, None in
    let exp_folder_noop env () e = (env,e) in
    let sub, (tsub::forms_sub) = typs_fold_map subst_and_collect_uvars_typ exp_folder_noop (fun _ e -> e) Absyn.ignore_env [] () (t::forms) in
    let tvars = sub |> List.map (fun (uv, ((Typ_btvar btv) as tv)) ->
                                   let _ = unify uv (twithsort tv btv.sort) in
                                     (tv, fst <| freevarsKind btv.sort)) in
    let tvars = tvars |> List.sortWith (fun (Typ_btvar tv1, fv1) (Typ_btvar tv2, fv2) ->
                                          if fv1 |> List.exists (bvar_eq tv2) then 1
                                          else if fv2 |> List.exists (bvar_eq tv1) then -1
                                          else String.compare ((bvar_real_name tv1).idText) ((bvar_real_name tv2).idText)) in
    let residue, univ_typ, Lambda_e = List.fold_right
      (fun (tv, _) (residue, out_typ, Lambda_e) ->
         let forms, residue = match residue with
           | [] -> [], []
           | f -> f, [] in (* TODO: optimize and simplify constraints --- only include forms with the appropriate variables *)
           match tv with
             | Typ_btvar btv ->
                 let out_typ = twithsort (Typ_univ (btv.v, btv.sort, forms, out_typ)) Kind_star  in
                 let Lambda_e = ewithinfo (Exp_tabs (btv.v, btv.sort, forms, Lambda_e)) out_typ Lambda_e.p in
                   (residue, out_typ, Lambda_e)
             | _ -> raise Impos) tvars (forms_sub, tsub, e) in
      residue, univ_typ, Lambda_e

let generalize env t e =
  match generalize_with_constraints env [] t e with
    | ([], t, e) -> t, e
    | _ -> raise Impos


let extractSignature (env:Tcenv.env) (m:modul) =
  let find_letbinding lets (lid:lident) =
    lets |> Util.findOpt (fun (lb, _) ->
                            lb |> List.exists (fun (bvd, _, _) ->
                                                 let _, name = Util.pfx lid.lid in
                                                   name.idText = (pp_name bvd).idText)) in
  let extract_signature_prelude (env:Tcenv.env) sigs lets =
    let prelude, valdecls = sigs |>
        List.partition (function
                          | Sig_value_decl(lid, t) ->
                              (match find_letbinding lets lid with
                                 | None ->
                                     if (not (Sugar.lid_equals env.curmodule Const.prims_lid)) &&
                                       (not (Sugar.lid_equals env.curmodule Const.prooflib_lid))
                                     then Util.warn "Admitting value declaration %s as an axiom without a corresponding definition\n" (Pretty.sli lid);
                                     true
                                 | Some _ -> false)
                          | _ -> true) in
      prelude, valdecls in
  let signature, valdecls = extract_signature_prelude env m.signature m.letbindings in
    signature, valdecls
