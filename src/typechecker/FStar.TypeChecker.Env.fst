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
module FStar.TypeChecker.Env
open FStar.Pervasives
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar
open FStar.Compiler
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Syntax.Util
open FStar.Compiler.Util
open FStar.Ident
open FStar.Compiler.Range
open FStar.Errors
open FStar.TypeChecker.Common

module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module BU = FStar.Compiler.Util
module U  = FStar.Syntax.Util
module UF = FStar.Syntax.Unionfind
module Const = FStar.Parser.Const
module TcComm = FStar.TypeChecker.Common

let rec eq_step s1 s2 =
  match s1, s2 with
  | Beta, Beta
  | Iota, Iota           //pattern matching
  | Zeta, Zeta            //fixed points
  | ZetaFull, ZetaFull    //fixed points
  | Weak, Weak            //Do not descend into binders
  | HNF, HNF             //Only produce a head normal form
  | Primops, Primops         //reduce primitive operators like +, -, *, /, etc.
  | Eager_unfolding, Eager_unfolding
  | Inlining, Inlining
  | DoNotUnfoldPureLets, DoNotUnfoldPureLets
  | UnfoldTac, UnfoldTac
  | PureSubtermsWithinComputations, PureSubtermsWithinComputations
  | Simplify, Simplify
  | EraseUniverses, EraseUniverses
  | AllowUnboundUniverses, AllowUnboundUniverses
  | Reify, Reify
  | CompressUvars, CompressUvars
  | NoFullNorm, NoFullNorm
  | CheckNoUvars, CheckNoUvars
  | Unmeta, Unmeta
  | Unascribe, Unascribe
  | NBE, NBE
  | Unrefine, Unrefine -> true
  | Exclude s1, Exclude s2 -> eq_step s1 s2
  | UnfoldUntil s1, UnfoldUntil s2 -> s1 = s2
  | UnfoldOnly lids1, UnfoldOnly lids2
  | UnfoldFully lids1, UnfoldFully lids2
  | UnfoldAttr lids1, UnfoldAttr lids2 ->
      List.length lids1 = List.length lids2 && List.forall2 Ident.lid_equals lids1 lids2
  | UnfoldQual strs1, UnfoldQual strs2 -> strs1 = strs2
  | _ -> false

let preprocess env tau tm  = env.mpreprocess env tau tm
let postprocess env tau ty tm = env.postprocess env tau ty tm

let rename_gamma subst gamma =
    gamma |> List.map (function
      | Binding_var x -> begin
        let y = Subst.subst subst (S.bv_to_name x) in
        match (Subst.compress y).n with
        | Tm_name y ->
            // We don't want to change the type
            Binding_var ({ y with sort = Subst.subst subst x.sort })
        | _ -> failwith "Not a renaming"
        end
      | b -> b)
let rename_env subst env = {env with gamma=rename_gamma subst env.gamma}
let default_tc_hooks =
  { tc_push_in_gamma_hook = (fun _ _ -> ()) }
let tc_hooks (env: env) = env.tc_hooks
let set_tc_hooks env hooks = { env with tc_hooks = hooks }

let set_dep_graph e g = {e with dsenv=DsEnv.set_dep_graph e.dsenv g}
let dep_graph e = DsEnv.dep_graph e.dsenv

type sigtable = BU.smap sigelt

let should_verify env =
    not env.lax
    && not env.admit
    && Options.should_verify (string_of_lid env.curmodule)

let visible_at d q = match d, q with
  | NoDelta,    _
  | Eager_unfolding_only, Unfold_for_unification_and_vcgen
  | Unfold _,   Unfold_for_unification_and_vcgen
  | Unfold _,   Visible_default -> true
  | InliningDelta, Inline_for_extraction -> true
  | _ -> false

let default_table_size = 200
let new_sigtab () = BU.smap_create default_table_size
let new_gamma_cache () = BU.smap_create 100

let initial_env deps
  tc_term
  typeof_tot_or_gtot_term
  typeof_tot_or_gtot_term_fastpath
  universe_of
  teq_nosmt_force
  subtype_nosmt_force
  solver module_lid nbe : env =
  { solver=solver;
    range=dummyRange;
    curmodule=module_lid;
    gamma= [];
    gamma_sig = [];
    gamma_cache=new_gamma_cache();
    modules= [];
    expected_typ=None;
    sigtab=new_sigtab();
    attrtab=new_sigtab();
    instantiate_imp=true;
    effects={decls=[]; order=[]; joins=[]; polymonadic_binds=[]; polymonadic_subcomps=[]};
    generalize=true;
    letrecs=[];
    top_level=false;
    check_uvars=false;
    use_eq_strict=false;
    is_iface=false;
    admit=false;
    lax=false;
    lax_universes=false;
    phase1=false;
    failhard=false;
    nosynth=false;
    uvar_subtyping=true;

    tc_term=tc_term;
    typeof_tot_or_gtot_term=typeof_tot_or_gtot_term;
    typeof_well_typed_tot_or_gtot_term =
      (fun env t must_tot ->
       match typeof_tot_or_gtot_term_fastpath env t must_tot with
       | Some k -> k, trivial_guard
       | None ->
         let t', k, g = typeof_tot_or_gtot_term env t must_tot in
         k, g);
    universe_of=universe_of;
    teq_nosmt_force=teq_nosmt_force;
    subtype_nosmt_force=subtype_nosmt_force;
    use_bv_sorts=false;
    qtbl_name_and_index=BU.smap_create 10, None;  //10?
    normalized_eff_names=BU.smap_create 20;  //20?
    fv_delta_depths = BU.smap_create 50;
    proof_ns = Options.using_facts_from ();
    synth_hook = (fun e g tau -> failwith "no synthesizer available");
    try_solve_implicits_hook = (fun e tau imps -> failwith "no implicit hook available");
    splice = (fun e rng tau -> failwith "no splicer available");
    mpreprocess = (fun e tau tm -> failwith "no preprocessor available");
    postprocess = (fun e tau typ tm -> failwith "no postprocessor available");
    identifier_info=BU.mk_ref FStar.TypeChecker.Common.id_info_table_empty;
    tc_hooks = default_tc_hooks;
    dsenv = FStar.Syntax.DsEnv.empty_env deps;
    nbe = nbe;
    strict_args_tab = BU.smap_create 20;
    erasable_types_tab = BU.smap_create 20;
    enable_defer_to_tac=true;
    unif_allow_ref_guards=false;
    erase_erasable_args=false;

    rel_query_for_apply_tac_uvar=None;
  }

let dsenv env = env.dsenv
let sigtab env = env.sigtab
let attrtab env = env.attrtab
let gamma_cache env = env.gamma_cache

(* Marking and resetting the environment, for the interactive mode *)

let query_indices: ref (list (list (lident * int))) = BU.mk_ref [[]]
let push_query_indices () = match !query_indices with // already signal-atmoic
  | [] -> failwith "Empty query indices!"
  | _ -> query_indices := (List.hd !query_indices)::!query_indices

let pop_query_indices () = match !query_indices with // already signal-atmoic
  | [] -> failwith "Empty query indices!"
  | hd::tl -> query_indices := tl

let snapshot_query_indices () = Common.snapshot push_query_indices query_indices ()
let rollback_query_indices depth = Common.rollback pop_query_indices query_indices depth

let add_query_index (l, n) = match !query_indices with
  | hd::tl -> query_indices := ((l,n)::hd)::tl
  | _ -> failwith "Empty query indices"

let peek_query_indices () = List.hd !query_indices

let stack: ref (list env) = BU.mk_ref []
let push_stack env =
    stack := env::!stack;
    {env with sigtab=BU.smap_copy (sigtab env);
              attrtab=BU.smap_copy (attrtab env);
              gamma_cache=BU.smap_copy (gamma_cache env);
              identifier_info=BU.mk_ref !env.identifier_info;
              qtbl_name_and_index=BU.smap_copy (env.qtbl_name_and_index |> fst), env.qtbl_name_and_index |> snd;
              normalized_eff_names=BU.smap_copy env.normalized_eff_names;
              fv_delta_depths=BU.smap_copy env.fv_delta_depths;
              strict_args_tab=BU.smap_copy env.strict_args_tab;
              erasable_types_tab=BU.smap_copy env.erasable_types_tab }

let pop_stack () =
    match !stack with
    | env::tl ->
      stack := tl;
      env
    | _ -> failwith "Impossible: Too many pops"

let snapshot_stack env = Common.snapshot push_stack stack env
let rollback_stack depth = Common.rollback pop_stack stack depth

let snapshot env msg = BU.atomically (fun () ->
    let stack_depth, env = snapshot_stack env in
    let query_indices_depth, () = snapshot_query_indices () in
    let solver_depth, () = env.solver.snapshot msg in
    let dsenv_depth, dsenv = DsEnv.snapshot env.dsenv in
    (stack_depth, query_indices_depth, solver_depth, dsenv_depth), { env with dsenv=dsenv })

let rollback solver msg depth = BU.atomically (fun () ->
    let stack_depth, query_indices_depth, solver_depth, dsenv_depth = match depth with
        | Some (s1, s2, s3, s4) -> Some s1, Some s2, Some s3, Some s4
        | None -> None, None, None, None in
    let () = solver.rollback msg solver_depth in
    let () = rollback_query_indices query_indices_depth in
    let tcenv = rollback_stack stack_depth in
    let dsenv = DsEnv.rollback dsenv_depth in
    // Because of the way ``snapshot`` is implemented, the `tcenv` and `dsenv`
    // that we rollback to should be consistent:
    FStar.Common.runtime_assert
      (BU.physical_equality tcenv.dsenv dsenv)
      "Inconsistent stack state";
    tcenv)

let push env msg = snd (snapshot env msg)
let pop env msg = rollback env.solver msg None

let incr_query_index env =
  let qix = peek_query_indices () in
  match env.qtbl_name_and_index with
  | _, None -> env
  | tbl, Some (l, n) ->
    match qix |> List.tryFind (fun (m, _) -> Ident.lid_equals l m) with
    | None ->
      let next = n + 1 in
      add_query_index (l, next);
      BU.smap_add tbl (string_of_lid l) next;
      {env with qtbl_name_and_index=tbl, Some (l, next)}
    | Some (_, m) ->
      let next = m + 1 in
      add_query_index (l, next);
      BU.smap_add tbl (string_of_lid l) next;
      {env with qtbl_name_and_index=tbl, Some (l, next)}

////////////////////////////////////////////////////////////
// Checking the per-module debug level and position info  //
////////////////////////////////////////////////////////////
let debug env (l:Options.debug_level_t) =
    Options.debug_at_level (string_of_lid env.curmodule) l
let set_range e r = if r=dummyRange then e else {e with range=r}
let get_range e = e.range

let toggle_id_info env enabled =
  env.identifier_info :=
    FStar.TypeChecker.Common.id_info_toggle !env.identifier_info enabled
let insert_bv_info env bv ty =
  env.identifier_info :=
    FStar.TypeChecker.Common.id_info_insert_bv !env.identifier_info bv ty
let insert_fv_info env fv ty =
  env.identifier_info :=
    FStar.TypeChecker.Common.id_info_insert_fv !env.identifier_info fv ty
let promote_id_info env ty_map =
  env.identifier_info :=
    FStar.TypeChecker.Common.id_info_promote !env.identifier_info ty_map

////////////////////////////////////////////////////////////
// Private utilities                                      //
////////////////////////////////////////////////////////////
let modules env = env.modules
let current_module env = env.curmodule
let set_current_module env lid = {env with curmodule=lid}
let has_interface env l = env.modules |> BU.for_some (fun m -> m.is_interface && lid_equals m.name l)
let find_in_sigtab env lid = BU.smap_try_find (sigtab env) (string_of_lid lid)

let name_not_found (l:lid) =
  (Errors.Fatal_NameNotFound, (format1 "Name \"%s\" not found" (string_of_lid l)))

let variable_not_found v =
  (Errors.Fatal_VariableNotFound, (format1 "Variable \"%s\" not found" (Print.bv_to_string v)))

//Construct a new universe unification variable
let new_u_univ () = U_unif (Unionfind.univ_fresh Range.dummyRange)

let mk_univ_subst (formals : list univ_name) (us : universes) : list subst_elt =
    assert (List.length us = List.length formals);
    let n = List.length formals - 1 in
    us |> List.mapi (fun i u -> UN (n - i, u))

//Instantiate the universe variables in a type scheme with provided universes
let inst_tscheme_with : tscheme -> universes -> universes * term = fun ts us ->
    match ts, us with
    | ([], t), [] -> [], t
    | (formals, t), _ ->
      let vs = mk_univ_subst formals us in
      us, Subst.subst vs t

//Instantiate the universe variables in a type scheme with new unification variables
let inst_tscheme : tscheme -> universes * term = function
    | [], t -> [], t
    | us, t ->
      let us' = us |> List.map (fun _ -> new_u_univ()) in
      inst_tscheme_with (us, t) us'

let inst_tscheme_with_range (r:range) (t:tscheme) =
    let us, t = inst_tscheme t in
    us, Subst.set_use_range r t

let check_effect_is_not_a_template (ed:eff_decl) rng : unit =
  if List.length ed.univs <> 0 || List.length ed.binders <> 0
  then
    let msg = BU.format2
      "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
      (Print.lid_to_string ed.mname)
      (Print.binders_to_string ", " ed.binders) in
    raise_error (Errors.Fatal_NotEnoughArgumentsForEffect, msg) rng

let inst_effect_fun_with (insts:universes) (env:env) (ed:eff_decl) (us, t)  =
  check_effect_is_not_a_template ed env.range;
  if List.length insts <> List.length us
  then failwith (BU.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                   (string_of_int <| List.length us) (string_of_int <| List.length insts)
                   (Print.lid_to_string ed.mname) (Print.term_to_string t));
  snd (inst_tscheme_with (us, t) insts)

type tri =
    | Yes
    | No
    | Maybe

let in_cur_mod env (l:lident) : tri = (* TODO: need a more efficient namespace check! *)
    let cur = current_module env in
    if nsstr l = (string_of_lid cur) then Yes (* fast case; works for everything except records *)
    else if BU.starts_with (nsstr l) (string_of_lid cur)
    then let lns = ns_of_lid l   @ [ident_of_lid l] in
         let cur = ns_of_lid cur @ [ident_of_lid cur] in
         let rec aux c l = match c, l with
            | [], _ -> Maybe
            | _, [] -> No
            | hd::tl, hd'::tl' when ((string_of_id hd = string_of_id hd')) -> aux tl tl'
            | _ -> No in
         aux cur lns
    else No

let lookup_qname env (lid:lident) : qninfo =
  let cur_mod = in_cur_mod env lid in
  let cache t = BU.smap_add (gamma_cache env) (string_of_lid lid) t; Some t in
  let found =
    if cur_mod <> No
    then match BU.smap_try_find (gamma_cache env) (string_of_lid lid) with
      | None ->
        BU.catch_opt
            (BU.find_map env.gamma (function
              | Binding_lid(l, (us_names, t)) when lid_equals lid l->
                (* A recursive definition.
                 * We must return the exact set of universes on which
                 * it is being defined, and not instantiate it.
                 * TODO: could we cache this? *)
                let us = List.map U_name us_names in
                Some (Inl (us, t), Ident.range_of_lid l)
              | _ -> None))
            (fun () -> BU.find_map env.gamma_sig (function
              | (_, { sigel = Sig_bundle(ses, _) }) ->
                  BU.find_map ses (fun se ->
                    if lids_of_sigelt se |> BU.for_some (lid_equals lid)
                    then cache (Inr (se, None), U.range_of_sigelt se)
                    else None)
              | (lids, s) ->
                let maybe_cache t = match s.sigel with
                  | Sig_declare_typ _ -> Some t
                  | _ -> cache t
                in
                begin match List.tryFind (lid_equals lid) lids with
                      | None -> None
                      | Some l -> maybe_cache (Inr (s, None), Ident.range_of_lid l)
                end))
      | se -> se
    else None
  in
  if is_some found
  then found
  else match find_in_sigtab env lid with
        | Some se -> Some (Inr (se, None), U.range_of_sigelt se)
        | None -> None

let lookup_sigelt (env:env) (lid:lid) : option sigelt =
    match lookup_qname env lid with
    | None -> None
    | Some (Inl _, rng) -> None
    | Some (Inr (se, us), rng) -> Some se

let lookup_attr (env:env) (attr:string) : list sigelt =
    match BU.smap_try_find (attrtab env) attr with
    | Some ses -> ses
    | None -> []

let add_se_to_attrtab env se =
    let add_one env se attr = BU.smap_add (attrtab env) attr (se :: lookup_attr env attr) in
    List.iter (fun attr ->
                match (Subst.compress attr).n with
                | Tm_fvar fv -> add_one env se (string_of_lid (lid_of_fv fv))
                | _ -> ()) se.sigattrs

let rec add_sigelt env se = match se.sigel with
    | Sig_bundle(ses, _) -> add_sigelts env ses
    | _ ->
      let lids = lids_of_sigelt se in
      List.iter (fun l -> BU.smap_add (sigtab env) (string_of_lid l) se) lids;
      add_se_to_attrtab env se

and add_sigelts env ses =
    ses |> List.iter (add_sigelt env)

////////////////////////////////////////////////////////////
// Lookup up various kinds of identifiers                 //
////////////////////////////////////////////////////////////
let try_lookup_bv env (bv:bv) =
  BU.find_map env.gamma (function
    | Binding_var id when bv_eq id bv ->
      Some (id.sort, (range_of_id id.ppname))
    | _ -> None)

let lookup_type_of_let us_opt se lid =
    let inst_tscheme ts =
      match us_opt with
      | None -> inst_tscheme ts
      | Some us -> inst_tscheme_with ts us
    in
    match se.sigel with
    | Sig_let((_, [lb]), _) ->
      Some (inst_tscheme (lb.lbunivs, lb.lbtyp), S.range_of_lbname lb.lbname)

    | Sig_let((_, lbs), _) ->
        BU.find_map lbs (fun lb -> match lb.lbname with
          | Inl _ -> failwith "impossible"
          | Inr fv ->
            if fv_eq_lid fv lid
            then Some (inst_tscheme (lb.lbunivs, lb.lbtyp), S.range_of_fv fv)
            else None)

    | _ -> None

let effect_signature (us_opt:option universes) (se:sigelt) rng : option ((universes * typ) * Range.range) =
  let inst_ts us_opt ts =
    match us_opt with
    | None -> inst_tscheme ts
    | Some us -> inst_tscheme_with ts us
  in
  match se.sigel with
  | Sig_new_effect ne ->
    check_effect_is_not_a_template ne rng;
    (match us_opt with
     | None -> ()
     | Some us ->
       if List.length us <> List.length (fst ne.signature)
       then failwith ("effect_signature: incorrect number of universes for the signature of " ^
         (string_of_lid ne.mname) ^ ", expected " ^ (string_of_int (List.length (fst ne.signature))) ^
         ", got " ^ (string_of_int (List.length us)))
       else ());

    Some (inst_ts us_opt ne.signature, se.sigrng)

  | Sig_effect_abbrev (lid, us, binders, _, _) ->
    Some (inst_ts us_opt (us, U.arrow binders (mk_Total teff)), se.sigrng)

  | _ -> None

let try_lookup_lid_aux us_opt env lid =
  let inst_tscheme ts =
      match us_opt with
      | None -> inst_tscheme ts
      | Some us -> inst_tscheme_with ts us
  in
  let mapper (lr, rng) =
    match lr with
    | Inl t ->
      Some (t, rng)

    | Inr ({sigel = Sig_datacon(_, uvs, t, _, _, _) }, None) ->
      Some (inst_tscheme (uvs, t), rng)

    | Inr ({sigel = Sig_declare_typ (l, uvs, t); sigquals=qs }, None) ->
      if in_cur_mod env l = Yes
      then if qs |> List.contains Assumption || env.is_iface
           then Some (inst_tscheme (uvs, t), rng)
           else None
      else Some (inst_tscheme (uvs, t), rng)

    | Inr ({sigel = Sig_inductive_typ (lid, uvs, tps, k, _, _) }, None) ->
      begin match tps with
        | [] -> Some (inst_tscheme (uvs, k), rng)
        | _ ->  Some (inst_tscheme (uvs, U.flat_arrow tps (mk_Total k)), rng)
      end

    | Inr ({sigel = Sig_inductive_typ (lid, uvs, tps, k, _, _) }, Some us) ->
      begin match tps with
        | [] -> Some (inst_tscheme_with (uvs, k) us, rng)
        | _ ->  Some (inst_tscheme_with (uvs, U.flat_arrow tps (mk_Total k)) us, rng)
      end

    | Inr se ->
      begin match se with // FIXME why does this branch not use rng?
        | { sigel = Sig_let _ }, None ->
          lookup_type_of_let us_opt (fst se) lid

        | _ ->
          effect_signature us_opt (fst se) env.range
      end |> BU.map_option (fun (us_t, rng) -> (us_t, rng))
  in
    match BU.bind_opt (lookup_qname env lid) mapper with
      | Some ((us, t), r) -> Some ((us, {t with pos=range_of_lid lid}), r)
      | None -> None

////////////////////////////////////////////////////////////////
//External interaface for querying identifiers
//Provides, in order from the interface env.fsi:
//        val lid_exists             : env -> lident -> bool
//        val lookup_bv              : env -> bv -> typ
//        val try_lookup_lid         : env -> lident -> option (universes * typ)
//        val lookup_lid             : env -> lident -> (universes * typ)
//        val lookup_univ            : env -> univ_name -> bool
//        val try_lookup_val_decl    : env -> lident -> option (tscheme * list qualifier)
//        val lookup_val_decl        : env -> lident -> universes * typ
//        val lookup_datacon         : env -> lident -> universes * typ
//        val datacons_of_typ        : env -> lident -> list lident
//        val typ_of_datacon         : env -> lident -> lident
//        val lookup_definition      : delta_level -> env -> lident -> option (univ_names * term)
//        val lookup_attrs_of_lid    : env -> lid -> option list attribute
//        val try_lookup_effect_lid  : env -> lident -> option term
//        val lookup_effect_lid      : env -> lident -> term
//        val lookup_effect_abbrev   : env -> universes -> lident -> option (binders * comp)
//        val norm_eff_name          : (env -> lident -> lident)
//        val lookup_effect_quals    : env -> lident -> list qualifier
//        val lookup_projector       : env -> lident -> int -> lident
//        val current_module         : env -> lident
//        val is_projector           : env -> lident -> bool
//        val is_datacon             : env -> lident -> bool
//        val is_record              : env -> lident -> bool
//        val is_interpreted         : (env -> term -> bool)
//        val is_type_constructor    : env -> lident -> bool
//        val num_inductive_ty_params: env -> lident -> int
//Each of these functions that returns a term ensures to update
//the range information on the term with the currrent use-site
////////////////////////////////////////////////////////////////

let lid_exists env l =
    match lookup_qname env l with
    | None -> false
    | Some _ -> true

let lookup_bv env bv =
    let bvr = range_of_bv bv in
    match try_lookup_bv env bv with
    | None -> raise_error (variable_not_found bv) bvr
    | Some (t, r) -> Subst.set_use_range bvr t,
                     Range.set_use_range r (Range.use_range bvr)

let try_lookup_lid env l =
    match try_lookup_lid_aux None env l with
    | None -> None
    | Some ((us, t), r) ->
      let use_range = range_of_lid l in
      let r = Range.set_use_range r (Range.use_range use_range) in
      Some ((us, Subst.set_use_range use_range t), r)

let try_lookup_and_inst_lid env us l =
    match try_lookup_lid_aux (Some us) env l with
    | None -> None
    | Some ((_, t), r) ->
      let use_range = range_of_lid l in
      let r = Range.set_use_range r (Range.use_range use_range) in
      Some (Subst.set_use_range use_range t, r)

let lookup_lid env l =
    match try_lookup_lid env l with
    | None -> raise_error (name_not_found l) (range_of_lid l)
    | Some v -> v

let lookup_univ env x =
    List.find (function
        | Binding_univ y -> (string_of_id x = string_of_id y)
        | _ -> false) env.gamma
    |> Option.isSome

let try_lookup_val_decl env lid =
  //QUESTION: Why does this not inst_tscheme?
  match lookup_qname env lid with
    | Some (Inr ({ sigel = Sig_declare_typ(_, uvs, t); sigquals = q }, None), _) ->
      Some ((uvs, Subst.set_use_range (range_of_lid lid) t),q)
    | _ -> None

let lookup_val_decl env lid =
  match lookup_qname env lid with
    | Some (Inr ({ sigel = Sig_declare_typ(_, uvs, t) }, None), _) ->
      inst_tscheme_with_range (range_of_lid lid) (uvs, t)
    | _ -> raise_error (name_not_found lid) (range_of_lid lid)

let lookup_datacon env lid =
  match lookup_qname env lid with
    | Some (Inr ({ sigel = Sig_datacon (_, uvs, t, _, _, _) }, None), _) ->
      inst_tscheme_with_range (range_of_lid lid) (uvs, t)
    | _ -> raise_error (name_not_found lid) (range_of_lid lid)

let datacons_of_typ env lid =
  match lookup_qname env lid with
    | Some (Inr ({ sigel = Sig_inductive_typ(_, _, _, _, _, dcs) }, _), _) -> true, dcs
    | _ -> false, []

let typ_of_datacon env lid =
  match lookup_qname env lid with
    | Some (Inr ({ sigel = Sig_datacon (_, _, _, l, _, _) }, _), _) -> l
    | _ -> failwith (BU.format1 "Not a datacon: %s" (Print.lid_to_string lid))

let lookup_definition_qninfo_aux rec_ok delta_levels lid (qninfo : qninfo) =
  let visible quals =
      delta_levels |> BU.for_some (fun dl -> quals |> BU.for_some (visible_at dl))
  in
  match qninfo with
  | Some (Inr (se, None), _) ->
    begin match se.sigel with
      | Sig_let((is_rec, lbs), _)
        when visible se.sigquals
          && (not is_rec || rec_ok) ->
          BU.find_map lbs (fun lb ->
              let fv = right lb.lbname in
              if fv_eq_lid fv lid
              then Some (lb.lbunivs, lb.lbdef)
              else None)
      | _ -> None
    end
  | _ -> None

let lookup_definition_qninfo delta_levels lid (qninfo : qninfo) =
    lookup_definition_qninfo_aux true delta_levels lid qninfo

let lookup_definition delta_levels env lid =
    lookup_definition_qninfo delta_levels lid <| lookup_qname env lid

let lookup_nonrec_definition delta_levels env lid =
    lookup_definition_qninfo_aux false delta_levels lid <| lookup_qname env lid

let delta_depth_of_qninfo_lid lid (qn:qninfo) : option delta_depth =
    match qn with
    | None
    | Some (Inl _, _) -> Some (Delta_constant_at_level 0)
    | Some (Inr(se, _), _) ->
      match se.sigel with
      | Sig_inductive_typ _
      | Sig_bundle _
      | Sig_datacon _ -> Some (Delta_constant_at_level 0)
      | Sig_declare_typ _ -> Some (FStar.Syntax.DsEnv.delta_depth_of_declaration lid se.sigquals)
      | Sig_let ((_,lbs), _) ->
          BU.find_map lbs (fun lb ->
              let fv = right lb.lbname in
              if fv_eq_lid fv lid
              then Some fv.fv_delta
              else None)

      | Sig_fail _
      | Sig_splice  _ ->
        failwith "impossible: delta_depth_of_qninfo"

      | Sig_assume _
      | Sig_new_effect _
      | Sig_sub_effect _
      | Sig_effect_abbrev _ (* None? *)
      | Sig_pragma  _
      | Sig_polymonadic_bind _
      | Sig_polymonadic_subcomp _ -> None


let delta_depth_of_qninfo (fv:fv) (qn:qninfo) : option delta_depth =
    let lid = fv.fv_name.v in
    if nsstr lid = "Prims" then Some fv.fv_delta //NS delta: too many special cases in existing code
    else delta_depth_of_qninfo_lid lid qn

let delta_depth_of_fv env fv =
  let lid = fv.fv_name.v in
  if nsstr lid = "Prims" then fv.fv_delta //NS delta: too many special cases in existing code for prims; FIXME!
  else
    //try cache
    (string_of_lid lid) |> BU.smap_try_find env.fv_delta_depths |> (fun d_opt ->
      if d_opt |> is_some then d_opt |> must
      else
        match delta_depth_of_qninfo fv (lookup_qname env fv.fv_name.v) with
        | None -> failwith (BU.format1 "Delta depth not found for %s" (FStar.Syntax.Print.fv_to_string fv))
        | Some d ->
          if d <> fv.fv_delta
          && Options.debug_any()
          then BU.print3 "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                         (Print.fv_to_string fv)
                         (Print.delta_depth_to_string fv.fv_delta)
                         (Print.delta_depth_to_string d);
          BU.smap_add env.fv_delta_depths (string_of_lid lid) d;
          d)

let quals_of_qninfo (qninfo : qninfo) : option (list qualifier) =
  match qninfo with
  | Some (Inr (se, _), _) -> Some se.sigquals
  | _ -> None

let attrs_of_qninfo (qninfo : qninfo) : option (list attribute) =
  match qninfo with
  | Some (Inr (se, _), _) -> Some se.sigattrs
  | _ -> None

let lookup_attrs_of_lid env lid : option (list attribute) =
  attrs_of_qninfo <| lookup_qname env lid

let fv_exists_and_has_attr env fv_lid attr_lid : bool * bool =
    match lookup_attrs_of_lid env fv_lid with
    | None ->
      false, false
    | Some attrs ->
      true,
      attrs |> BU.for_some (fun tm ->
         match (U.un_uinst tm).n with
         | Tm_fvar fv -> S.fv_eq_lid fv attr_lid
         | _ -> false)

let fv_with_lid_has_attr env fv_lid attr_lid : bool =
  snd (fv_exists_and_has_attr env fv_lid attr_lid)

let fv_has_attr env fv attr_lid =
  fv_with_lid_has_attr env fv.fv_name.v attr_lid

let cache_in_fv_tab (tab:BU.smap 'a) (fv:fv) (f:unit -> (bool * 'a)) : 'a =
  let s = string_of_lid (S.lid_of_fv fv) in
  match BU.smap_try_find tab s with
  | None ->
    let should_cache, res = f () in
    if should_cache then BU.smap_add tab s res;
    res

  | Some r ->
    r

let fv_has_erasable_attr env fv =
  let f () =
     let ex, erasable = fv_exists_and_has_attr env fv.fv_name.v Const.erasable_attr in
     ex,erasable
     //unfortunately, treating the Const.must_erase_for_extraction_attr
     //in the same way here as erasable_attr leads to regressions in fragile proofs,
     //notably in FStar.ModifiesGen, since this expands the class of computation types
     //that can be promoted from ghost to tot. That in turn results in slightly different
     //smt encodings, leading to breakages. So, sadly, I'm not including must_erase_for_extraction
     //here. In any case, must_erase_for_extraction is transitionary and should be removed
  in
  cache_in_fv_tab env.erasable_types_tab fv f

let fv_has_strict_args env fv =
  let f () =
    let attrs = lookup_attrs_of_lid env (S.lid_of_fv fv) in
    match attrs with
    | None -> false, None
    | Some attrs ->
      let res =
          BU.find_map attrs (fun x ->
            fst (FStar.ToSyntax.ToSyntax.parse_attr_with_list
                false x FStar.Parser.Const.strict_on_arguments_attr))
      in
      true, res
  in
  cache_in_fv_tab env.strict_args_tab fv f

let try_lookup_effect_lid env (ftv:lident) : option typ =
  match lookup_qname env ftv with
    | Some (Inr (se, None), _) ->
      begin match effect_signature None se env.range with
        | None -> None
        | Some ((_, t), r) -> Some (Subst.set_use_range (range_of_lid ftv) t)
      end
    | _ -> None

let lookup_effect_lid env (ftv:lident) : typ =
  match try_lookup_effect_lid env ftv with
    | None -> raise_error (name_not_found ftv) (range_of_lid ftv)
    | Some k -> k

let lookup_effect_abbrev env (univ_insts:universes) lid0 =
  match lookup_qname env lid0 with
    | Some (Inr ({ sigel = Sig_effect_abbrev (lid, univs, binders, c, _); sigquals = quals }, None), _) ->
      let lid = Ident.set_lid_range lid (Range.set_use_range (Ident.range_of_lid lid) (Range.use_range (Ident.range_of_lid lid0))) in
      if quals |> BU.for_some (function Irreducible -> true | _ -> false)
      then None
      else let insts = if List.length univ_insts = List.length univs
                       then univ_insts
                       else failwith (BU.format3 "(%s) Unexpected instantiation of effect %s with %s universes"
                                            (Range.string_of_range (get_range env))
                                            (Print.lid_to_string lid)
                                            (List.length univ_insts |> BU.string_of_int)) in
           begin match binders, univs with
             | [], _ -> failwith "Unexpected effect abbreviation with no arguments"
             | _, _::_::_ ->
                failwith (BU.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes"
                           (Print.lid_to_string lid) (string_of_int <| List.length univs))
             | _ -> let _, t = inst_tscheme_with (univs, U.arrow binders c) insts in
                    let t = Subst.set_use_range (range_of_lid lid) t in
                    begin match (Subst.compress t).n with
                        | Tm_arrow(binders, c) ->
                          Some (binders, c)
                        | _ -> failwith "Impossible"
                    end
          end
    | _ -> None

let norm_eff_name =
   fun env (l:lident) ->
       let rec find l =
           match lookup_effect_abbrev env [U_unknown] l with //universe doesn't matter here; we're just normalizing the name
            | None -> None
            | Some (_, c) ->
                let l = U.comp_effect_name c in
                match find l with
                    | None -> Some l
                    | Some l' -> Some l' in
       let res = match BU.smap_try_find env.normalized_eff_names (string_of_lid l) with
            | Some l -> l
            | None ->
              begin match find l with
                        | None -> l
                        | Some m -> BU.smap_add env.normalized_eff_names (string_of_lid l) m;
                                    m
              end in
       Ident.set_lid_range res (range_of_lid l)

let is_erasable_effect env l =
  l
  |> norm_eff_name env
  |> (fun l -> lid_equals l Const.effect_GHOST_lid ||
           S.lid_as_fv l (Delta_constant_at_level 0) None
           |> fv_has_erasable_attr env)

let rec non_informative env t =
    match (U.unrefine t).n with
    | Tm_type _ -> true
    | Tm_fvar fv ->
      fv_eq_lid fv Const.unit_lid
      || fv_eq_lid fv Const.squash_lid
      || fv_eq_lid fv Const.erased_lid
      || fv_has_erasable_attr env fv
    | Tm_app(head, _) -> non_informative env head
    | Tm_uinst (t, _) -> non_informative env t
    | Tm_arrow(_, c) ->
      (is_pure_or_ghost_comp c && non_informative env (comp_result c))
      || is_erasable_effect env (comp_effect_name c)
    | _ -> false

let num_effect_indices env name r =
  let sig_t = name |> lookup_effect_lid env |> SS.compress in
  match sig_t.n with
  | Tm_arrow (_a::bs, _) -> List.length bs
  | _ ->
    raise_error (Errors.Fatal_UnexpectedSignatureForMonad,
      BU.format2 "Signature for %s not an arrow (%s)" (Ident.string_of_lid name)
      (Print.term_to_string sig_t)) r


let lookup_effect_quals env l =
    let l = norm_eff_name env l in
    match lookup_qname env l with
    | Some (Inr ({ sigel = Sig_new_effect _; sigquals=q}, _), _) ->
      q
    | _ -> []

let lookup_projector env lid i =
    let fail () = failwith (BU.format2 "Impossible: projecting field #%s from constructor %s is undefined" (BU.string_of_int i) (Print.lid_to_string lid)) in
    let _, t = lookup_datacon env lid in
    match (compress t).n with
        | Tm_arrow(binders, _) ->
          if ((i < 0) || i >= List.length binders) //this has to be within bounds!
          then fail ()
          else let b = List.nth binders i in
               U.mk_field_projector_name lid b.binder_bv i
        | _ -> fail ()

let is_projector env (l:lident) : bool =
    match lookup_qname env l with
        | Some (Inr ({ sigel = Sig_declare_typ(_, _, _); sigquals=quals }, _), _) ->
          BU.for_some (function Projector _ -> true | _ -> false) quals
        | _ -> false

let is_datacon env lid =
  match lookup_qname env lid with
    | Some (Inr ({ sigel = Sig_datacon (_, _, _, _, _, _) }, _), _) -> true
    | _ -> false

let is_record env lid =
  match lookup_qname env lid with
    | Some (Inr ({ sigel = Sig_inductive_typ(_, _, _, _, _, _); sigquals=quals }, _), _) ->
        BU.for_some (function RecordType _ | RecordConstructor _ -> true | _ -> false) quals
    | _ -> false

let qninfo_is_action (qninfo : qninfo) =
    match qninfo with
        | Some (Inr ({ sigel = Sig_let(_, _); sigquals = quals }, _), _) ->
            BU.for_some (function Action _ -> true | _ -> false) quals
        | _ -> false

let is_action env lid =
    qninfo_is_action <| lookup_qname env lid

let is_interpreted =
    let interpreted_symbols =
       [Const.op_Eq;
        Const.op_notEq;
        Const.op_LT;
        Const.op_LTE;
        Const.op_GT;
        Const.op_GTE;
        Const.op_Subtraction;
        Const.op_Minus;
        Const.op_Addition;
        Const.op_Multiply;
        Const.op_Division;
        Const.op_Modulus;
        Const.op_And;
        Const.op_Or;
        Const.op_Negation] in
    fun (env:env) head ->
        match (U.un_uinst head).n with
        | Tm_fvar fv ->
            (match fv.fv_delta with
             | Delta_equational_at_level _ -> true
             | _ -> false) ||
            BU.for_some (Ident.lid_equals fv.fv_name.v) interpreted_symbols
        | _ -> false

let is_irreducible env l =
    match lookup_qname env l with
    | Some (Inr (se, _), _) ->
      BU.for_some (function Irreducible -> true | _ -> false) se.sigquals
    | _ -> false

let is_type_constructor env lid =
    let mapper x =
        match fst x with
        | Inl _ -> Some false
        | Inr (se, _) ->
           begin match se.sigel with
            | Sig_declare_typ _ ->
              Some (List.contains New se.sigquals)
            | Sig_inductive_typ _ ->
              Some true
            | _ -> Some false
           end in
    match BU.bind_opt (lookup_qname env lid) mapper with
      | Some b -> b
      | None -> false

let num_inductive_ty_params env lid =
  match lookup_qname env lid with
  | Some (Inr ({ sigel = Sig_inductive_typ (_, _, tps, _, _, _) }, _), _) ->
    Some (List.length tps)
  | _ ->
    None

////////////////////////////////////////////////////////////
// Operations on the monad lattice                        //
////////////////////////////////////////////////////////////
let effect_decl_opt env l =
  env.effects.decls |> BU.find_opt (fun (d, _) -> lid_equals d.mname l)

let get_effect_decl env l =
  match effect_decl_opt env l with
    | None -> raise_error (name_not_found l) (range_of_lid l)
    | Some md -> fst md

let get_lid_valued_effect_attr env
  (eff_lid attr_name_lid:lident)
  (default_if_attr_has_no_arg:option lident)
  : option lident
  = let attr_args =
      eff_lid |> norm_eff_name env
              |> lookup_attrs_of_lid env
              |> BU.dflt []
              |> U.get_attribute attr_name_lid in
    match attr_args with
    | None -> None
    | Some args ->
      if List.length args = 0
      then default_if_attr_has_no_arg
      else args
           |> List.hd
           |> (fun (t, _) ->
              match (SS.compress t).n with
              | Tm_constant (FStar.Const.Const_string (s, _)) -> s |> Ident.lid_of_str |> Some
              | _ ->
                raise_error
                  (Errors.Fatal_UnexpectedEffect,
                   BU.format2 "The argument for the effect attribute for %s is not a constant string, it is %s\n"
                     (string_of_lid eff_lid)
                     (Print.term_to_string t)) t.pos)

let get_default_effect env lid =
  get_lid_valued_effect_attr env lid Const.default_effect_attr None

let get_top_level_effect env lid =
  get_lid_valued_effect_attr env lid Const.top_level_effect_attr (Some lid)

let is_layered_effect env l =
  l |> get_effect_decl env |> U.is_layered

let identity_mlift : mlift =
  { mlift_wp=(fun _ c -> c, trivial_guard);
    mlift_term=Some (fun _ _ e -> return_all e) }

let join_opt env (l1:lident) (l2:lident) : option (lident * mlift * mlift) =
  if lid_equals l1 l2
  then Some (l1, identity_mlift, identity_mlift)
  else if lid_equals l1 Const.effect_GTot_lid && lid_equals l2 Const.effect_Tot_lid
       || lid_equals l2 Const.effect_GTot_lid && lid_equals l1 Const.effect_Tot_lid
  then Some (Const.effect_GTot_lid, identity_mlift, identity_mlift)
  else match env.effects.joins |> BU.find_opt (fun (m1, m2, _, _, _) -> lid_equals l1 m1 && lid_equals l2 m2) with
        | None -> None
        | Some (_, _, m3, j1, j2) -> Some (m3, j1, j2)

let join env l1 l2 : (lident * mlift * mlift) =
  match join_opt env l1 l2 with
  | None ->
    raise_error (Errors.Fatal_EffectsCannotBeComposed,
      (BU.format2 "Effects %s and %s cannot be composed"
        (Print.lid_to_string l1) (Print.lid_to_string l2))) env.range
  | Some t -> t

let monad_leq env l1 l2 : option edge =
  if lid_equals l1 l2
  || (lid_equals l1 Const.effect_Tot_lid && lid_equals l2 Const.effect_GTot_lid)
  then Some ({msource=l1; mtarget=l2; mlift=identity_mlift; mpath=[]})
  else env.effects.order |> BU.find_opt (fun e -> lid_equals l1 e.msource && lid_equals l2 e.mtarget)

let wp_sig_aux decls m =
  match decls |> BU.find_opt (fun (d, _) -> lid_equals d.mname m) with
  | None -> failwith (BU.format1 "Impossible: declaration for monad %s not found" (string_of_lid m))
  | Some (md, _q) ->
    (*
     * AR: this code used to be inst_tscheme md.univs md.signature
     *     i.e. implicitly there was an assumption that ed.binders is empty
     *     now when signature is itself a tscheme, this just translates to the following
     *)
    let _, s = inst_tscheme md.signature in
    let s = Subst.compress s in
    match md.binders, s.n with
      | [], Tm_arrow([b; wp_b], c) when (is_teff (comp_result c)) -> b.binder_bv, wp_b.binder_bv.sort
      | _ -> failwith "Impossible"

let wp_signature env m = wp_sig_aux env.effects.decls m

let comp_to_comp_typ (env:env) c =
    let c = match c.n with
            | Total (t, None) ->
              let u = env.universe_of env t in
              S.mk_Total' t (Some u)
            | GTotal (t, None) ->
              let u = env.universe_of env t in
              S.mk_GTotal' t (Some u)
            | _ -> c in
    U.comp_to_comp_typ c

let rec unfold_effect_abbrev env comp =
  let c = comp_to_comp_typ env comp in
  match lookup_effect_abbrev env c.comp_univs c.effect_name with
    | None -> c
    | Some (binders, cdef) ->
      let binders, cdef = Subst.open_comp binders cdef in
      if List.length binders <> List.length c.effect_args + 1
      then raise_error (Errors.Fatal_ConstructorArgLengthMismatch, (BU.format3 "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                                (BU.string_of_int (List.length binders))
                                (BU.string_of_int (List.length c.effect_args + 1))
                                (Print.comp_to_string (S.mk_Comp c)))) comp.pos;
      let inst = List.map2 (fun b (t, _) -> NT(b.binder_bv, t)) binders (as_arg c.result_typ::c.effect_args) in
      let c1 = Subst.subst_comp inst cdef in
      let c = {comp_to_comp_typ env c1 with flags=c.flags} |> mk_Comp in
      unfold_effect_abbrev env c

let effect_repr_aux only_reifiable env c u_res =
  let check_partial_application eff_name (args:args) =
    let r = get_range env in
    let given, expected = List.length args, num_effect_indices env eff_name r in
    if given = expected  then ()
    else
      let message = BU.format3 "Not enough arguments for effect %s, \
        This usually happens when you use a partially applied DM4F effect, \
        like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
        (Ident.string_of_lid eff_name) (string_of_int given) (string_of_int expected) in
      raise_error (Errors.Fatal_NotEnoughArgumentsForEffect, message) r in

  let effect_name = norm_eff_name env (U.comp_effect_name c) in
  match effect_decl_opt env effect_name with
  | None -> None
  | Some (ed, _) ->
    match ed |> U.get_eff_repr with
    | None -> None
    | Some ts ->
      let c = unfold_effect_abbrev env c in
      let res_typ = c.result_typ in
      let repr = inst_effect_fun_with [u_res] env ed ts in
      check_partial_application effect_name c.effect_args;
      Some (S.mk (Tm_app (repr, ((res_typ |> S.as_arg)::c.effect_args))) (get_range env))

let effect_repr env c u_res : option term = effect_repr_aux false env c u_res

(* [is_reifiable_* env x] returns true if the effect name/computational *)
(* effect (of a body or codomain of an arrow) [x] is reifiable. *)

(* [is_user_reifiable_* env x] is more restrictive, and only allows *)
(* reifying effects marked with the `reifiable` keyword. (For instance, TAC *)
(* is reifiable but not user-reifiable.) *)

let is_user_reifiable_effect (env:env) (effect_lid:lident) : bool =
    let effect_lid = norm_eff_name env effect_lid in
    let quals = lookup_effect_quals env effect_lid in
    List.contains Reifiable quals

let is_user_reflectable_effect (env:env) (effect_lid:lident) : bool =
    let effect_lid = norm_eff_name env effect_lid in
    let quals = lookup_effect_quals env effect_lid in
    quals |> List.existsb (function Reflectable _ -> true | _ -> false)

let is_total_effect (env:env) (effect_lid:lident) : bool =
    let effect_lid = norm_eff_name env effect_lid in
    let quals = lookup_effect_quals env effect_lid in
    List.contains TotalEffect quals

let is_reifiable_effect (env:env) (effect_lid:lident) : bool =
    let effect_lid = norm_eff_name env effect_lid in
    is_user_reifiable_effect env effect_lid
    || Ident.lid_equals effect_lid Const.effect_TAC_lid

let is_reifiable_rc (env:env) (c:S.residual_comp) : bool =
    is_reifiable_effect env c.residual_effect

let is_reifiable_comp (env:env) (c:S.comp) : bool =
    match c.n with
    | Comp ct -> is_reifiable_effect env ct.effect_name
    | _ -> false

let is_reifiable_function (env:env) (t:S.term) : bool =
    match (compress t).n with
    | Tm_arrow (_, c) -> is_reifiable_comp env c
    | _ -> false

let reify_comp env c u_c : term =
    let l = U.comp_effect_name c in
    if not (is_reifiable_effect env l) then
        raise_error (Errors.Fatal_EffectCannotBeReified, (BU.format1 "Effect %s cannot be reified" (Ident.string_of_lid l))) (get_range env);
    match effect_repr_aux true env c u_c with
    | None -> failwith "internal error: reifiable effect has no repr?"
    | Some tm -> tm


///////////////////////////////////////////////////////////
// Introducing identifiers and updating the environment   //
////////////////////////////////////////////////////////////

// The environment maintains the invariant that gamma is of the form:
//   l_1 ... l_n val_1 ... val_n
// where l_i is a local binding and val_i is a top-level binding.
//
//let push_in_gamma env s =
//  let rec push x rest =
//    match rest with
//    | Binding_sig _ :: _ ->
//        x :: rest
//    | [] ->
//        [ x ]
//    | local :: rest ->
//        local :: push x rest
//  in
//  env.tc_hooks.tc_push_in_gamma_hook env s;
//  { env with gamma = push s env.gamma }

// This function assumes that, in the case that the environment contains local
// bindings _and_ we push a top-level binding, then the top-level binding does
// not capture any of the local bindings (duh).
let push_sigelt env s =
  let sb = (lids_of_sigelt s, s) in
  let env = {env with gamma_sig = sb::env.gamma_sig} in
  add_sigelt env s;
  env.tc_hooks.tc_push_in_gamma_hook env (Inr sb);
  env

let push_new_effect env (ed, quals) =
  let effects = {env.effects with decls=env.effects.decls@[(ed, quals)]} in
  {env with effects=effects}

let exists_polymonadic_bind env m n =
  match env.effects.polymonadic_binds
        |> BU.find_opt (fun (m1, n1, _, _) -> lid_equals m m1 && lid_equals n n1) with
  | Some (_, _, p, t) -> Some (p, t)
  | _ -> None

let exists_polymonadic_subcomp env m n =
  match env.effects.polymonadic_subcomps
        |> BU.find_opt (fun (m1, n1, _) -> lid_equals m m1 && lid_equals n n1) with
  | Some (_, _, ts) -> Some ts
  | _ -> None

let print_effects_graph env =
  let eff_name lid = lid |> ident_of_lid |> string_of_id in
  let path_str path = path |> List.map eff_name |> String.concat ";" in

  //
  //Right now the values in the map are just ""
  //
  //But it may be range or something else if we wanted to dump it in the dot graph
  //
  let pbinds : smap string = smap_create 10 in

  //
  //The keys in the map are sources
  //
  //Each source is mapped to a map, whose keys are targets, and values are the path strings
  //
  let lifts : smap (smap string) = smap_create 20 in

  //Similar to pbinds
  let psubcomps : smap string = smap_create 10 in

  //Populate the maps

  //
  //Note that since order, polymonadic_binds, and polymonadic_subcomps are lists,
  //  they may have duplicates (and the typechecker picks the first one)
  //

  env.effects.order |> List.iter (fun ({msource=src; mtarget=tgt; mpath=path}) ->
    let key = eff_name src in
    let m =
      match smap_try_find lifts key with
      | None ->
        let m = smap_create 10 in
        smap_add lifts key m;
        m
      | Some m -> m in
    match smap_try_find m (eff_name tgt) with
    | Some _ -> ()
    | None -> smap_add m (eff_name tgt) (path_str path));

  env.effects.polymonadic_binds |> List.iter (fun (m, n, p, _) ->
    let key = BU.format3 "%s, %s |> %s" (eff_name m) (eff_name n) (eff_name p) in
    smap_add pbinds key "");

  env.effects.polymonadic_subcomps |> List.iter (fun (m, n, _) ->
    let key = BU.format2 "%s <: %s" (eff_name m) (eff_name n) in
    smap_add psubcomps key "");

  //
  //Dump the dot graph
  //
  //Interesting bit of trivia:
  //  the cluster_ in the names of the subgraphs is important,
  //  if the name does not begin like this, dot rendering does not draw boxes
  //    around subgraphs (!)
  //

  BU.format3 "digraph {\n\
    label=\"Effects ordering\"\n\
    subgraph cluster_lifts {\n\
      label = \"Lifts\"\n
      %s\n\
    }\n\
    subgraph cluster_polymonadic_binds {\n\
      label = \"Polymonadic binds\"\n\
      %s\n\
    }\n\
    subgraph cluster_polymonadic_subcomps {\n\
      label = \"Polymonadic subcomps\"\n\
      %s\n\
    }}\n"

    ((smap_fold lifts (fun src m s ->
        smap_fold m (fun tgt path s ->
          (BU.format3 "%s -> %s [label=\"%s\"]" src tgt path)::s) s) []) |> String.concat "\n")
    (smap_fold pbinds (fun k _ s -> (BU.format1 "\"%s\" [shape=\"plaintext\"]" k)::s) [] |> String.concat "\n")
    (smap_fold psubcomps (fun k _ s -> (BU.format1 "\"%s\" [shape=\"plaintext\"]" k)::s) [] |> String.concat "\n")

let update_effect_lattice env src tgt st_mlift =
  let compose_edges e1 e2 : edge =
    let composed_lift =
      let mlift_wp env c =
        c |> e1.mlift.mlift_wp env
	  |> (fun (c, g1) -> c |> e2.mlift.mlift_wp env |> (fun (c, g2) -> c, TcComm.conj_guard g1 g2)) in
      let mlift_term =
        match e1.mlift.mlift_term, e2.mlift.mlift_term with
        | Some l1, Some l2 -> Some (fun u t e -> l2 u t (l1 u t e))
        | _ -> None
      in
      { mlift_wp=mlift_wp ; mlift_term=mlift_term}
    in
    { msource=e1.msource;
      mtarget=e2.mtarget;
      mlift=composed_lift;
      mpath=e1.mpath@[e1.mtarget]@e2.mpath}
  in

  let edge = {
    msource=src;
    mtarget=tgt;
    mlift=st_mlift;
    mpath=[];
  } in

  let id_edge l = {
    msource=src;
    mtarget=tgt;
    mlift=identity_mlift;
    mpath=[];
  } in

  let find_edge order (i, j) =
    if lid_equals i j
    then id_edge i |> Some
    else order |> BU.find_opt (fun e -> lid_equals e.msource i && lid_equals e.mtarget j) in

  let ms = env.effects.decls |> List.map (fun (e, _) -> e.mname) in

  (*
   * AR: we compute all the new edges induced by the input edge
   *     and add them to the head of the edges list
   *
   *     in other words, previous paths are overwritten
   *)

  //all nodes i such that i <> src and i ~> src is an edge
  let all_i_src = ms |> List.fold_left (fun edges i ->
    if lid_equals i edge.msource then edges
    else match find_edge env.effects.order (i, edge.msource) with
         | Some e -> e::edges
         | None -> edges) [] in

  //all nodes j such that j <> tgt and tgt ~> j is an edge
  let all_tgt_j = ms |> List.fold_left (fun edges j ->
    if lid_equals edge.mtarget j then edges
    else match find_edge env.effects.order (edge.mtarget, j) with
         | Some e -> e::edges
         | None -> edges) [] in

  let check_cycle src tgt =
    if lid_equals src tgt
    then raise_error (Errors.Fatal_Effects_Ordering_Coherence,
           BU.format3 "Adding an edge %s~>%s induces a cycle %s"
             (Ident.string_of_lid edge.msource)
             (Ident.string_of_lid edge.mtarget)
             (Ident.string_of_lid src)) env.range in

  //
  //There are three types of new edges now:
  //
  //  - From i to edge target
  //  - From edge source to j
  //  - From i to j
  //

  let new_i_edge_target = List.fold_left (fun edges i_src ->
    check_cycle i_src.msource edge.mtarget;
    (compose_edges i_src edge)::edges) [] all_i_src in

  let new_edge_source_j = List.fold_left (fun edges tgt_j ->
    check_cycle edge.msource tgt_j.mtarget;
    (compose_edges edge tgt_j)::edges) [] all_tgt_j in

  let new_i_j = List.fold_left (fun edges i_src ->
    List.fold_left (fun edges tgt_j ->
      check_cycle i_src.msource tgt_j.mtarget;
      (compose_edges (compose_edges i_src edge) tgt_j)::edges) edges all_tgt_j) [] all_i_src in

  let new_edges = edge::(new_i_edge_target@new_edge_source_j@new_i_j) in

  //Add new edges to the front of the list, shadowing existing ones

  let order = new_edges@env.effects.order in

  order |> List.iter (fun edge ->
    if Ident.lid_equals edge.msource Const.effect_DIV_lid
    && lookup_effect_quals env edge.mtarget |> List.contains TotalEffect
    then raise_error (Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                      (BU.format1 "Divergent computations cannot be included in an effect %s marked 'total'"
                        (string_of_lid edge.mtarget))) (get_range env));

  //
  //Compute upper bounds
  //
  //Addition of an edge may change upper bounds,
  // that's ok, as long as it is unique in the new graph
  //
  let joins =
    //
    //A map where we populate all upper bounds for each pair of effects
    //
    let ubs : smap (list (lident * lident * lident * mlift * mlift)) =
      BU.smap_create 10 in
    let add_ub i j k ik jk =
      let key = string_of_lid i ^ ":" ^ string_of_lid j in
      let v =
        match smap_try_find ubs key with
        | Some ubs -> (i, j, k, ik, jk)::ubs
        | None -> [i, j, k, ik, jk] in

      smap_add ubs key v in

    //Populate ubs
    ms |> List.iter (fun i ->
      ms |> List.iter (fun j ->
        if lid_equals i j then ()
        else ms |> List.iter (fun k ->
               match find_edge order (i, k), find_edge order (j, k) with
               | Some ik, Some jk -> add_ub i j k ik.mlift jk.mlift
               | _ -> ())));

    //
    //Fold over the map
    //
    //For each pair of effects (i.e. key in the ubs map),
    //  make sure there is a unique lub
    //
    smap_fold ubs (fun s l joins ->
      //Filter entries that have an edge to every other entry
      let lubs = List.filter (fun (i, j, k, ik, jk) ->
        List.for_all (fun (_, _, k', _, _) ->
          find_edge order (k, k') |> is_some) l) l in
      //Make sure there is only one such entry
      if List.length lubs <> 1
      then raise_error (Errors.Fatal_Effects_Ordering_Coherence,
                        BU.format1 "Effects %s have incomparable upper bounds" s)
                       env.range
      else lubs@joins) [] in

  let effects = {env.effects with order=order; joins=joins} in
  {env with effects=effects}

(*
 * We allow overriding a previously defined poymonadic bind/subcomps
 *   between the same effects
 *
 * Also, polymonadic versions always take precedence over the effects graph
 *)

let add_polymonadic_bind env m n p ty =
  { env with
    effects = ({ env.effects with polymonadic_binds = (m, n, p, ty)::env.effects.polymonadic_binds }) }

let add_polymonadic_subcomp env m n ts =
  { env with
    effects = ({ env.effects with
                 polymonadic_subcomps = (m, n, ts)::env.effects.polymonadic_subcomps }) }

let push_local_binding env b =
  {env with gamma=b::env.gamma}

let push_bv env x = push_local_binding env (Binding_var x)

let push_bvs env bvs =
    List.fold_left (fun env bv -> push_bv env bv) env bvs

let pop_bv env =
    match env.gamma with
    | Binding_var x::rest -> Some (x, {env with gamma=rest})
    | _ -> None

let push_binders env (bs:binders) =
    List.fold_left (fun env b -> push_bv env b.binder_bv) env bs

let binding_of_lb (x:lbname) t = match x with
  | Inl x ->
    assert (fst t = []);
    let x = {x with sort=snd t} in
    Binding_var x
  | Inr fv ->
    Binding_lid(fv.fv_name.v, t)

let push_let_binding env lb ts =
    push_local_binding env (binding_of_lb lb ts)

let push_univ_vars (env:env_t) (xs:univ_names) : env_t =
    List.fold_left (fun env x -> push_local_binding env (Binding_univ x)) env xs

let open_universes_in env uvs terms =
    let univ_subst, univ_vars = Subst.univ_var_opening uvs in
    let env' = push_univ_vars env univ_vars in
    env', univ_vars, List.map (Subst.subst univ_subst) terms

let set_expected_typ env t =
  //false bit says that use subtyping
  {env with expected_typ = Some (t, false)}

let set_expected_typ_maybe_eq env t use_eq =
  {env with expected_typ = Some (t, use_eq)}

let expected_typ env = match env.expected_typ with
  | None -> None
  | Some t -> Some t

let clear_expected_typ (env_: env): env * option (typ * bool) =
    {env_ with expected_typ=None}, expected_typ env_

let finish_module =
    let empty_lid = lid_of_ids [id_of_text ""] in
    fun env m ->
      let sigs =
        if lid_equals m.name Const.prims_lid
        then env.gamma_sig |> List.map snd |> List.rev
        else m.declarations  in
      add_sigelts env sigs;
      {env with
        curmodule=empty_lid;
        gamma=[];
        gamma_sig=[];
        modules=m::env.modules}

////////////////////////////////////////////////////////////
// Collections from the environment                       //
////////////////////////////////////////////////////////////
let uvars_in_env env =
  let no_uvs = Free.new_uv_set () in
  let ext out uvs = BU.set_union out uvs in
  let rec aux out g = match g with
    | [] -> out
    | Binding_univ _ :: tl -> aux out tl
    | Binding_lid(_, (_, t))::tl
    | Binding_var({sort=t})::tl -> aux (ext out (Free.uvars t)) tl
  in
  aux no_uvs env.gamma

let univ_vars env =
    let no_univs = Free.new_universe_uvar_set () in
    let ext out uvs = BU.set_union out uvs in
    let rec aux out g = match g with
      | [] -> out
      | Binding_univ _ :: tl -> aux out tl
      | Binding_lid(_, (_, t))::tl
      | Binding_var({sort=t})::tl -> aux (ext out (Free.univs t)) tl
    in
    aux no_univs env.gamma

let univnames env =
    let no_univ_names = Syntax.no_universe_names in
    let ext out uvs = BU.set_union out uvs in
    let rec aux out g = match g with
        | [] -> out
        | Binding_univ uname :: tl -> aux (BU.set_add uname out) tl
        | Binding_lid(_, (_, t))::tl
        | Binding_var({sort=t})::tl -> aux (ext out (Free.univnames t)) tl
    in
    aux no_univ_names env.gamma

let bound_vars_of_bindings bs =
  bs |> List.collect (function
        | Binding_var x -> [x]
        | Binding_lid _
        | Binding_univ _ -> [])

let binders_of_bindings bs = bound_vars_of_bindings bs |> List.map Syntax.mk_binder |> List.rev

let bound_vars env = bound_vars_of_bindings env.gamma

let all_binders env = binders_of_bindings env.gamma

let print_gamma gamma =
    (gamma |> List.map (function
        | Binding_var x -> "Binding_var (" ^ (Print.bv_to_string x) ^ ":" ^ (Print.term_to_string x.sort) ^ ")"
        | Binding_univ u -> "Binding_univ " ^ (string_of_id u)
        | Binding_lid (l, _) -> "Binding_lid " ^ (Ident.string_of_lid l)))//  @
    // (env.gamma_sig |> List.map (fun (ls, _) ->
    //     "Binding_sig " ^ (ls |> List.map Ident.string_of_lid |> String.concat ", ")
    // ))
    |> String.concat "::\n"

let string_of_delta_level = function
  | NoDelta -> "NoDelta"
  | InliningDelta -> "Inlining"
  | Eager_unfolding_only -> "Eager_unfolding_only"
  | Unfold d -> "Unfold " ^ Print.delta_depth_to_string d

let lidents env : list lident =
  let keys = List.collect fst env.gamma_sig in
  BU.smap_fold (sigtab env) (fun _ v keys -> U.lids_of_sigelt v@keys) keys

let should_enc_path env path =
    let rec str_i_prefix xs ys =
        match xs, ys with
        | [], _ -> true
        | x::xs, y::ys -> String.lowercase x = String.lowercase y && str_i_prefix xs ys
        | _, _ -> false
    in
    match FStar.Compiler.List.tryFind (fun (p, _) -> str_i_prefix p path) env.proof_ns with
    | None -> false
    | Some (_, b) -> b

let should_enc_lid env lid =
    should_enc_path env (path_of_lid lid)

let cons_proof_ns b e path =
    { e with proof_ns = (path,b) :: e.proof_ns }

// F# forces me to fully apply this... ugh
let add_proof_ns e path = cons_proof_ns true  e path
let rem_proof_ns e path = cons_proof_ns false e path
let get_proof_ns e = e.proof_ns
let set_proof_ns ns e = {e with proof_ns = ns}

let unbound_vars (e : env) (t : term) : BU.set bv =
    // FV(t) \ Vars(Γ)
    List.fold_left (fun s bv -> BU.set_remove bv s) (Free.names t) (bound_vars e)

let closed (e : env) (t : term) =
    BU.set_is_empty (unbound_vars e t)

let closed' (t : term) =
    BU.set_is_empty (Free.names t)

let string_of_proof_ns env =
    let aux (p,b) =
        if p = [] && b then "*"
        else (if b then "+" else "-")^Ident.text_of_path p
    in
    List.map aux env.proof_ns
    |> List.rev
    |> String.concat " "


(* ------------------------------------------------*)
(* <guard_formula ops> Operations on guard_formula *)
(* ------------------------------------------------*)
let guard_of_guard_formula g = {
  guard_f=g;
  deferred=[];
  deferred_to_tac=[];
  univ_ineqs=([], []);
  implicits=[]
}

let guard_form g = g.guard_f

let is_trivial g = match g with
    | {guard_f=Trivial; deferred=[]; univ_ineqs=([], []); implicits=i} ->
      i |> BU.for_all (fun imp ->
           (U.ctx_uvar_should_check imp.imp_uvar=Allow_unresolved)
           || (match Unionfind.find imp.imp_uvar.ctx_uvar_head with
               | Some _ -> true
               | None -> false))
    | _ -> false

let is_trivial_guard_formula g = match g with
    | {guard_f=Trivial} -> true
    | _ -> false

let trivial_guard = TcComm.trivial_guard

let abstract_guard_n bs g =
    match g.guard_f with
    | Trivial -> g
    | NonTrivial f ->
        let f' = U.abs bs f (Some (U.residual_tot U.ktype0)) in
        ({ g with guard_f = NonTrivial f' })

let abstract_guard b g =
    abstract_guard_n [b] g

let def_check_vars_in_set rng msg vset t =
    if Options.defensive () then begin
        let s = Free.names t in
        if not (BU.set_is_empty <| BU.set_difference s vset)
        then Errors.log_issue rng
                    (Errors.Warning_Defensive,
                     BU.format3 "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                                      msg
                                      (Print.term_to_string t)
                                      (BU.set_elements s |> Print.bvs_to_string ",\n\t"))
    end


let too_early_in_prims env =
  not (lid_exists env Const.effect_GTot_lid)

let def_check_closed_in rng msg l t =
    if not (Options.defensive ()) then () else
    def_check_vars_in_set rng msg (BU.as_set l Syntax.order_bv) t

let def_check_closed_in_env rng msg e t =
    if not (Options.defensive ()) then () else
    def_check_closed_in rng msg (bound_vars e) t

let def_check_guard_wf rng msg env g =
    match g.guard_f with
    | Trivial -> ()
    | NonTrivial f -> def_check_closed_in_env rng msg env f

let apply_guard g e = match g.guard_f with
  | Trivial -> g
  | NonTrivial f -> {g with guard_f=NonTrivial <| mk (Tm_app(f, [as_arg e])) f.pos}

let map_guard g map = match g.guard_f with
  | Trivial -> g
  | NonTrivial f -> {g with guard_f=NonTrivial (map f)}

let always_map_guard g map = match g.guard_f with
  | Trivial -> {g with guard_f=NonTrivial (map U.t_true)}
  | NonTrivial f -> {g with guard_f=NonTrivial (map f)}

let trivial t = match t with
  | Trivial -> ()
  | NonTrivial _ -> failwith "impossible"

let check_trivial t = TcComm.check_trivial t

let conj_guard g1 g2 = TcComm.conj_guard g1 g2
let conj_guards gs = TcComm.conj_guards gs
let imp_guard g1 g2 = TcComm.imp_guard g1 g2


let close_guard_univs us bs g =
    match g.guard_f with
    | Trivial -> g
    | NonTrivial f ->
      let f =
          List.fold_right2 (fun u b f ->
              if Syntax.is_null_binder b then f
              else U.mk_forall u b.binder_bv f)
        us bs f in
    {g with guard_f=NonTrivial f}

let close_forall env bs f =
    List.fold_right (fun b f ->
            if Syntax.is_null_binder b then f
            else let u = env.universe_of env b.binder_bv.sort in
                 U.mk_forall u b.binder_bv f)
    bs f

let close_guard env binders g =
    match g.guard_f with
    | Trivial -> g
    | NonTrivial f ->
      {g with guard_f=NonTrivial (close_forall env binders f)}

(* ------------------------------------------------*)
(* </guard_formula ops>                            *)
(* ------------------------------------------------*)

(* Generating new implicit variables *)
let new_tac_implicit_var reason r env k should_check meta apply_tac_deps =
    match U.destruct k FStar.Parser.Const.range_of_lid with
     | Some [_; (tm, _)] ->
       let t = S.mk (S.Tm_constant (FStar.Const.Const_range tm.pos)) tm.pos in
       t, [], trivial_guard

     | _ ->
      let binders = all_binders env in
      let gamma = env.gamma in
      let decoration = {
             uvar_decoration_typ = k;
             uvar_decoration_should_check = should_check;
          }
      in
      let ctx_uvar = {
          ctx_uvar_head=FStar.Syntax.Unionfind.fresh decoration r;
          ctx_uvar_gamma=gamma;
          ctx_uvar_binders=binders;
          ctx_uvar_reason=reason;
          ctx_uvar_range=r;
          ctx_uvar_meta=meta;

          ctx_uvar_apply_tac_prefix=apply_tac_deps;
      } in
      check_uvar_ctx_invariant reason r true gamma binders;
      let t = mk (Tm_uvar (ctx_uvar, ([], NoUseRange))) r in
      let imp = { imp_reason = reason
                ; imp_tm     = t
                ; imp_uvar   = ctx_uvar
                ; imp_range  = r
                } in
      if debug env (Options.Other "ImplicitTrace") then
        BU.print1 "Just created uvar for implicit {%s}\n" (Print.uvar_to_string ctx_uvar.ctx_uvar_head);
      let g = {trivial_guard with implicits=[imp]} in
      t, [(ctx_uvar, r)], g

let new_implicit_var_aux reason r env k should_check meta =
  new_tac_implicit_var reason r env k should_check meta []

(***************************************************)

(*
 * The Allow_untyped is a bit unfortunate here. But here is an explanation and plan to remove it:
 *
 * This gadget is used to create uvars when applying layered effect combinators
 * These uvars are typically for layered effect indices (or their subterms),
 *   which are analogous to wps in the wp-based effects
 *
 * Suppose we use Strict instead of Allow_untyped, that has two problems:
 *
 * (a) Performance: These uvars (indices) are repetedly resolved by the unifier and
 *     then typechecked (as done for normal implicits). If these terms are big, this
 *     can cause significant slowdowns.
 *
 *     If some day we have memoization in the typechecker, then this slowdown can go away.
 *
 * (b) Convincing the typechecker of their well-typedness: The layered effect indices (and wps)
 *     are many times constructed by the typechecker, and so far, there is no guarantee that they
 *     can be typechecked by the typechecker. For example, in the case of wp-based effects,
 *     the typechecker constructs wps by applying combinators, but these terms are often not typechecked
 *     again (even in 2-phase TC, there inference of wp is anyway out of scope). Analogous reasoning
 *     for layered effect indices. While it would be awesome if we could maintain this hygiene,
 *     it's not there right now. And it may not always be possible too (e.g. using projectors in the
 *     branch VCs).
 *
 * As a result for now we use Allow_untyped here, and TRUST the unifier to do the right thing.
 * When we have memoization, we can move to Strict and then it would be finding ill-typed instances
 *   one-by-one and fixing them.
 *
 * To guard against misuses of this, we typecheck the layered effect combinator types in a strict
 *   mode (with no smt and subtyping)
 *)
let uvars_for_binders env (bs:S.binders) substs reason r =
  bs |> List.fold_left (fun (substs, uvars, g) b ->
    let sort = SS.subst substs b.binder_bv.sort in

    let ctx_uvar_meta_t =
      match b.binder_qual, b.binder_attrs with
      | Some (Meta t), [] ->
        Some (Ctx_uvar_meta_tac (FStar.Compiler.Dyn.mkdyn env, t))
      | _, t::_ ->
        Some (Ctx_uvar_meta_attr t)
      | _ -> None in

    let t, l_ctx_uvars, g_t = new_implicit_var_aux
      (reason b) r env sort Allow_untyped ctx_uvar_meta_t in

    if debug env <| Options.Other "LayeredEffectsEqns"
    then List.iter (fun (ctx_uvar, _) -> BU.print1 "Layered Effect uvar : %s\n"
      (Print.ctx_uvar_to_string_no_reason ctx_uvar)) l_ctx_uvars;

    substs@[NT (b.binder_bv, t)], uvars@[t], conj_guard g g_t
  ) (substs, [], trivial_guard) |> (fun (_, uvars, g) -> uvars, g)


let pure_precondition_for_trivial_post env u t wp r =
  let trivial_post =
    let post_ts = lookup_definition [NoDelta] env Const.trivial_pure_post_lid |> must in
    let _, post = inst_tscheme_with post_ts [u] in
    S.mk_Tm_app
      post
      [t |> S.as_arg]
      r in
  S.mk_Tm_app
    wp
    [trivial_post |> S.as_arg]
    r


(* <Move> this out of here *)
let dummy_solver = {
    init=(fun _ -> ());
    push=(fun _ -> ());
    pop=(fun _ -> ());
    snapshot=(fun _ -> (0, 0, 0), ());
    rollback=(fun _ _ -> ());
    encode_sig=(fun _ _ -> ());
    preprocess=(fun e g -> [e,g, FStar.Options.peek ()]);
    spinoff_strictly_positive_goals=None;
    handle_smt_goal=(fun e g -> [e,g]);
    solve=(fun _ _ _ -> ());
    finish=(fun () -> ());
    refresh=(fun () -> ());
}
(* </Move> *)

let get_letrec_arity (env:env) (lbname:lbname) : option int =
  let compare_either f1 f2 e1 e2 : bool =
      match e1, e2 with
      | Inl v1, Inl v2 -> f1 v1 v2
      | Inr v1, Inr v2 -> f2 v1 v2
      | _ -> false
  in
  match BU.find_opt (fun (lbname', _, _, _) -> compare_either S.bv_eq S.fv_eq lbname lbname')
                    env.letrecs with
  | Some (_, arity, _, _) -> Some arity
  | None -> None

let fvar_of_nonqual_lid env lid =
    let qn = lookup_qname env lid in
    let dd =
        match delta_depth_of_qninfo_lid lid qn with
        | None -> failwith "Unexpected no delta_depth"
        | Some dd -> dd
    in
    fvar lid dd None

let split_smt_query (e:env) (q:term) 
  : option (list (env & term))
  = match e.solver.spinoff_strictly_positive_goals with
    | None -> None
    | Some p -> Some (p e q)
