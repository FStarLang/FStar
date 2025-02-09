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
module FStarC.TypeChecker.Env

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Syntax.Subst
open FStarC.Syntax.Util
open FStarC.Util
open FStarC.SMap
open FStarC.Ident
open FStarC.Range
open FStarC.Errors
open FStarC.TypeChecker.Common
open FStarC.Class.Setlike

open FStarC.Class.Show
open FStarC.Class.PP
module Listlike = FStarC.Class.Listlike

module S = FStarC.Syntax.Syntax
module SS = FStarC.Syntax.Subst
module BU = FStarC.Util
module U  = FStarC.Syntax.Util
module UF = FStarC.Syntax.Unionfind
module Const = FStarC.Parser.Const
module TcComm = FStarC.TypeChecker.Common

open FStarC.Defensive

let dbg_ImplicitTrace = Debug.get_toggle "ImplicitTrace"
let dbg_LayeredEffectsEqns = Debug.get_toggle "LayeredEffectsEqns"

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
  | UnfoldAttr lids1, UnfoldAttr lids2 -> lids1 =? lids2
  | UnfoldQual strs1, UnfoldQual strs2 -> strs1 =? strs2
  | UnfoldNamespace strs1, UnfoldNamespace strs2 -> strs1 =? strs2
  | DontUnfoldAttr lids1, DontUnfoldAttr lids2 -> lids1 =? lids2
  | _ -> false // fixme: others ?

instance deq_step : deq step = {
  (=?) = eq_step;
}

let rec step_to_string (s:step) : string =
  match s with
  | Beta -> "Beta"
  | Iota -> "Iota"
  | Zeta -> "Zeta"
  | ZetaFull -> "ZetaFull"
  | Exclude s1 -> "Exclude " ^ step_to_string s1
  | Weak -> "Weak"
  | HNF -> "HNF"
  | Primops -> "Primops"
  | Eager_unfolding -> "Eager_unfolding"
  | Inlining -> "Inlining"
  | DoNotUnfoldPureLets -> "DoNotUnfoldPureLets"
  | UnfoldUntil s1 -> "UnfoldUntil " ^ show s1
  | UnfoldOnly lids1 -> "UnfoldOnly " ^ show lids1
  | UnfoldFully lids1 -> "UnfoldFully " ^ show lids1
  | UnfoldAttr lids1 -> "UnfoldAttr " ^ show lids1
  | UnfoldQual strs1 -> "UnfoldQual " ^ show strs1
  | UnfoldNamespace strs1 -> "UnfoldNamespace " ^ show strs1
  | DontUnfoldAttr lids1 -> "DontUnfoldAttr " ^ show lids1
  | PureSubtermsWithinComputations -> "PureSubtermsWithinComputations"
  | Simplify -> "Simplify"
  | EraseUniverses -> "EraseUniverses"
  | AllowUnboundUniverses -> "AllowUnboundUniverses"
  | Reify -> "Reify"
  | CompressUvars -> "CompressUvars"
  | NoFullNorm -> "NoFullNorm"
  | CheckNoUvars -> "CheckNoUvars"
  | Unmeta -> "Unmeta"
  | Unascribe -> "Unascribe"
  | NBE -> "NBE"
  | ForExtraction -> "ForExtraction"
  | Unrefine -> "Unrefine"
  | NormDebug -> "NormDebug"
  | DefaultUnivsToZero -> "DefaultUnivsToZero"
  | Tactics -> "Tactics"

instance showable_step : showable step = {
  show = step_to_string;
}

instance deq_delta_level : deq delta_level = {
  (=?) = (fun x y -> match x, y with
    | NoDelta, NoDelta -> true
    | InliningDelta, InliningDelta -> true
    | Eager_unfolding_only, Eager_unfolding_only -> true
    | Unfold x, Unfold y -> x =? y
    | _ -> false);
}

instance showable_delta_level : showable delta_level = {
  show = (function
          | NoDelta -> "NoDelta"
          | InliningDelta -> "Inlining"
          | Eager_unfolding_only -> "Eager_unfolding_only"
          | Unfold d -> "Unfold " ^ show d);
}

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

let record_val_for (e:env) (l:lident) : env =
  { e with missing_decl = add l e.missing_decl }

let record_definition_for (e:env) (l:lident) : env =
  { e with missing_decl = remove l e.missing_decl }

let missing_definition_list (e:env) : list lident =
  elems e.missing_decl

type sigtable = SMap.t sigelt

let should_verify env =
    not (Options.lax ())
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
let new_sigtab () = SMap.create default_table_size
let new_gamma_cache () = SMap.create 100

let initial_env deps
  tc_term
  typeof_tot_or_gtot_term
  typeof_tot_or_gtot_term_fastpath
  universe_of
  teq_nosmt_force
  subtype_nosmt_force
  solver module_lid nbe
  core_check : env =
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
    lax_universes=false;
    phase1=false;
    nocoerce=false;
    failhard=false;
    flychecking=false;
    uvar_subtyping=true;
    intactics=false;

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
    qtbl_name_and_index=None, SMap.create 10;
    normalized_eff_names=SMap.create 20;  //20?
    fv_delta_depths = SMap.create 50;
    proof_ns = Options.using_facts_from ();
    synth_hook = (fun e g tau -> failwith "no synthesizer available");
    try_solve_implicits_hook = (fun e tau imps -> failwith "no implicit hook available");
    splice = (fun e is_typed lids tau range -> failwith "no splicer available");
    mpreprocess = (fun e tau tm -> failwith "no preprocessor available");
    postprocess = (fun e tau typ tm -> failwith "no postprocessor available");
    identifier_info=mk_ref FStarC.TypeChecker.Common.id_info_table_empty;
    tc_hooks = default_tc_hooks;
    dsenv = FStarC.Syntax.DsEnv.empty_env deps;
    nbe = nbe;
    strict_args_tab = SMap.create 20;
    erasable_types_tab = SMap.create 20;
    enable_defer_to_tac=true;
    unif_allow_ref_guards=false;
    erase_erasable_args=false;

    core_check;

    missing_decl = empty();
  }

let dsenv env = env.dsenv
let sigtab env = env.sigtab
let attrtab env = env.attrtab
let gamma_cache env = env.gamma_cache

(* Marking and resetting the environment, for the interactive mode *)

let query_indices: ref (list (list (lident & int))) = mk_ref [[]]
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

let stack: ref (list env) = mk_ref []
let push_stack env =
    stack := env::!stack;
    {env with sigtab=SMap.copy (sigtab env);
              attrtab=SMap.copy (attrtab env);
              gamma_cache=SMap.copy (gamma_cache env);
              identifier_info=mk_ref !env.identifier_info;
              qtbl_name_and_index=env.qtbl_name_and_index |> fst, SMap.copy (env.qtbl_name_and_index |> snd);
              normalized_eff_names=SMap.copy env.normalized_eff_names;
              fv_delta_depths=SMap.copy env.fv_delta_depths;
              strict_args_tab=SMap.copy env.strict_args_tab;
              erasable_types_tab=SMap.copy env.erasable_types_tab }

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
    FStarC.Common.runtime_assert
      (BU.physical_equality tcenv.dsenv dsenv)
      "Inconsistent stack state";
    tcenv)

let push env msg = snd (snapshot env msg)
let pop env msg = rollback env.solver msg None

let incr_query_index env =
  let qix = peek_query_indices () in
  match env.qtbl_name_and_index with
  | None, _ -> env
  | Some (l, typ, n), tbl ->
    match qix |> List.tryFind (fun (m, _) -> Ident.lid_equals l m) with
    | None ->
      let next = n + 1 in
      add_query_index (l, next);
      SMap.add tbl (string_of_lid l) next;
      {env with qtbl_name_and_index=Some (l, typ, next), tbl}
    | Some (_, m) ->
      let next = m + 1 in
      add_query_index (l, next);
      SMap.add tbl (string_of_lid l) next;
      {env with qtbl_name_and_index=Some (l, typ, next), tbl}

////////////////////////////////////////////////////////////
// Checking the per-module debug level and position info  //
////////////////////////////////////////////////////////////

let set_range e r = if r=dummyRange then e else {e with range=r}
let get_range e = e.range

instance hasRange_env : hasRange env = {
  pos = get_range;
  setPos = (fun r e -> set_range e r);
}

let toggle_id_info env enabled =
  env.identifier_info :=
    FStarC.TypeChecker.Common.id_info_toggle !env.identifier_info enabled
let insert_bv_info env bv ty =
  env.identifier_info :=
    FStarC.TypeChecker.Common.id_info_insert_bv !env.identifier_info bv ty
let insert_fv_info env fv ty =
  env.identifier_info :=
    FStarC.TypeChecker.Common.id_info_insert_fv !env.identifier_info fv ty
let promote_id_info env ty_map =
  env.identifier_info :=
    FStarC.TypeChecker.Common.id_info_promote !env.identifier_info ty_map

////////////////////////////////////////////////////////////
// Private utilities                                      //
////////////////////////////////////////////////////////////
let modules env = env.modules
let current_module env = env.curmodule
let set_current_module env lid = {env with curmodule=lid}
let has_interface env l = env.modules |> BU.for_some (fun m -> m.is_interface && lid_equals m.name l)
let find_in_sigtab env lid = SMap.try_find (sigtab env) (string_of_lid lid)

//Construct a new universe unification variable
let new_u_univ () = U_unif (UF.univ_fresh Range.dummyRange)

let mk_univ_subst (formals : list univ_name) (us : universes) : list subst_elt =
    assert (List.length us = List.length formals);
    let n = List.length formals - 1 in
    us |> List.mapi (fun i u -> UN (n - i, u))

//Instantiate the universe variables in a type scheme with provided universes
let inst_tscheme_with : tscheme -> universes -> universes & term = fun ts us ->
    match ts, us with
    | ([], t), [] -> [], t
    | (formals, t), _ ->
      let vs = mk_univ_subst formals us in
      us, Subst.subst vs t

//Instantiate the universe variables in a type scheme with new unification variables
let inst_tscheme : tscheme -> universes & term = function
    | [], t -> [], t
    | us, t ->
      let us' = us |> List.map (fun _ -> new_u_univ()) in
      inst_tscheme_with (us, t) us'

let inst_tscheme_with_range (r:range) (t:tscheme) =
    let us, t = inst_tscheme t in
    us, Subst.set_use_range r t

let check_effect_is_not_a_template (ed:eff_decl) (rng:Range.range) : unit =
  if List.length ed.univs <> 0 || List.length ed.binders <> 0
  then
    let msg = BU.format2
      "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
      (show ed.mname)
      (String.concat "," <| List.map Print.binder_to_string_with_type ed.binders) in
    raise_error rng Errors.Fatal_NotEnoughArgumentsForEffect msg

let inst_effect_fun_with (insts:universes) (env:env) (ed:eff_decl) (us, t)  =
  check_effect_is_not_a_template ed env.range;
  if List.length insts <> List.length us
  then failwith (BU.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                   (string_of_int <| List.length us) (string_of_int <| List.length insts)
                   (show ed.mname) (show t));
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
  let cache t = SMap.add (gamma_cache env) (string_of_lid lid) t; Some t in
  let found =
    if cur_mod <> No
    then match SMap.try_find (gamma_cache env) (string_of_lid lid) with
      | None ->
        (BU.find_map env.gamma (function
          | Binding_lid(l, (us_names, t)) when lid_equals lid l->
            (* A recursive definition.
              * We must return the exact set of universes on which
              * it is being defined, and not instantiate it.
              * TODO: could we cache this? *)
            let us = List.map U_name us_names in
            Some (Inl (us, t), Ident.range_of_lid l)
          | _ -> None))
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
    match SMap.try_find (attrtab env) attr with
    | Some ses -> ses
    | None -> []

let add_se_to_attrtab env se =
    let add_one env se attr = SMap.add (attrtab env) attr (se :: lookup_attr env attr) in
    List.iter (fun attr ->
                let hd, _ = U.head_and_args attr in
                match (Subst.compress hd).n with
                | Tm_fvar fv -> add_one env se (string_of_lid (lid_of_fv fv))
                | _ -> ()) se.sigattrs

(* This adds a sigelt to the sigtab in the environment but checks
that we are not clashing with something that is already defined.
The force flag overrides the check, it's convenient in the checking for
haseq in inductives. *)
let try_add_sigelt force env se l =
  let s = string_of_lid l in
  if not force && Some? (SMap.try_find (sigtab env) s) then (
    let old_se = Some?.v (SMap.try_find (sigtab env) s) in
    if Sig_declare_typ? old_se.sigel &&
        (Sig_let? se.sigel || Sig_inductive_typ? se.sigel || Sig_datacon? se.sigel)
    then
      (* overriding a val with a let, a type, or a datacon is ok *)
      ()
    else (
      (* anything else is an error *)
      let open FStarC.Errors.Msg in
      let open FStarC.Pprint in
      raise_error l Errors.Fatal_DuplicateTopLevelNames [
        text "Duplicate top-level names" ^/^ arbitrary_string s;
        text "Previously declared at" ^/^ arbitrary_string (Range.string_of_range (range_of_lid l));
        // text "New decl = " ^/^ Print.sigelt_to_doc se;
        // text "Old decl = " ^/^ Print.sigelt_to_doc old_se;
        // backtrace_doc ();
      ]
    )
  );
  SMap.add (sigtab env) s se

let rec add_sigelt force env se = match se.sigel with
    | Sig_bundle {ses} -> add_sigelts force env ses
    | _ ->
      let lids = lids_of_sigelt se in
      List.iter (try_add_sigelt force env se) lids;
      add_se_to_attrtab env se

and add_sigelts force env ses =
    ses |> List.iter (add_sigelt force env)

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
    | Sig_let {lbs=(_, [lb])} ->
      Some (inst_tscheme (lb.lbunivs, lb.lbtyp), S.range_of_lbname lb.lbname)

    | Sig_let {lbs=(_, lbs)} ->
        BU.find_map lbs (fun lb -> match lb.lbname with
          | Inl _ -> failwith "impossible"
          | Inr fv ->
            if fv_eq_lid fv lid
            then Some (inst_tscheme (lb.lbunivs, lb.lbtyp), S.range_of_fv fv)
            else None)

    | _ -> None

let effect_signature (us_opt:option universes) (se:sigelt) rng : option ((universes & typ) & Range.range) =
  let inst_ts us_opt ts =
    match us_opt with
    | None -> inst_tscheme ts
    | Some us -> inst_tscheme_with ts us
  in
  match se.sigel with
  | Sig_new_effect ne ->
    let sig_ts = U.effect_sig_ts ne.signature in
    check_effect_is_not_a_template ne rng;
    (match us_opt with
     | None -> ()
     | Some us ->
       if List.length us <> List.length (fst sig_ts)
       then failwith ("effect_signature: incorrect number of universes for the signature of " ^
         (string_of_lid ne.mname) ^ ", expected " ^ (string_of_int (List.length (fst sig_ts))) ^
         ", got " ^ (string_of_int (List.length us)))
       else ());

    Some (inst_ts us_opt sig_ts, se.sigrng)

  | Sig_effect_abbrev {lid; us; bs=binders} ->
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

    | Inr ({sigel = Sig_datacon {us=uvs; t} }, None) ->
      Some (inst_tscheme (uvs, t), rng)

    | Inr ({sigel = Sig_declare_typ {lid=l; us=uvs; t}; sigquals=qs }, None) ->
      if in_cur_mod env l = Yes
      then if qs |> List.contains Assumption || env.is_iface
           then Some (inst_tscheme (uvs, t), rng)
           else None
      else Some (inst_tscheme (uvs, t), rng)

    | Inr ({sigel = Sig_inductive_typ {lid; us=uvs; params=tps; t=k} }, None) ->
      begin match tps with
        | [] -> Some (inst_tscheme (uvs, k), rng)
        | _ ->  Some (inst_tscheme (uvs, U.flat_arrow tps (mk_Total k)), rng)
      end

    | Inr ({sigel = Sig_inductive_typ {lid; us=uvs; params=tps; t=k} }, Some us) ->
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
//        val datacons_of_typ        : env -> lident -> bool * list lident
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
    | None -> raise_error bvr Errors.Fatal_VariableNotFound
                (format1 "Variable \"%s\" not found" (show bv))
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

let name_not_found (#a:Type) (l:lid) : a =
  raise_error l Errors.Fatal_NameNotFound
    (format1 "Name \"%s\" not found" (string_of_lid l))

let lookup_lid env l =
    match try_lookup_lid env l with
    | Some v -> v
    | None -> name_not_found l

let lookup_univ env x =
    List.find (function
        | Binding_univ y -> (string_of_id x = string_of_id y)
        | _ -> false) env.gamma
    |> Option.isSome

let try_lookup_val_decl env lid =
  //QUESTION: Why does this not inst_tscheme?
  match lookup_qname env lid with
    | Some (Inr ({ sigel = Sig_declare_typ {us=uvs; t}; sigquals = q }, None), _) ->
      Some ((uvs, Subst.set_use_range (range_of_lid lid) t),q)
    | _ -> None

let lookup_val_decl env lid =
  match lookup_qname env lid with
  | Some (Inr ({ sigel = Sig_declare_typ {us=uvs; t} }, None), _) ->
    inst_tscheme_with_range (range_of_lid lid) (uvs, t)
  | _ -> name_not_found lid

let lookup_datacon env lid =
  match lookup_qname env lid with
  | Some (Inr ({ sigel = Sig_datacon {us=uvs; t} }, None), _) ->
    inst_tscheme_with_range (range_of_lid lid) (uvs, t)
  | _ -> name_not_found lid

let lookup_and_inst_datacon env us lid =
  match lookup_qname env lid with
  | Some (Inr ({ sigel = Sig_datacon {us=uvs; t} }, None), _) ->
    inst_tscheme_with (uvs, t) us |> snd
  | _ -> name_not_found lid

let datacons_of_typ env lid =
  match lookup_qname env lid with
    | Some (Inr ({ sigel = Sig_inductive_typ {ds=dcs} }, _), _) -> true, dcs
    | _ -> false, []

let typ_of_datacon env lid =
  match lookup_qname env lid with
    | Some (Inr ({ sigel = Sig_datacon {ty_lid=l} }, _), _) -> l
    | _ -> failwith (BU.format1 "Not a datacon: %s" (show lid))

let num_datacon_non_injective_ty_params env lid =
  match lookup_qname env lid with
    | Some (Inr ({ sigel = Sig_datacon {num_ty_params; injective_type_params} }, _), _) ->
      if injective_type_params then Some 0 else Some num_ty_params
    | _ -> None

let visible_with delta_levels quals =
  delta_levels |> BU.for_some (fun dl -> quals |> BU.for_some (visible_at dl))

let lookup_definition_qninfo_aux rec_ok delta_levels lid (qninfo : qninfo) =
  match qninfo with
  | Some (Inr (se, None), _) ->
    begin match se.sigel with
      | Sig_let {lbs=(is_rec, lbs)}
        when visible_with delta_levels se.sigquals
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

let rec delta_depth_of_qninfo_lid env lid (qn:qninfo) : delta_depth =
  match qn with
  | None
  | Some (Inl _, _) -> delta_constant
  | Some (Inr(se, _), _) ->
    match se.sigel with
    | Sig_inductive_typ _
    | Sig_bundle _
    | Sig_datacon _ -> delta_constant

    | Sig_declare_typ _ ->
      let d0 =
        if U.is_primop_lid lid
        then delta_equational
        else delta_constant
      in
      if se.sigquals |> BU.for_some (Assumption?)
        && not (se.sigquals |> BU.for_some (New?))
      then Delta_abstract d0
      else d0

    | Sig_let {lbs=(_,lbs)} ->
      BU.find_map lbs (fun lb ->
          let fv = right lb.lbname in
          if fv_eq_lid fv lid then
            Some (incr_delta_depth <| delta_depth_of_term env lb.lbdef)
          else None) |> must

    | Sig_fail _
    | Sig_splice  _ ->
      failwith "impossible: delta_depth_of_qninfo"

    | Sig_assume _
    | Sig_new_effect _
    | Sig_sub_effect _
    | Sig_effect_abbrev _ (* None? *)
    | Sig_pragma  _
    | Sig_polymonadic_bind _
    | Sig_polymonadic_subcomp _ ->
      delta_constant

and delta_depth_of_qninfo env (fv:fv) (qn:qninfo) : delta_depth =
  delta_depth_of_qninfo_lid env fv.fv_name.v qn

(* Computes the canonical delta_depth of a given fvar, by looking at its
definition (and recursing) if needed. Results are memoized in the env.

NB: The cache is never invalidated. A potential problem here would be
if we memoize the delta_depth of a `val` before seeing the corresponding
`let`, but I don't think that can happen. Before seeing the `let`, other code
cannot refer to the name. *)
and delta_depth_of_fv (env:env) (fv:S.fv) : delta_depth =
  let lid = fv.fv_name.v in
  (string_of_lid lid) |> SMap.try_find env.fv_delta_depths |> (function
  | Some dd -> dd
  | None ->
    SMap.add env.fv_delta_depths (string_of_lid lid) delta_equational;
    // ^ To prevent an infinite loop on recursive functions, we pre-seed the cache with
    // a delta_equational. If we run into the same function while computing its delta_depth,
    // we will return delta_equational. If not, we override the cache with the correct delta_depth.
    let d = delta_depth_of_qninfo env fv (lookup_qname env fv.fv_name.v) in
    // if Debug.any () then
    //  BU.print2_error "Memoizing delta_depth_of_fv %s ->\t%s\n" (show lid) (show d);
    SMap.add env.fv_delta_depths (string_of_lid lid) d;
    d)

(* Computes the delta_depth of an fv, but taking into account the visibility
in the current module. *)
and fv_delta_depth (env:env) (fv:S.fv) : delta_depth =
    let d = delta_depth_of_fv env fv in
    match d with
    | Delta_abstract (Delta_constant_at_level l) ->
      if string_of_lid env.curmodule = nsstr fv.fv_name.v && not env.is_iface
       //AR: TODO: this is to prevent unfolding of abstract symbols in the extracted interface
       //a better way would be create new fvs with appripriate delta_depth at extraction time
      then Delta_constant_at_level l //we're in the defining module
      else delta_constant
    | d -> d

(* Computes the delta_depth of a term. This is the single way to compute it. *)
and delta_depth_of_term env t =
    let t = U.unmeta t in
    match t.n with
    | Tm_meta _
    | Tm_delayed _  -> failwith "Impossible (delta depth of term)"
    | Tm_lazy i -> delta_depth_of_term env (U.unfold_lazy i)

    | Tm_fvar fv -> fv_delta_depth env fv

    | Tm_bvar _
    | Tm_name _
    | Tm_match _
    | Tm_uvar _
    | Tm_unknown -> delta_equational

    | Tm_type _
    | Tm_quoted _
    | Tm_constant _
    | Tm_arrow _ -> delta_constant

    | Tm_uinst(t, _)
    | Tm_refine {b={sort=t}}
    | Tm_ascribed {tm=t}
    | Tm_app {hd=t}
    | Tm_abs {body=t}
    | Tm_let {body=t} -> delta_depth_of_term env t

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

let fv_exists_and_has_attr env fv_lid attr_lid : bool & bool =
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

let cache_in_fv_tab (tab:SMap.t 'a) (fv:fv) (f:unit -> (bool & 'a)) : 'a =
  let s = string_of_lid (S.lid_of_fv fv) in
  match SMap.try_find tab s with
  | None ->
    let should_cache, res = f () in
    if should_cache then SMap.add tab s res;
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
  let f () : bool & option (list int) =
    let attrs = lookup_attrs_of_lid env (S.lid_of_fv fv) in
    match attrs with
    | None -> false, None
    | Some attrs ->
      let res =
          BU.find_map attrs (fun x ->
            fst (FStarC.ToSyntax.ToSyntax.parse_attr_with_list
                false x FStarC.Parser.Const.strict_on_arguments_attr))
      in
      true, BU.map_opt res fst
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
    | None -> name_not_found ftv
    | Some k -> k

let lookup_effect_abbrev env (univ_insts:universes) lid0 =
  match lookup_qname env lid0 with
    | Some (Inr ({ sigel = Sig_effect_abbrev {lid; us=univs; bs=binders; comp=c}; sigquals = quals }, None), _) ->
      let lid = Ident.set_lid_range lid (Range.set_use_range (Ident.range_of_lid lid) (Range.use_range (Ident.range_of_lid lid0))) in
      if quals |> BU.for_some (function Irreducible -> true | _ -> false)
      then None
      else let insts = if List.length univ_insts = List.length univs
                       then univ_insts
                       else failwith (BU.format3 "(%s) Unexpected instantiation of effect %s with %s universes"
                                            (Range.string_of_range (get_range env))
                                            (show lid)
                                            (List.length univ_insts |> BU.string_of_int)) in
           begin match binders, univs with
             | [], _ -> failwith "Unexpected effect abbreviation with no arguments"
             | _, _::_::_ ->
                failwith (BU.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes"
                           (show lid) (string_of_int <| List.length univs))
             | _ -> let _, t = inst_tscheme_with (univs, U.arrow binders c) insts in
                    let t = Subst.set_use_range (range_of_lid lid) t in
                    begin match (Subst.compress t).n with
                        | Tm_arrow {bs=binders; comp=c} ->
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
       let res = match SMap.try_find env.normalized_eff_names (string_of_lid l) with
            | Some l -> l
            | None ->
              begin match find l with
                        | None -> l
                        | Some m -> SMap.add env.normalized_eff_names (string_of_lid l) m;
                                    m
              end in
       Ident.set_lid_range res (range_of_lid l)

let is_erasable_effect env l =
  l
  |> norm_eff_name env
  |> (fun l -> lid_equals l Const.effect_GHOST_lid ||
           S.lid_as_fv l None
           |> fv_has_erasable_attr env)

let rec non_informative env t =
    match (U.unrefine t).n with
    | Tm_type _ -> true
    | Tm_fvar fv ->
      fv_eq_lid fv Const.unit_lid
      || fv_eq_lid fv Const.squash_lid
      || fv_eq_lid fv Const.erased_lid
      || fv_has_erasable_attr env fv
    | Tm_app {hd=head} -> non_informative env head
    | Tm_uinst (t, _) -> non_informative env t
    | Tm_arrow {comp=c} ->
      (is_pure_or_ghost_comp c && non_informative env (comp_result c))
      || is_erasable_effect env (comp_effect_name c)
    | _ -> false

let num_effect_indices env name r =
  let sig_t = name |> lookup_effect_lid env |> SS.compress in
  match sig_t.n with
  | Tm_arrow {bs=_a::bs} -> List.length bs
  | _ ->
    raise_error r Errors.Fatal_UnexpectedSignatureForMonad
      (BU.format2 "Signature for %s not an arrow (%s)" (show name) (show sig_t))

let lookup_effect_quals env l =
    let l = norm_eff_name env l in
    match lookup_qname env l with
    | Some (Inr ({ sigel = Sig_new_effect _; sigquals=q}, _), _) ->
      q
    | _ -> []

let lookup_projector env lid i =
    let fail () = failwith (BU.format2 "Impossible: projecting field #%s from constructor %s is undefined" (BU.string_of_int i) (show lid)) in
    let _, t = lookup_datacon env lid in
    match (compress t).n with
        | Tm_arrow {bs=binders} ->
          if ((i < 0) || i >= List.length binders) //this has to be within bounds!
          then fail ()
          else let b = List.nth binders i in
               U.mk_field_projector_name lid b.binder_bv i
        | _ -> fail ()

let is_projector env (l:lident) : bool =
    match lookup_qname env l with
        | Some (Inr ({ sigel = Sig_declare_typ _; sigquals=quals }, _), _) ->
          BU.for_some (function Projector _ -> true | _ -> false) quals
        | _ -> false

let is_datacon env lid =
  match lookup_qname env lid with
    | Some (Inr ({ sigel = Sig_datacon _ }, _), _) -> true
    | _ -> false

let is_record env lid =
  match lookup_qname env lid with
    | Some (Inr ({ sigel = Sig_inductive_typ _; sigquals=quals }, _), _) ->
        BU.for_some (function RecordType _ | RecordConstructor _ -> true | _ -> false) quals
    | _ -> false

let qninfo_is_action (qninfo : qninfo) =
    match qninfo with
        | Some (Inr ({ sigel = Sig_let _; sigquals = quals }, _), _) ->
            BU.for_some (function Action _ -> true | _ -> false) quals
        | _ -> false

let is_action env lid =
    qninfo_is_action <| lookup_qname env lid

// FIXME? Does not use environment.
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
          BU.for_some (Ident.lid_equals fv.fv_name.v) interpreted_symbols ||
            (match delta_depth_of_fv env fv with
             | Delta_equational_at_level _ -> true
             | _ -> false)
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
  | Some (Inr ({ sigel = Sig_inductive_typ {params=tps} }, _), _) ->
    Some (List.length tps)
  | _ ->
    None

let num_inductive_uniform_ty_params env lid =
  match lookup_qname env lid with
  | Some (Inr ({ sigel = Sig_inductive_typ {num_uniform_params=num_uniform} }, _), _) ->
    (
      match num_uniform with
      | None ->
        raise_error lid Errors.Fatal_UnexpectedInductivetype
          (BU.format1 "Internal error: Inductive %s is not decorated with its uniform type parameters"
                                (show lid))
      | Some n -> Some n
    )
  | _ ->
    None

////////////////////////////////////////////////////////////
// Operations on the monad lattice                        //
////////////////////////////////////////////////////////////
let effect_decl_opt env l =
  env.effects.decls |> BU.find_opt (fun (d, _) -> lid_equals d.mname l)

let get_effect_decl env l =
  match effect_decl_opt env l with
    | None -> name_not_found l
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
              | Tm_constant (FStarC.Const.Const_string (s, _)) -> s |> Ident.lid_of_str |> Some
              | _ ->
                raise_error t Errors.Fatal_UnexpectedEffect
                   (BU.format2 "The argument for the effect attribute for %s is not a constant string, it is %s\n"
                     (show eff_lid)
                     (show t)))

let get_default_effect env lid =
  get_lid_valued_effect_attr env lid Const.default_effect_attr None

let get_top_level_effect env lid =
  get_lid_valued_effect_attr env lid Const.top_level_effect_attr (Some lid)

let is_layered_effect env l =
  l |> get_effect_decl env |> U.is_layered

let identity_mlift : mlift =
  { mlift_wp=(fun _ c -> c, trivial_guard);
    mlift_term=Some (fun _ _ e -> return_all e) }

let join_opt env (l1:lident) (l2:lident) : option (lident & mlift & mlift) =
  if lid_equals l1 l2
  then Some (l1, identity_mlift, identity_mlift)
  else if lid_equals l1 Const.effect_GTot_lid && lid_equals l2 Const.effect_Tot_lid
       || lid_equals l2 Const.effect_GTot_lid && lid_equals l1 Const.effect_Tot_lid
  then Some (Const.effect_GTot_lid, identity_mlift, identity_mlift)
  else match env.effects.joins |> BU.find_opt (fun (m1, m2, _, _, _) -> lid_equals l1 m1 && lid_equals l2 m2) with
        | None -> None
        | Some (_, _, m3, j1, j2) -> Some (m3, j1, j2)

let join env l1 l2 : (lident & mlift & mlift) =
  match join_opt env l1 l2 with
  | None ->
    raise_error env Errors.Fatal_EffectsCannotBeComposed
      (BU.format2 "Effects %s and %s cannot be composed" (show l1) (show l2))
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
    let _, s = md.signature |> U.effect_sig_ts |> inst_tscheme in
    let s = Subst.compress s in
    match md.binders, s.n with
      | [], Tm_arrow {bs=[b; wp_b]; comp=c} when (is_teff (comp_result c)) -> b.binder_bv, wp_b.binder_bv.sort
      | _ -> failwith "Impossible"

let wp_signature env m = wp_sig_aux env.effects.decls m

let bound_vars_of_bindings bs =
  bs |> List.collect (function
        | Binding_var x -> [x]
        | Binding_lid _
        | Binding_univ _ -> [])

let binders_of_bindings bs = bound_vars_of_bindings bs |> List.map Syntax.mk_binder |> List.rev
let all_binders env = binders_of_bindings env.gamma
let bound_vars env = bound_vars_of_bindings env.gamma

instance hasBinders_env : hasBinders env = {
  boundNames = (fun e -> FlatSet.from_list (bound_vars e) );
}

instance hasNames_lcomp : hasNames lcomp = {
  freeNames = (fun lc -> freeNames (fst (lcomp_comp lc)));
}

instance pretty_lcomp : pretty lcomp = {
  pp = (fun lc -> let open FStarC.Pprint in empty);
}

instance hasNames_guard : hasNames guard_t = {
  freeNames = (fun g -> match g.guard_f with
                        | Trivial -> FlatSet.empty ()
                        | NonTrivial f -> freeNames f);
}

instance pretty_guard : pretty guard_t = {
  pp = (fun g -> let open FStarC.Pprint in
                 match g.guard_f with
                 | Trivial -> doc_of_string "Trivial"
                 | NonTrivial f -> doc_of_string "NonTrivial" ^/^ pp f);
}

let comp_to_comp_typ (env:env) c =
  def_check_scoped c.pos "comp_to_comp_typ" env c;
  match c.n with
  | Comp ct -> ct
  | _ ->
    let effect_name, result_typ =
      match c.n with
      | Total t -> Const.effect_Tot_lid, t
      | GTotal t -> Const.effect_GTot_lid, t in
    {comp_univs = [env.universe_of env result_typ];
     effect_name;
     result_typ;
     effect_args = [];
     flags = U.comp_flags c}

let comp_set_flags env c f =
    def_check_scoped c.pos "comp_set_flags.IN" env c;
    let r = {c with n=Comp ({comp_to_comp_typ env c with flags=f})} in
    def_check_scoped c.pos "comp_set_flags.OUT" env r;
    r

let rec unfold_effect_abbrev env comp =
  def_check_scoped comp.pos "unfold_effect_abbrev" env comp;
  let c = comp_to_comp_typ env comp in
  match lookup_effect_abbrev env c.comp_univs c.effect_name with
    | None -> c
    | Some (binders, cdef) ->
      let binders, cdef = Subst.open_comp binders cdef in
      if List.length binders <> List.length c.effect_args + 1 then
        raise_error comp Errors.Fatal_ConstructorArgLengthMismatch
          (BU.format3 "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         (show (List.length binders)) (show (List.length c.effect_args + 1))
                         (show (S.mk_Comp c)));
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
      raise_error r Errors.Fatal_NotEnoughArgumentsForEffect message
  in

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
      Some (S.mk (Tm_app {hd=repr; args=((res_typ |> S.as_arg)::c.effect_args)}) (get_range env))

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
    | Tm_arrow {comp=c} -> is_reifiable_comp env c
    | _ -> false

let reify_comp env c u_c : term =
    let l = U.comp_effect_name c in
    if not (is_reifiable_effect env l) then
      raise_error env Errors.Fatal_EffectCannotBeReified
        (BU.format1 "Effect %s cannot be reified" (Ident.string_of_lid l));
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

let rec record_vals_and_defns (g:env) (se:sigelt) : env =
  match se.sigel with
  | Sig_declare_typ _
  | Sig_let _
      when se.sigquals |> BU.for_some (function OnlyName -> true | _ -> false) ->
      g
  | Sig_declare_typ {lid} ->
    if se.sigquals |> List.contains Assumption || g.is_iface
    then g
    else record_val_for g lid
  | Sig_let {lids} ->
    List.fold_left record_definition_for g lids
  | Sig_datacon {lid} ->
    record_definition_for g lid
  | Sig_inductive_typ {lid} ->
    record_definition_for g lid
  | Sig_bundle {ses} ->
    List.fold_left record_vals_and_defns g ses
  | _ -> g

// This function assumes that, in the case that the environment contains local
// bindings _and_ we push a top-level binding, then the top-level binding does
// not capture any of the local bindings (duh).
let push_sigelt' (force:bool) env s =
  let sb = (lids_of_sigelt s, s) in
  let env = {env with gamma_sig = sb::env.gamma_sig} in
  add_sigelt force env s;
  env.tc_hooks.tc_push_in_gamma_hook env (Inr sb);
  let env = record_vals_and_defns env s in
  env

let push_sigelt = push_sigelt' false
let push_sigelt_force = push_sigelt' true

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
        |> BU.find_opt (fun (m1, n1, _, _) -> lid_equals m m1 && lid_equals n n1) with
  | Some (_, _, ts, k) -> Some (ts, k)
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

  env.effects.polymonadic_subcomps |> List.iter (fun (m, n, _, _) ->
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
	  |> (fun (c, g1) -> c |> e2.mlift.mlift_wp env
                           |> (fun (c, g2) -> c, TcComm.conj_guard g1 g2)) in
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
    then raise_error env Errors.Fatal_Effects_Ordering_Coherence
           (BU.format3 "Adding an edge %s~>%s induces a cycle %s"
             (show edge.msource) (show edge.mtarget) (show src))
  in

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
    then
      raise_error env Errors.Fatal_DivergentComputationCannotBeIncludedInTotal
        (BU.format1 "Divergent computations cannot be included in an effect %s marked 'total'"
                        (show edge.mtarget)));

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
    let ubs : smap (list (lident & lident & lident & mlift & mlift)) =
      SMap.create 10 in
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
      then
        raise_error env Errors.Fatal_Effects_Ordering_Coherence
          (BU.format1 "Effects %s have incomparable upper bounds" s)
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

let add_polymonadic_subcomp env m n (ts, k) =
  { env with
    effects = ({ env.effects with
                 polymonadic_subcomps = (m, n, ts, k)::env.effects.polymonadic_subcomps }) }

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

let clear_expected_typ (env_: env): env & option (typ & bool) =
    {env_ with expected_typ=None}, expected_typ env_

let finish_module =
    let empty_lid = lid_of_ids [id_of_text ""] in
    fun env m ->
      {env with
        curmodule=empty_lid;
        gamma=[];
        gamma_sig=[];
        modules=m::env.modules}

////////////////////////////////////////////////////////////
// Collections from the environment                       //
////////////////////////////////////////////////////////////
let uvars_in_env env =
  let no_uvs = empty () in
  let rec aux out g = match g with
    | [] -> out
    | Binding_univ _ :: tl -> aux out tl
    | Binding_lid(_, (_, t))::tl
    | Binding_var({sort=t})::tl -> aux (union out (Free.uvars t)) tl
  in
  aux no_uvs env.gamma

let univ_vars env =
    let no_univs = empty () in
    let rec aux out g = match g with
      | [] -> out
      | Binding_univ _ :: tl -> aux out tl
      | Binding_lid(_, (_, t))::tl
      | Binding_var({sort=t})::tl -> aux (union out (Free.univs t)) tl
    in
    aux no_univs env.gamma

let univnames env =
    let no_univ_names = empty () in
    let rec aux out g = match g with
        | [] -> out
        | Binding_univ uname :: tl -> aux (add uname out) tl
        | Binding_lid(_, (_, t))::tl
        | Binding_var({sort=t})::tl -> aux (union out (Free.univnames t)) tl
    in
    aux no_univ_names env.gamma

let lidents env : list lident =
  let keys = List.collect fst env.gamma_sig in
  SMap.fold (sigtab env) (fun _ v keys -> U.lids_of_sigelt v@keys) keys

let should_enc_path proof_ns path =
    let rec str_i_prefix xs ys =
        match xs, ys with
        | [], _ -> true
        | x::xs, y::ys -> String.lowercase x = String.lowercase y && str_i_prefix xs ys
        | _, _ -> false
    in
    match FStarC.List.tryFind (fun (p, _) -> str_i_prefix p path) proof_ns with
    | None -> false
    | Some (_, b) -> b

let should_enc_lid proof_ns lid =
    should_enc_path proof_ns (path_of_lid lid)

let cons_proof_ns b e path =
    { e with proof_ns = (path,b) :: e.proof_ns }

// F# forces me to fully apply this... ugh
let add_proof_ns e path = cons_proof_ns true  e path
let rem_proof_ns e path = cons_proof_ns false e path
let get_proof_ns e = e.proof_ns
let set_proof_ns ns e = {e with proof_ns = ns}

let unbound_vars (e : env) (t : term) : FlatSet.t bv =
    // FV(t) \ Vars(Γ)
    List.fold_left (fun s bv -> remove bv s) (Free.names t) (bound_vars e)

let closed (e : env) (t : term) =
    is_empty (unbound_vars e t)

let closed' (t : term) =
    is_empty (Free.names t)

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
let guard_of_guard_formula g =
  let open FStarC.Class.Listlike in
  {
    guard_f=g;
    deferred=empty;
    deferred_to_tac=empty;
    univ_ineqs=(empty, empty);
    implicits=empty;
  }

let guard_form g = g.guard_f

let is_trivial g =
  let open FStarC.Class.Listlike in
  (* This is cumbersome due to not having view patterns. *)
  // match g with
  // | {guard_f=Trivial; deferred=[]; univ_ineqs=([], []); implicits=i} ->
  if
    Trivial? g.guard_f &&
    is_empty g.deferred &&
    is_empty (fst g.univ_ineqs) &&
    is_empty (snd g.univ_ineqs)
  then
    g.implicits |> CList.for_all (fun imp ->
         (Allow_unresolved? (U.ctx_uvar_should_check imp.imp_uvar))
         || (match Unionfind.find imp.imp_uvar.ctx_uvar_head with
             | Some _ -> true
             | None -> false))
  else
    false

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

let too_early_in_prims env =
  not (lid_exists env Const.effect_GTot_lid)

let apply_guard g e = match g.guard_f with
  | Trivial -> g
  | NonTrivial f -> {g with guard_f=NonTrivial <| mk (Tm_app {hd=f; args=[as_arg e]}) f.pos}

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

let close_forall (env:env) (bs:binders) (f:formula) : formula =
  Errors.with_ctx "While closing a formula" (fun () ->
    def_check_scoped f.pos "close_forall" env (U.arrow bs (S.mk_Total f));
    let bvs = List.map (fun b -> b.binder_bv) bs in
    (* We start with env_full and pop bvs one-by-one. This way each
     * bv sort is always well scoped in the call to universe_of below. *)
    let env_full = push_bvs env bvs in

    let (f', e) =
      List.fold_right (fun bv (f, e) ->
        let e' = pop_bv e |> must |> snd in
        def_check_scoped Range.dummyRange "close_forall.sort" e' bv.sort;
        let f' =
              if Syntax.is_null_bv bv then f
              else let u = e'.universe_of e' bv.sort in
                   U.mk_forall u bv f
        in
        (f', e')
      ) bvs (f, env_full)
    in
    f'
  )

let close_guard env binders g =
    match g.guard_f with
    | Trivial -> g
    | NonTrivial f ->
      {g with guard_f=NonTrivial (close_forall env binders f)}

(* ------------------------------------------------*)
(* </guard_formula ops>                            *)
(* ------------------------------------------------*)

(* Generating new implicit variables *)
let new_tac_implicit_var
  (reason: string)
  (r: Range.range)
  (env:env)
  (uvar_typ:typ)
  (should_check:should_check_uvar)
  (uvar_typedness_deps:list ctx_uvar)
  (meta:option ctx_uvar_meta_t)
  (unrefine:bool)
: term & (ctx_uvar & Range.range) & guard_t
=
  let binders = all_binders env in
  let gamma = env.gamma in
  let decoration = {
         uvar_decoration_typ = uvar_typ;
         uvar_decoration_typedness_depends_on = uvar_typedness_deps;
         uvar_decoration_should_check = should_check;
         uvar_decoration_should_unrefine = unrefine;
  } in
  let ctx_uvar = {
      ctx_uvar_head=FStarC.Syntax.Unionfind.fresh decoration r;
      ctx_uvar_gamma=gamma;
      ctx_uvar_binders=binders;
      ctx_uvar_reason=reason;
      ctx_uvar_range=r;
      ctx_uvar_meta=meta;
  } in
  check_uvar_ctx_invariant reason r true gamma binders;
  let t = mk (Tm_uvar (ctx_uvar, ([], NoUseRange))) r in
  let imp = { imp_reason = reason
            ; imp_tm     = t
            ; imp_uvar   = ctx_uvar
            ; imp_range  = r
            } in
  if !dbg_ImplicitTrace then
    BU.print1 "Just created uvar for implicit {%s}\n" (show ctx_uvar.ctx_uvar_head);
  let g = {trivial_guard with implicits = Listlike.cons imp Listlike.empty} in
  t, (ctx_uvar, r), g

let new_implicit_var_aux reason r env k should_check meta unrefine =
  new_tac_implicit_var reason r env k should_check [] meta unrefine

(***************************************************)

let uvar_meta_for_binder (b:binder) : option ctx_uvar_meta_t & bool=
  let should_unrefine = U.has_attribute b.binder_attrs Const.unrefine_binder_attr in
  let meta =
    match b.binder_qual with
    | Some (Meta tau) ->
      (* Meta qualifier (e.g typeclass constraints) *)
      Some (Ctx_uvar_meta_tac tau)
    | _ ->
      (* NB: it does not have to be marked Implicit to get a
      Ctx_uvar_meta_attr. In practice most of them are (or
      the typechecker will not decide to instantiate) but the
      layered effects checking code will sometimes call this
      function on regular explicit binders. *)
      let is_unification_tag (t:term) : option term =
        let hd, args = U.head_and_args t in
        let hd = U.un_uinst hd in
        match (SS.compress hd).n, args with
        | Tm_fvar fv, [(_, Some ({aqual_implicit = true})); (a, None)]
          when S.fv_eq_lid fv Const.unification_tag_lid ->
          Some a
        | _ -> None
      in
      match b.binder_attrs |> List.tryPick is_unification_tag with
      | Some tag -> Some (Ctx_uvar_meta_attr tag)
      | None -> None
  in
  meta, should_unrefine
//
// Perhaps this should not return a guard,
//   but only a list of implicits, so that callers don't have to
//   be cautious about the logical payload of the guard
//
let uvars_for_binders env (bs:S.binders) substs reason r =
  bs |> List.fold_left (fun (substs, uvars, g) b ->
    let sort = SS.subst substs b.binder_bv.sort in

    let ctx_uvar_meta, should_unrefine = uvar_meta_for_binder b in

    let t, l_ctx_uvars, g_t = new_implicit_var_aux
      (reason b) r env sort
      (if Options.compat_pre_typed_indexed_effects ()
       then Allow_untyped "indexed effect uvar in compat mode"
       else Strict)
      ctx_uvar_meta
      should_unrefine
    in

    if !dbg_LayeredEffectsEqns then
      BU.print1 "Layered Effect uvar: %s\n" (show l_ctx_uvars);

    substs@[NT (b.binder_bv, t)],
    uvars@[t],
    conj_guards [g; g_t]
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
    fvar lid None

let split_smt_query (e:env) (q:term) 
  : option (list (env & term))
  = match e.solver.spinoff_strictly_positive_goals with
    | None -> None
    | Some p -> Some (p e q)
