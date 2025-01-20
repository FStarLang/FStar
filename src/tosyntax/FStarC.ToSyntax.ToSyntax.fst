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
module FStarC.ToSyntax.ToSyntax
open FStar.Pervasives
open FStarC.Effect
open FStarC.List
open FStar open FStarC
open FStarC
open FStarC.Util
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Syntax.Util
open FStarC.Parser
open FStarC.Syntax.DsEnv
open FStarC.Parser.AST
open FStarC.Ident
open FStarC.Const
open FStarC.Errors
open FStarC.Syntax
open FStarC.Class.Setlike
open FStarC.Class.Show

module C = FStarC.Parser.Const
module S = FStarC.Syntax.Syntax
module U = FStarC.Syntax.Util
module BU = FStarC.Util
module Env = FStarC.Syntax.DsEnv
module P = FStarC.Syntax.Print
module EMB = FStarC.Syntax.Embeddings
module SS = FStarC.Syntax.Subst

let extension_tosyntax_table 
: BU.smap extension_tosyntax_decl_t
= FStarC.Util.smap_create 20

let register_extension_tosyntax
    (lang_name:string)
    (cb:extension_tosyntax_decl_t)
= FStarC.Util.smap_add extension_tosyntax_table lang_name cb

let lookup_extension_tosyntax
    (lang_name:string)
= FStarC.Util.smap_try_find extension_tosyntax_table lang_name

let dbg_attrs    = Debug.get_toggle "attrs"
let dbg_ToSyntax = Debug.get_toggle "ToSyntax"

type antiquotations_temp = list (bv & S.term)

let tun_r (r:Range.range) : S.term = { tun with pos = r }

type annotated_pat = Syntax.pat & list (bv & Syntax.typ & list S.term)

let mk_thunk e =
  let b = S.mk_binder (S.new_bv None S.tun) in
  U.abs [b] e None

let mk_binder_with_attrs bv aq attrs = 
  let pqual, attrs = U.parse_positivity_attributes attrs in
  S.mk_binder_with_attrs bv aq pqual attrs

(*
   If the user wrote { f1=v1; ...; fn=vn }, where `field_names` [f1;..;fn]
   then we resolve this, using scoping rules only, to `record`.

   The choice of `record` is not settled, however, since type information
   later can be used to resolve any ambiguity.

   However, if any of the field_names, f1...fn, are qualified field names,
   like `A.B.f`, then, at this stage, we

   1. Check that all the field names, if qualified, are qualified in
      the same way. I.e., it's ok to write

       { A.f1 = v1; f2 = v2; ... }

      But not

       { A.f1 = v1; B.f2 = v2; ... }

      even if A and B are module aliases.

   2. If any of the field names are qualified, then qualify all the
      field_names to the module in which `record` is defined, since
      that's the user-provided qualifier already determines that.

      This is important because at this stage, A, B etc. can refer to
      module aliases, included modules, etc. and as we pass the term
      to the typechecker, all those module aliases have to be fully
      resolved.
*)
let qualify_field_names record_or_dc_lid field_names =
    let qualify_to_record l =
        let ns = ns_of_lid record_or_dc_lid in
        Ident.lid_of_ns_and_id ns (ident_of_lid l)
    in
    let _, field_names_rev =
      List.fold_left
        (fun (ns_opt, out) l ->
          match nsstr l with
          | "" ->
            if Option.isSome ns_opt
            then (ns_opt, qualify_to_record l::out)
            else (ns_opt, l::out)

          | ns ->
            match ns_opt with
            | Some ns' ->
              if ns <> ns'
              then raise_error l Errors.Fatal_MissingFieldInRecord
                     (BU.format2 "Field %s of record type was expected to be scoped to namespace %s" (show l) ns')
              else (
                ns_opt, qualify_to_record l :: out
              )

            | None ->
              Some ns, qualify_to_record l :: out)
        (None, [])
        field_names
    in
    List.rev field_names_rev

let desugar_disjunctive_pattern annotated_pats when_opt branch =
    annotated_pats |> List.map (fun (pat, annots) ->
        let branch = List.fold_left (fun br (bv, ty, _) ->
                        let lb = U.mk_letbinding (Inl bv) [] ty C.effect_Tot_lid (S.bv_to_name bv) [] br.pos in
                        let branch = SS.close [S.mk_binder bv] branch in
                        mk (Tm_let {lbs=(false, [lb]); body=branch}) br.pos) branch annots in
        U.branch(pat, when_opt, branch)
    )

let trans_qual (r:Range.range) maybe_effect_id = function
  | AST.Private ->       S.Private
  | AST.Assumption ->    S.Assumption
  | AST.Unfold_for_unification_and_vcgen -> S.Unfold_for_unification_and_vcgen
  | AST.Inline_for_extraction -> S.Inline_for_extraction
  | AST.NoExtract ->     S.NoExtract
  | AST.Irreducible ->   S.Irreducible
  | AST.Logic ->         S.Logic
  | AST.TotalEffect ->   S.TotalEffect
  | AST.Effect_qual ->   S.Effect
  | AST.New  ->          S.New
  | AST.Opaque ->
    Errors.log_issue r Errors.Warning_DeprecatedOpaqueQualifier [
      text "The 'opaque' qualifier is deprecated since its use was strangely schizophrenic.";
      text "There were two overloaded uses: (1) Given 'opaque val f : t', the behavior was to exclude the definition of 'f' to the SMT solver. This corresponds roughly to the new 'irreducible' qualifier. (2) Given 'opaque type t = t'', the behavior was to provide the definition of 't' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of 'unfoldable' (which is currently the default)."
    ];
    S.Visible_default
  | AST.Reflectable ->
    begin match maybe_effect_id with
    | None -> raise_error r Errors.Fatal_ReflectOnlySupportedOnEffects "Qualifier reflect only supported on effects"
    | Some effect_id ->  S.Reflectable effect_id
    end
  | AST.Reifiable ->     S.Reifiable
  | AST.Noeq ->          S.Noeq
  | AST.Unopteq ->       S.Unopteq
  | AST.DefaultEffect -> raise_error r Errors.Fatal_DefaultQualifierNotAllowedOnEffects "The 'default' qualifier on effects is no longer supported"
  | AST.Inline
  | AST.Visible ->
    raise_error r Errors.Fatal_UnsupportedQualifier "Unsupported qualifier"

let trans_pragma = function
  | AST.ShowOptions -> S.ShowOptions
  | AST.SetOptions s -> S.SetOptions s
  | AST.ResetOptions sopt -> S.ResetOptions sopt
  | AST.PushOptions sopt -> S.PushOptions sopt
  | AST.PopOptions -> S.PopOptions
  | AST.RestartSolver -> S.RestartSolver
  | AST.PrintEffectsGraph -> S.PrintEffectsGraph

let as_imp = function
    | Hash -> S.as_aqual_implicit true
    | _ -> None
let arg_withimp_t imp t =
    t, as_imp imp

let contains_binder binders =
  binders |> BU.for_some (fun b -> match b.b with
    | Annotated _ -> true
    | _ -> false)

let rec unparen t = match t.tm with
  | Paren t -> unparen t
  | _ -> t

let tm_type_z r = mk_term (Name (lid_of_path ["Type0"] r)) r Kind
let tm_type r = mk_term (Name (lid_of_path   [ "Type"] r)) r Kind

//Deciding if the t is a computation type
//based on its head symbol
let rec is_comp_type env t =
    match (unparen t).tm with
    (* we're right at the beginning of Prims, when (G)Tot isn't yet fully defined *)
    | Name l when lid_equals (Env.current_module env) C.prims_lid &&
                  (let s = string_of_id (ident_of_lid l) in
                   s = "Tot" || s = "GTot") ->
      true

    | Name l
    | Construct(l, _) -> Env.try_lookup_effect_name env l |> Option.isSome
    | App(head, _, _) -> is_comp_type env head
    | Paren t -> failwith "impossible"
    | Ascribed(t, _, _, _)
    | LetOpen(_, t) -> is_comp_type env t
    | _ -> false

let unit_ty rng = mk_term (Name C.unit_lid) rng Type_level

type env_t = Env.env
type lenv_t = list bv

let desugar_name' setpos (env: env_t) (resolve: bool) (l: lid) : option S.term =
    let tm_attrs_opt =
        if resolve
        then Env.try_lookup_lid_with_attributes env l
        else Env.try_lookup_lid_with_attributes_no_resolve env l
    in
    match tm_attrs_opt with
    | None -> None
    | Some (tm, attrs) ->
        let tm = setpos tm in
        Some tm

let desugar_name mk setpos env resolve l =
    fail_or env (desugar_name' setpos env resolve) l

let compile_op_lid n s r = [mk_ident(compile_op n s r, r)] |> lid_of_ids

let op_as_term env arity op : option S.term =
  let r l = Some (S.lid_and_dd_as_fv (set_lid_range l (range_of_id op)) None |> S.fv_to_tm) in
  let fallback () =
    match Ident.string_of_id op with
    | "=" -> r C.op_Eq
    | "<" -> r C.op_LT
    | "<=" -> r C.op_LTE
    | ">" -> r C.op_GT
    | ">=" -> r C.op_GTE
    | "&&" -> r C.op_And
    | "||" -> r C.op_Or
    | "+" -> r C.op_Addition
    | "-" when (arity=1) -> r C.op_Minus
    | "-" -> r C.op_Subtraction
    | "/" -> r C.op_Division
    | "%" -> r C.op_Modulus
    | "@" ->
      FStarC.Errors.log_issue op FStarC.Errors.Warning_DeprecatedGeneric [
          Errors.Msg.text "The operator '@' has been resolved to FStar.List.Tot.append even though \
                           FStar.List.Tot is not in scope. Please add an 'open FStar.List.Tot' to \
                           stop relying on this deprecated, special treatment of '@'."];
      r C.list_tot_append_lid

    | "<>" -> r C.op_notEq
    | "~"   -> r C.not_lid
    | "=="  -> r C.eq2_lid
    | "<<" -> r C.precedes_lid
    | "/\\" -> r C.and_lid
    | "\\/" -> r C.or_lid
    | "==>" -> r C.imp_lid
    | "<==>" -> r C.iff_lid
    | _ -> None
  in
  match desugar_name' (fun t -> {t with pos=(range_of_id op)})
        env true (compile_op_lid arity (string_of_id op) (range_of_id op)) with
  | Some t -> Some t
  | _ -> fallback()

let sort_ftv ftv =
  BU.sort_with (fun x y -> String.compare (string_of_id x) (string_of_id y)) <|
      BU.remove_dups (fun x y -> (string_of_id x) = (string_of_id y)) ftv

let rec free_vars_b tvars_only env binder : (Env.env & list ident) =
  match binder.b with
  | Variable x ->
    if tvars_only
    then env, [] //tvars can't clash with vars
    else (
      let env, _ = Env.push_bv env x in
      env, []
    )
  | TVariable x ->
    let env, _ = Env.push_bv env x in
    env, [x]
  | Annotated(x, term) ->
    if tvars_only  //tvars can't clash with vars
    then env, free_vars tvars_only env term
    else (
      let env', _ = Env.push_bv env x in
      env', free_vars tvars_only env term
    )
  | TAnnotated(id, term) ->
    let env', _ = Env.push_bv env id in
    env', free_vars tvars_only env term
  | NoName t ->
    env, free_vars tvars_only env t

and free_vars_bs tvars_only env binders =
    List.fold_left
      (fun (env, free) binder ->
        let env, f = free_vars_b tvars_only env binder in
        env, f@free)
      (env, [])
      binders

and free_vars tvars_only env t = match (unparen t).tm with
  | Labeled _ -> failwith "Impossible --- labeled source term"

  | Tvar a ->
    (match Env.try_lookup_id env a with
      | None -> [a]
      | _ -> [])

  | Var x ->
    if tvars_only 
    then []
    else (
      let ids = Ident.ids_of_lid x in
      match ids with
      | [id] -> ( //unqualified name
        if None? (Env.try_lookup_id env id)
        && None? (Env.try_lookup_lid env x)
        then [id]
        else []
      )
      | _ -> []
    )
    
  | Wild
  | Const _
  | Uvar _

  | Projector _
  | Discrim _
  | Name _  -> []

  | Requires (t, _)
  | Ensures (t, _)
  | Decreases (t, _)
  | NamedTyp(_, t) -> free_vars tvars_only env t

  | LexList l -> List.collect (free_vars tvars_only env) l
  | WFOrder (rel, e) ->
    (free_vars tvars_only env rel) @ (free_vars tvars_only env e)

  | Paren t -> failwith "impossible"

  | Ascribed(t, t', tacopt, _) ->
    let ts = t::t'::(match tacopt with None -> [] | Some t -> [t]) in
    List.collect (free_vars tvars_only env) ts

  | Construct(_, ts) -> List.collect (fun (t, _) -> free_vars tvars_only env t) ts

  | Op(_, ts) -> List.collect (free_vars tvars_only env) ts

  | App(t1,t2,_) -> free_vars tvars_only env t1@free_vars tvars_only env t2

  | Refine (b, t) ->
    let env, f = free_vars_b tvars_only env b in
    f@free_vars tvars_only env t

  | Sum(binders, body) ->
    let env, free = List.fold_left (fun (env, free) bt ->
      let env, f =
        match bt with
        | Inl binder -> free_vars_b tvars_only env binder
        | Inr t -> env, free_vars tvars_only env t
      in
      env, f@free) (env, []) binders in
    free@free_vars tvars_only env body

  | Product(binders, body) ->
    let env, free = free_vars_bs tvars_only env binders in
    free@free_vars tvars_only env body

  | Project(t, _) -> free_vars tvars_only env t

  | Attributes cattributes ->
      (* attributes should be closed but better safe than sorry *)
      List.collect (free_vars tvars_only env) cattributes

  | CalcProof (rel, init, steps) ->
    free_vars tvars_only env rel
    @ free_vars tvars_only env init
    @ List.collect (fun (CalcStep (rel, just, next)) ->
                            free_vars tvars_only env rel
                            @ free_vars tvars_only env just
                            @ free_vars tvars_only env next) steps

  | ElimForall  (bs, t, ts) ->
    let env', free = free_vars_bs tvars_only env bs in
    free@
    free_vars tvars_only env' t@
    List.collect (free_vars tvars_only env') ts

  | ElimExists (binders, p, q, y, e) ->
    let env', free = free_vars_bs tvars_only env binders in
    let env'', free' = free_vars_b tvars_only env' y in
    free@
    free_vars tvars_only env' p@
    free_vars tvars_only env  q@
    free'@
    free_vars tvars_only env'' e

  | ElimImplies (p, q, e) ->
    free_vars tvars_only env p@
    free_vars tvars_only env q@
    free_vars tvars_only env e

  | ElimOr(p, q, r, x, e, x', e') ->
    free_vars tvars_only env p@
    free_vars tvars_only env q@
    free_vars tvars_only env r@
    (let env', free = free_vars_b tvars_only env x in
     free@free_vars tvars_only env' e)@
    (let env', free = free_vars_b tvars_only env x' in
     free@free_vars tvars_only env' e')

  | ElimAnd(p, q, r, x, y, e) ->
    free_vars tvars_only env p@
    free_vars tvars_only env q@
    free_vars tvars_only env r@
    (let env', free = free_vars_bs tvars_only env [x;y] in
     free@free_vars tvars_only env' e)

  | ListLiteral ts ->
    List.collect (free_vars tvars_only env) ts

  | SeqLiteral ts ->
    List.collect (free_vars tvars_only env) ts

  | Abs _  (* not closing implicitly over free vars in all these forms: TODO: Fixme! *)
  | Function _
  | Let _
  | LetOpen _
  | If _
  | QForall _
  | QExists _
  | QuantOp _
  | Record _
  | Match _
  | TryWith _
  | Bind _
  | Quote _
  | VQuote _
  | Antiquote _
  | Seq _ -> []

let free_type_vars = free_vars true

let head_and_args t =
    let rec aux args t = match (unparen t).tm with
        | App(t, arg, imp) -> aux ((arg,imp)::args) t
        | Construct(l, args') -> {tm=Name l; range=t.range; level=t.level}, args'@args
        | _ -> t, args in
    aux [] t

let close env t =
  let ftv = sort_ftv <| free_type_vars env t in
  if List.length ftv = 0
  then t
  else let binders = ftv |> List.map (fun x -> mk_binder (TAnnotated(x, tm_type (range_of_id x))) (range_of_id x) Type_level (Some Implicit)) in
       let result = mk_term (Product(binders, t)) t.range t.level in
       result

let close_fun env t =
  let ftv = sort_ftv <| free_type_vars env t in
  if List.length ftv = 0
  then t
  else let binders = ftv |> List.map (fun x -> mk_binder (TAnnotated(x, tm_type (range_of_id x))) (range_of_id x) Type_level (Some Implicit)) in
       let t = match (unparen t).tm with
        | Product _ -> t
        | _ -> mk_term (App(mk_term (Name C.effect_Tot_lid) t.range t.level, t, Nothing)) t.range t.level in
       let result = mk_term (Product(binders, t)) t.range t.level in
       result

let rec uncurry bs t = match t.tm with
    | Product(binders, t) -> uncurry (bs@binders) t
    | _ -> bs, t

let rec is_var_pattern p = match p.pat with
  | PatWild _
  | PatTvar _
  | PatVar _ -> true
  | PatAscribed(p, _) -> is_var_pattern p
  | _ -> false

let rec is_app_pattern p = match p.pat with
  | PatAscribed(p,_) -> is_app_pattern p
  | PatApp({pat=PatVar _}, _) -> true
  | _ -> false

let replace_unit_pattern p = match p.pat with
  | PatConst FStarC.Const.Const_unit ->
    mk_pattern (PatAscribed (mk_pattern (PatWild (None, [])) p.prange, (unit_ty p.prange, None))) p.prange
  | _ -> p

let rec destruct_app_pattern (env:env_t) (is_top_level:bool) (p:pattern)
  : either ident lid              // name at the head
  & list pattern                  // arguments the head is applied to
  & option (term & option term)  // a possible (outermost) ascription on the pattern
  =
  match p.pat with
  | PatAscribed(p,t) ->
    let (name, args, _) = destruct_app_pattern env is_top_level p in
    (name, args, Some t)
  | PatApp({pat=PatVar (id, _, _)}, args) when is_top_level ->
    (Inr (qualify env id), args, None)
  | PatApp({pat=PatVar (id, _, _)}, args) ->
    (Inl id, args, None)
  | _ ->
    failwith "Not an app pattern"

let rec gather_pattern_bound_vars_maybe_top (acc : FlatSet.t ident) p =
  let gather_pattern_bound_vars_from_list =
      List.fold_left gather_pattern_bound_vars_maybe_top acc
  in
  match p.pat with
  | PatWild _
  | PatConst _
  | PatVQuote _
  | PatName _
  | PatOp _ -> acc
  | PatApp (phead, pats) -> gather_pattern_bound_vars_from_list (phead::pats)
  | PatTvar (x, _, _)
  | PatVar (x, _, _) -> add x acc
  | PatList pats
  | PatTuple  (pats, _)
  | PatOr pats -> gather_pattern_bound_vars_from_list pats
  | PatRecord guarded_pats -> gather_pattern_bound_vars_from_list (List.map snd guarded_pats)
  | PatAscribed (pat, _) -> gather_pattern_bound_vars_maybe_top acc pat

let gather_pattern_bound_vars : pattern -> FlatSet.t Ident.ident =
  let acc = empty #ident () in
  fun p -> gather_pattern_bound_vars_maybe_top acc p

type bnd =
  | LocalBinder of bv     & S.bqual & list S.term  //binder attributes
  | LetBinder   of lident & (S.term & option S.term)

let is_implicit (b:bnd) : bool =
  match b with
  | LocalBinder (_, Some (S.Implicit _), _) -> true
  | _ -> false

let binder_of_bnd = function
  | LocalBinder (a, aq, attrs) -> a, aq, attrs
  | _ -> failwith "Impossible"

(* TODO : shouldn't this be Tot by default ? *)
let mk_lb (attrs, n, t, e, pos) = {
    lbname=n;
    lbunivs=[];
    lbeff=C.effect_ALL_lid ();
    lbtyp=t;
    lbdef=e;
    lbattrs=attrs;
    lbpos=pos;
}
let no_annot_abs bs t = U.abs bs t None

(*
 * Collect the explicitly annotated universes in the sigelt, close the sigelt with them, and stash them appropriately in the sigelt
 *)
let rec generalize_annotated_univs (s:sigelt) :sigelt =
  (* NB!! Order is very important here, so a definition like
      type t = Type u#a -> Type u#b
    gets is two universe parameters in the order in which
    they appear. So we do not use a set, and instead just use a mutable
    list that we update as we find universes. We also keep a set of 'seen'
    universes, whose order we do not care, just for efficiency. *)
  let vars : ref (list univ_name) = mk_ref [] in
  let seen : ref (RBSet.t univ_name) = mk_ref (empty ()) in
  let reg (u:univ_name) : unit =
    if not (mem u !seen) then (
      seen := add u !seen;
      vars := u::!vars
    )
  in
  let get () : list univ_name = List.rev !vars in

  (* Visit the sigelt and rely on side effects to capture all
  the names. This goes roughly in left-to-right order. *)
  let _ = Visit.visit_sigelt false
            (fun t -> t)
            (fun u -> ignore (match u with
                              | U_name nm -> reg nm
                              | _ -> ());
                      u) s
  in
  let unames = get () in

  match s.sigel with
  | Sig_inductive_typ _
  | Sig_datacon _ -> failwith "Impossible: collect_annotated_universes: bare data/type constructor"
  | Sig_bundle {ses=sigs; lids} ->
    let usubst = Subst.univ_var_closing unames in
    { s with sigel = Sig_bundle {ses=sigs |> List.map (fun se ->
      match se.sigel with
      | Sig_inductive_typ {lid; params=bs; num_uniform_params=num_uniform; t; mutuals=lids1; ds=lids2} ->
        { se with sigel = Sig_inductive_typ {lid;
                                             us=unames;
                                             params=Subst.subst_binders usubst bs;
                                             num_uniform_params=num_uniform;
                                             t=Subst.subst (Subst.shift_subst (List.length bs) usubst) t;
                                             mutuals=lids1;
                                             ds=lids2;
                                             injective_type_params=false} }
      | Sig_datacon {lid;t;ty_lid=tlid;num_ty_params=n;mutuals=lids} ->
        { se with sigel = Sig_datacon {lid;
                                       us=unames;
                                       t=Subst.subst usubst t;
                                       ty_lid=tlid;
                                       num_ty_params=n;
                                       mutuals=lids;
                                       injective_type_params=false} }
      | _ -> failwith "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
      ); lids} }
  | Sig_declare_typ {lid; t} ->
    { s with sigel = Sig_declare_typ {lid; us=unames; t=Subst.close_univ_vars unames t} }
  | Sig_let {lbs=(b, lbs); lids} ->
    let usubst = Subst.univ_var_closing unames in
    //This respects the invariant enforced by FStarC.Syntax.Util.check_mutual_universes
    { s with sigel = Sig_let {lbs=(b, lbs |> List.map (fun lb -> { lb with lbunivs = unames; lbdef = Subst.subst usubst lb.lbdef; lbtyp = Subst.subst usubst lb.lbtyp }));
                              lids} }
  | Sig_assume {lid;phi=fml} ->
    { s with sigel = Sig_assume {lid; us=unames; phi=Subst.close_univ_vars unames fml} }
  | Sig_effect_abbrev {lid;bs;comp=c;cflags=flags} ->
    let usubst = Subst.univ_var_closing unames in
    { s with sigel = Sig_effect_abbrev {lid;
                                        us=unames;
                                        bs=Subst.subst_binders usubst bs;
                                        comp=Subst.subst_comp usubst c;
                                        cflags=flags} }

  | Sig_fail {errs; rng; fail_in_lax=lax; ses} ->
    { s with sigel = Sig_fail {errs; rng;
                               fail_in_lax=lax;
                               ses=List.map generalize_annotated_univs ses} }

  (* Works over the signature only *)
  | Sig_new_effect ed ->
    let generalize_annotated_univs_signature (s : effect_signature) : effect_signature =
      match s with
      | Layered_eff_sig (n, (_, t)) ->
        let uvs = Free.univnames t |> elems in
        let usubst = Subst.univ_var_closing uvs in
        Layered_eff_sig (n, (uvs, Subst.subst usubst t))
      | WP_eff_sig (_, t) ->
        let uvs = Free.univnames t |> elems in
        let usubst = Subst.univ_var_closing uvs in
        WP_eff_sig (uvs, Subst.subst usubst t)
    in
    { s with sigel = Sig_new_effect { ed with signature = generalize_annotated_univs_signature ed.signature } }

  | Sig_sub_effect _
  | Sig_polymonadic_bind _
  | Sig_polymonadic_subcomp _
  | Sig_splice _
  | Sig_pragma _ ->
    s

let is_special_effect_combinator = function
  | "lift1"
  | "lift2"
  | "pure"
  | "app"
  | "push"
  | "wp_if_then_else"
  | "wp_assert"
  | "wp_assume"
  | "wp_close"
  | "stronger"
  | "ite_wp"
  | "wp_trivial"
  | "ctx"
  | "gctx"
  | "lift_from_pure"
  | "return_wp"
  | "return_elab"
  | "bind_wp"
  | "bind_elab"
  | "repr"
  | "post"
  | "pre"
  | "wp" -> true
  | _ -> false

let rec sum_to_universe u n =
    if n = 0 then u else U_succ (sum_to_universe u (n-1))

let int_to_universe n = sum_to_universe U_zero n

let rec desugar_maybe_non_constant_universe t
  : either int Syntax.universe  (* level of universe or desugared universe *)
=
  match (unparen t).tm with
  | Wild -> Inr U_unknown
  | Uvar u -> Inr (U_name u)

  | Const (Const_int (repr, _)) ->
      (* TODO : That might be a little dangerous... *)
      let n = int_of_string repr in
      if n < 0
      then raise_error t Errors.Fatal_NegativeUniverseConstFatal_NotSupported
             ("Negative universe constant  are not supported : " ^ repr);
      Inl n
  | Op (op_plus, [t1 ; t2]) ->
      assert (Ident.string_of_id op_plus = "+") ;
      let u1 = desugar_maybe_non_constant_universe t1 in
      let u2 = desugar_maybe_non_constant_universe t2 in
      begin match u1, u2 with
          | Inl n1, Inl n2 -> Inl (n1+n2)
          | Inl n, Inr u
          | Inr u, Inl n -> Inr (sum_to_universe u n)
          | Inr u1, Inr u2 ->
            raise_error t Errors.Fatal_UniverseMightContainSumOfTwoUnivVars
              ("This universe might contain a sum of two universe variables " ^ show t)
      end
  | App _ ->
      let rec aux t univargs  =
        match (unparen t).tm with
        | App(t, targ, _) ->
            let uarg = desugar_maybe_non_constant_universe targ in
            aux t (uarg::univargs)
        | Var max_lid ->
            assert (Ident.string_of_lid max_lid = "max") ;
            if List.existsb (function Inr _ -> true | _ -> false) univargs
            then Inr (U_max (List.map (function Inl n -> int_to_universe n | Inr u -> u) univargs))
            else
              let nargs = List.map (function Inl n -> n | Inr _ -> failwith "impossible") univargs in
              Inl (List.fold_left (fun m n -> if m > n then m else n) 0 nargs)
        (* TODO : Might not be the best place to raise the error... *)
        | _ -> raise_error t Errors.Fatal_UnexpectedTermInUniverse ("Unexpected term " ^ term_to_string t ^ " in universe context")
      in aux t []
  | _ -> raise_error t Errors.Fatal_UnexpectedTermInUniverse ("Unexpected term " ^ term_to_string t ^ " in universe context")

let desugar_universe t : Syntax.universe =
    let u = desugar_maybe_non_constant_universe t in
    match u with
        | Inl n -> int_to_universe n
        | Inr u -> u

let check_no_aq (aq : antiquotations_temp) : unit =
    match aq with
    | [] -> ()
    | (bv, { n = Tm_quoted (e, { qkind = Quote_dynamic })})::_ ->
        raise_error e Errors.Fatal_UnexpectedAntiquotation
          (BU.format1 "Unexpected antiquotation: `@(%s)" (show e))
    | (bv, e)::_ ->
        raise_error e Errors.Fatal_UnexpectedAntiquotation
          (BU.format1 "Unexpected antiquotation: `#(%s)" (show e))

let check_linear_pattern_variables pats (r:Range.range) =
  // returns the set of pattern variables
  let rec pat_vars p : RBSet.t bv =
    match p.v with
    | Pat_dot_term _
    | Pat_constant _ -> empty ()
    | Pat_var x ->
      (* Only consider variables that actually have names,
      not wildcards. *)
      if string_of_id x.ppname = Ident.reserved_prefix
      then empty ()
      else singleton x
    | Pat_cons(_, _, pats) ->
      let aux out (p, _) =
          let p_vars = pat_vars p in
          let intersection = inter p_vars out in
          if is_empty intersection
          then union out p_vars
          else
            let duplicate_bv = List.hd (elems intersection) in
            raise_error r Errors.Fatal_NonLinearPatternNotPermitted
              (BU.format1 "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                (show duplicate_bv.ppname))
      in
      List.fold_left aux (empty ()) pats
  in

  // check that the same variables are bound in each pattern
  match pats with
  | [] -> ()
  | [p] -> pat_vars p |> ignore
  | p::ps ->
    let pvars = pat_vars p in
    let aux p =
      if equal pvars (pat_vars p) then () else
      let symdiff s1 s2 = union (diff s1 s2) (diff s2 s1) in
      let nonlinear_vars = symdiff pvars (pat_vars p) in
      let first_nonlinear_var = List.hd (elems nonlinear_vars) in
      raise_error r Errors.Fatal_IncoherentPatterns
        (BU.format1 "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (show first_nonlinear_var.ppname))
    in
    List.iter aux ps

let smt_pat_lid (r:Range.range) = Ident.set_lid_range C.smtpat_lid r
let smt_pat_or_lid (r:Range.range) = Ident.set_lid_range C.smtpatOr_lid r

// [hoist_pat_ascription' pat] pulls [PatAscribed] nodes out of [pat]
// and construct a tuple that consists in a non-ascribed pattern and a
// type abscription.  Note [hoist_pat_ascription'] only works with
// patterns whose ascriptions live under tuple or list nodes. This
// function is used for [LetOperator] desugaring in
// [resugar_data_pat], because direct ascriptions in patterns are
// dropped (see issue #2678).
let rec hoist_pat_ascription' (pat: pattern): pattern & option term
  = let mk tm = mk_term tm (pat.prange) Type_level in
    let handle_list type_lid pat_cons pats =
      let pats, terms = List.unzip (List.map hoist_pat_ascription' pats) in
      if List.for_all None? terms
      then pat, None
      else
        let terms = List.map (function | Some t -> t | None -> mk Wild) terms in
        { pat with pat = pat_cons pats}
      , Some (mkApp (mk type_lid) (List.map (fun t -> (t, Nothing)) terms) pat.prange)
    in match pat.pat with
  | PatList pats -> handle_list (Var C.list_lid) PatList pats
  | PatTuple (pats, dep) ->
    handle_list
      (Var ((if dep then C.mk_dtuple_lid else C.mk_tuple_lid) (List.length pats) pat.prange))
      (fun pats -> PatTuple (pats, dep)) pats
  | PatAscribed (pat, (typ, None)) -> pat, Some typ
  // if [pat] is not a list, a tuple or an ascription, we cannot
  // compose (at least not in a simple way) sub ascriptions, thus we
  // return the pattern directly
  | _ -> pat, None

let hoist_pat_ascription (pat: pattern): pattern
  = let pat, typ = hoist_pat_ascription' pat in
    match typ with
  | Some typ -> { pat with pat = PatAscribed (pat, (typ, None)) }
  | None     -> pat

(* TODO : Patterns should be checked that there are no incompatible type ascriptions *)
(* and these type ascriptions should not be dropped !!!                              *)
let rec desugar_data_pat
    (top_level_ascr_allowed : bool)
    (env:env_t)
    (p:pattern)
    : (env_t & bnd & list annotated_pat) & antiquotations_temp =
  let resolvex (l:lenv_t) e x =
    (* This resolution function will be shared across
     * the cases of a PatOr, so different ocurrences of
     * a same (surface) variable are mapped to exactly the
     * same internal variable. *)
    match BU.find_opt (fun y -> (string_of_id y.ppname = string_of_id x)) l with
    | Some y -> l, e, y
    | _ ->
      let e, xbv = push_bv e x in
      (xbv::l), e, xbv
  in

  let rec aux' (top:bool) (loc:lenv_t) (aqs:antiquotations_temp) (env:env_t) (p:pattern)
    : lenv_t                                  (* list of all BVs mentioned *)
    & antiquotations_temp                     (* updated antiquotations_temp *)
    & env_t                                   (* env updated with the BVs pushed in *)
    & bnd                                     (* a binder for the pattern *)
    & pat                                     (* elaborated pattern *)
    & list (bv & Syntax.typ & list S.term)  (* ascripted pattern variables (collected) with attributes *)
    =
    let pos q = Syntax.withinfo q p.prange in
    let pos_r r q = Syntax.withinfo q r in
    let orig = p in
    match p.pat with
      | PatOr _ -> failwith "impossible: PatOr handled below"

      | PatOp op ->
        (* Turn into a PatVar and recurse *)
        let id_op = mk_ident (compile_op 0 (string_of_id op) (range_of_id op), (range_of_id op)) in
        let p = { p with pat = PatVar (id_op, None, []) } in
        aux loc aqs env p

      | PatAscribed(p, (t, tacopt)) ->
        (* Check that there's no tactic *)
        begin match tacopt with
          | None -> ()
          | Some _ ->
            raise_error orig Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly
              "Type ascriptions within patterns cannot be associated with a tactic"
        end;
        let loc, aqs, env', binder, p, annots = aux loc aqs env p in
        let annots', binder, aqs = match binder with
            | LetBinder _ -> failwith "impossible"
            | LocalBinder(x, aq, attrs) ->
              let t, aqs' = desugar_term_aq env (close_fun env t) in
              let x = { x with sort = t } in
              [(x, t, attrs)], LocalBinder(x, aq, attrs), aqs'@aqs
        in
        (* Check that the ascription is over a variable, and not something else *)
        begin match p.v with
          | Pat_var _ -> ()
          | _ when top && top_level_ascr_allowed -> ()
          | _ ->
            raise_error orig Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly
              "Type ascriptions within patterns are only allowed on variables"
        end;
        loc, aqs, env', binder, p, annots'@annots

      | PatWild (aq, attrs) ->
        let aq = trans_bqual env aq in
        let attrs = attrs |> List.map (desugar_term env) in
        let x = S.new_bv (Some p.prange) (tun_r p.prange) in
        loc, aqs, env, LocalBinder(x, aq, attrs), pos <| Pat_var x, []

      | PatConst c ->
        let x = S.new_bv (Some p.prange) (tun_r p.prange) in
        loc, aqs, env, LocalBinder(x, None, []), pos <| Pat_constant c, []

      | PatVQuote e ->
        // Here, we desugar [PatVQuote e] into a [PatConst s] where
        // [s] is the (string represented) lid of [e] (see function
        // [desugar_vquote]), then re-run desugaring on [PatConst s].
        let pat = PatConst (Const_string (desugar_vquote env e p.prange, p.prange)) in
        aux' top loc aqs env ({ p with pat })

      | PatTvar(x, aq, attrs)
      | PatVar (x, aq, attrs) ->
        let aq = trans_bqual env aq in
        let attrs = attrs |> List.map (desugar_term env) in
        let loc, env, xbv = resolvex loc env x in
        loc, aqs, env, LocalBinder(xbv, aq, attrs), pos <| Pat_var xbv, []

      | PatName l ->
        let l = fail_or env (try_lookup_datacon env) l in
        let x = S.new_bv (Some p.prange) (tun_r p.prange) in
        loc, aqs, env, LocalBinder(x,  None, []), pos <| Pat_cons(l, None, []), []

      | PatApp({pat=PatName l}, args) ->
        let loc, aqs, env, annots, args = List.fold_right (fun arg (loc, aqs, env, annots, args) ->
          let loc, aqs, env, b, arg, ans = aux loc aqs env arg in
          let imp = is_implicit b in
          (loc, aqs, env, ans@annots, (arg, imp)::args)) args (loc, aqs, env, [], []) in
        let l = fail_or env  (try_lookup_datacon env) l in
        let x = S.new_bv (Some p.prange) (tun_r p.prange) in
        loc, aqs, env, LocalBinder(x, None, []), pos <| Pat_cons(l, None, args), annots

      | PatApp _ -> raise_error p Errors.Fatal_UnexpectedPattern "Unexpected pattern"

      | PatList pats ->
        let loc, aqs, env, annots, pats = List.fold_right (fun pat (loc, aqs, env, annots, pats) ->
          let loc, aqs, env, _, pat, ans = aux loc aqs env pat in
          loc, aqs, env, ans@annots, pat::pats) pats (loc, aqs, env, [], []) in
        let pat = List.fold_right (fun hd tl ->
            let r = Range.union_ranges hd.p tl.p in
            pos_r r <| Pat_cons(S.lid_and_dd_as_fv C.cons_lid (Some Data_ctor), None, [(hd, false);(tl, false)])) pats
                        (pos_r (Range.end_range p.prange) <| Pat_cons(S.lid_and_dd_as_fv C.nil_lid (Some Data_ctor), None, [])) in
        let x = S.new_bv (Some p.prange) (tun_r p.prange) in
        loc, aqs, env, LocalBinder(x, None, []), pat, annots

      | PatTuple(args, dep) ->
        let loc, aqs, env, annots, args = List.fold_left (fun (loc, aqs, env, annots, pats) p ->
          let loc, aqs, env, _, pat, ans = aux loc aqs env p in
          loc, aqs, env, ans@annots, (pat, false)::pats) (loc, aqs, env, [], []) args in
        let args = List.rev args in
        let l = if dep then C.mk_dtuple_data_lid (List.length args) p.prange
                else C.mk_tuple_data_lid (List.length args) p.prange in
        let constr = fail_or env  (Env.try_lookup_lid env) l in
        let l = match constr.n with
          | Tm_fvar fv -> fv
          | _ -> failwith "impossible" in
        let x = S.new_bv (Some p.prange) (tun_r p.prange) in
        loc, aqs, env, LocalBinder(x, None, []), pos <| Pat_cons(l, None, args), annots

      | PatRecord (fields) ->
        (* Record patterns have to wait for type information to be fully resolved *)
        let field_names, pats = List.unzip fields in
        let typename, field_names =
          match fields with
          | [] -> None, field_names
          | (f, _)::_ ->
            match try_lookup_record_by_field_name env f with
            | None -> None, field_names
            | Some r -> Some r.typename, qualify_field_names r.typename field_names
        in
        (* Just build a candidate constructor, as we do for Record literals *)
        let candidate_constructor =
            let lid = lid_of_path ["__dummy__"] p.prange in
            S.lid_and_dd_as_fv
              lid
              (Some
                 (Unresolved_constructor
                     ({ uc_base_term = false;
                        uc_typename = typename;
                        uc_fields = field_names })))
        in
        let loc, aqs, env, annots, pats =
          List.fold_left
            (fun (loc, aqs, env, annots, pats) p ->
              let loc, aqs, env, _, pat, ann = aux loc aqs env p in
              loc, aqs, env, ann@annots, (pat, false)::pats)
            (loc, aqs, env, [], [])
            pats
        in
        let pats = List.rev pats in
        (* TcTerm will look for the Unresolved_constructor qualifier
           and resolve the pattern fully in tc_pat *)
        let pat = pos <| Pat_cons(candidate_constructor, None, pats) in
        let x = S.new_bv (Some p.prange) (tun_r p.prange) in
        loc, aqs, env, LocalBinder(x, None, []), pat, annots
  and aux loc aqs env p = aux' false loc aqs env p
  in

  (* Explode PatOr's and call aux *)
  let aux_maybe_or env (p:pattern) =
    let loc = [] in
    match p.pat with
      | PatOr [] -> failwith "impossible"
      | PatOr (p::ps) ->
        let loc, aqs, env, var, p, ans = aux' true loc [] env p in
        let loc, aqs, env, ps = List.fold_left (fun (loc, aqs, env, ps) p ->
          let loc, aqs, env, _, p, ans = aux' true loc aqs env p in
          loc, aqs, env, (p,ans)::ps) (loc, aqs, env, []) ps in
        let pats = ((p,ans)::List.rev ps) in
        (env, var, pats), aqs
      | _ ->
        let loc, aqs, env, var, pat, ans = aux' true loc [] env p in
        (env, var, [(pat, ans)]), aqs
  in

  let (env, b, pats), aqs = aux_maybe_or env p in
  check_linear_pattern_variables (List.map fst pats) p.prange;
  (env, b, pats), aqs

and desugar_binding_pat_maybe_top top env p
  : (env_t                 (* environment with patterns variables pushed in *)
  & bnd                    (* a binder for the pattern *)
  & list annotated_pat)    (* elaborated patterns with their variable annotations *)
  & antiquotations_temp    (* antiquotations_temp found in binder types *)
  =

  if top then
    let mklet x ty (tacopt : option S.term) : (env_t & bnd & list annotated_pat) =
    // GM: ^ I seem to need the type annotation here,
    //     or F* gets confused between tuple2 and tuple3 apparently?
        env, LetBinder(qualify env x, (ty, tacopt)), []
    in
    let op_to_ident x = mk_ident (compile_op 0 (string_of_id x) (range_of_id x), (range_of_id x)) in
    match p.pat with
    | PatOp x ->
        mklet (op_to_ident x) (tun_r (range_of_id x)) None, []
    | PatVar (x, _, _) ->
        mklet x (tun_r (range_of_id x)) None, []
    | PatAscribed({pat=PatOp x}, (t, tacopt)) ->
        let tacopt = BU.map_opt tacopt (desugar_term env) in
        let t, aq = desugar_term_aq env t in
        mklet (op_to_ident x) t tacopt, aq
    | PatAscribed({pat=PatVar (x, _, _)}, (t, tacopt)) ->
        let tacopt = BU.map_opt tacopt (desugar_term env) in
        let t, aq = desugar_term_aq env t in
        mklet x t tacopt, aq
    | _ ->
        raise_error p Errors.Fatal_UnexpectedPattern "Unexpected pattern at the top-level"
  else
    let (env, binder, p), aq = desugar_data_pat true env p in
    let p = match p with
      | [{v=Pat_var _}, _] -> []
      | _ -> p in
    (env, binder, p), aq

and desugar_binding_pat_aq env p = desugar_binding_pat_maybe_top false env p

and desugar_match_pat_maybe_top _ env pat =
  let (env, _, pat), aqs = desugar_data_pat false env pat in
  (env, pat), aqs

and desugar_match_pat env p = desugar_match_pat_maybe_top false env p

and desugar_term_aq env e : S.term & antiquotations_temp =
    let env = Env.set_expect_typ env false in
    desugar_term_maybe_top false env e

and desugar_term env e : S.term =
    let t, aq = desugar_term_aq env e in
    check_no_aq aq;
    t

and desugar_typ_aq env e : S.term & antiquotations_temp =
    let env = Env.set_expect_typ env true in
    desugar_term_maybe_top false env e

and desugar_typ env e : S.term =
    let t, aq = desugar_typ_aq env e in
    check_no_aq aq;
    t

and desugar_machine_integer env repr (signedness, width) range =
  let tnm = if width = Sizet then "FStar.SizeT" else
    "FStar." ^
    (match signedness with | Unsigned -> "U" | Signed -> "") ^ "Int" ^
    (match width with | Int8 -> "8" | Int16 -> "16" | Int32 -> "32" | Int64 -> "64")
  in
  //we do a static check of integer constants
  //and coerce them to the appropriate type using the internal coercion
  // __uint_to_t or __int_to_t
  //Rather than relying on a verification condition to check this trivial property
  if not (within_bounds repr signedness width)
  then FStarC.Errors.log_issue range Errors.Error_OutOfRange
         (BU.format2 "%s is not in the expected range for %s" repr tnm);
  let private_intro_nm = tnm ^
    ".__" ^ (match signedness with | Unsigned -> "u" | Signed -> "") ^ "int_to_t"
  in
  let intro_nm = tnm ^
    "." ^ (match signedness with | Unsigned -> "u" | Signed -> "") ^ "int_to_t"
  in
  let lid = lid_of_path (path_of_text intro_nm) range in
  let lid =
    match Env.try_lookup_lid env lid with
    | Some intro_term ->
      begin match intro_term.n with
        | Tm_fvar fv ->
          let private_lid = lid_of_path (path_of_text private_intro_nm) range in
          let private_fv = S.lid_and_dd_as_fv private_lid fv.fv_qual in
          {intro_term with n=Tm_fvar private_fv}
        | _ ->
          failwith ("Unexpected non-fvar for " ^ intro_nm)
      end
    | None ->
      raise_error range Errors.Fatal_UnexpectedNumericLiteral
        (BU.format1 "Unexpected numeric literal.  Restart F* to load %s." tnm) in
  let repr' = S.mk (Tm_constant (Const_int (repr, None))) range in
  let app = S.mk (Tm_app {hd=lid; args=[repr', S.as_aqual_implicit false]}) range in
  S.mk (Tm_meta {tm=app;
                 meta=Meta_desugared (Machine_integer (signedness, width))}) range

and desugar_term_maybe_top (top_level:bool) (env:env_t) (top:term) : S.term & antiquotations_temp =
  let mk e = S.mk e top.range in
  let noaqs = [] in
  let join_aqs aqs = List.flatten aqs in
  let setpos e = {e with pos=top.range} in
  let desugar_binders env binders =
      let env, bs_rev =
          List.fold_left
            (fun (env, bs) b ->
              let bb = desugar_binder env b in
              let b, env = as_binder env b.aqual bb in
              env, b::bs)
            (env, [])
            binders
      in
      env, List.rev bs_rev
  in
  let unqual_bv_of_binder b =
      match b with
      | {binder_bv=x; binder_qual=None; binder_attrs=[]} -> x
      | _ ->
        raise_error b Fatal_UnexpectedTerm "Unexpected qualified binder in ELIM_EXISTS"
  in
  if !dbg_ToSyntax then
    BU.print1 "desugaring (%s)\n\n" (show top);
  begin match (unparen top).tm with
    | Wild -> setpos tun, noaqs

    | Labeled _ -> desugar_formula env top, noaqs

    | Requires (t, lopt) ->
      desugar_formula env t, noaqs

    | Ensures (t, lopt) ->
      desugar_formula env t, noaqs

    | Attributes ts ->
        failwith "Attributes should not be desugared by desugar_term_maybe_top"
        // desugar_attributes env ts

    | Const (Const_int (i, Some size)) ->
        desugar_machine_integer env i size top.range, noaqs

    | Const c ->
        mk (Tm_constant c), noaqs

    | Op(id, args) when string_of_id id = "=!=" ->
      let r = range_of_id id in
      let e = mk_term (Op(Ident.mk_ident ("==", r), args)) top.range top.level in
      desugar_term_aq env (mk_term(Op(Ident.mk_ident ("~",r), [e])) top.range top.level)

    (* if op_Star has not been rebound, then it's reserved for tuples *)
    | Op(op_star, [lhs;rhs]) when
      (Ident.string_of_id op_star = "*" &&
       op_as_term env 2 op_star |> Option.isNone) ->
      (* See the comment in parse.mly to understand why this implicitly relies
       * on the presence of a Paren node in the AST. *)
      let rec flatten t = match t.tm with
        // * is left-associative
        | Op(id, [t1;t2]) when
           string_of_id id = "*" &&
           op_as_term env 2 op_star |> Option.isNone ->
          flatten t1 @ [ t2 ]
        | _ -> [t]
      in
      let terms = flatten lhs in
      //make the surface syntax for a non-dependent tuple
      let t = {top with tm=Sum(List.map Inr terms, rhs)} in
      desugar_term_maybe_top top_level env t

    | Tvar a ->
      setpos <| (fail_or2 (try_lookup_id env) a), noaqs

    | Uvar u ->
      raise_error top Errors.Fatal_UnexpectedUniverseVariable
          ("Unexpected universe variable " ^
            string_of_id u ^
            " in non-universe context")

    | Op(s, [f;e]) when Ident.string_of_id s = "<|" ->
      desugar_term_maybe_top top_level env (mkApp f [e,Nothing] top.range)

    | Op(s, [e;f]) when Ident.string_of_id s = "|>" ->
      desugar_term_maybe_top top_level env (mkApp f [e,Nothing] top.range)

    | Op(s, args) ->
      begin
      match op_as_term env (List.length args) s with
      | None ->
        raise_error s Errors.Fatal_UnepxectedOrUnboundOperator
                    ("Unexpected or unbound operator: " ^
                     Ident.string_of_id s)
      | Some op ->
            if List.length args > 0 then
              let args, aqs = args |> List.map (fun t -> let t', s = desugar_term_aq env t in
                                                         (t', None), s) |> List.unzip in
              mk (Tm_app {hd=op; args}), join_aqs aqs
            else
              op, noaqs
      end

    | Construct (n, [(a, _)]) when (string_of_lid n) = "SMTPat" ->
        desugar_term_maybe_top top_level env
          ({top with tm = App ({top with tm = Var (smt_pat_lid top.range)}, a, Nothing)})

    | Construct (n, [(a, _)]) when (string_of_lid n) = "SMTPatT" ->
        Errors.log_issue top Errors.Warning_SMTPatTDeprecated "SMTPatT is deprecated; please just use SMTPat";
        desugar_term_maybe_top top_level env
          ({top with tm = App ({top with tm = Var (smt_pat_lid top.range) }, a, Nothing)})

    | Construct (n, [(a, _)]) when (string_of_lid n) = "SMTPatOr" ->
        desugar_term_maybe_top top_level env
          ({top with tm = App ({top with tm = Var (smt_pat_or_lid top.range)}, a, Nothing)})

    | Name lid when string_of_lid lid = "Type0"  ->
        mk (Tm_type U_zero), noaqs
    | Name lid when string_of_lid lid = "Type"   ->
        mk (Tm_type U_unknown), noaqs
    | Construct (lid, [t, UnivApp]) when string_of_lid lid = "Type" ->
        mk (Tm_type (desugar_universe t)), noaqs
    | Name lid when string_of_lid lid = "Effect" ->
        mk (Tm_constant Const_effect), noaqs
    | Name lid when string_of_lid lid = "True"   ->
        S.fvar_with_dd (Ident.set_lid_range Const.true_lid top.range) None,
                             noaqs
    | Name lid when string_of_lid lid = "False"   ->
        S.fvar_with_dd (Ident.set_lid_range Const.false_lid top.range) None,
                              noaqs
    | Projector (eff_name, id)
      when is_special_effect_combinator (string_of_id id) && Env.is_effect_name env eff_name ->
      (* TODO : would it be possible to normalize the effect name at that point so that *)
      (* we get back the original effect definition instead of an effect abbreviation *)
      let txt = string_of_id id in
      begin match try_lookup_effect_defn env eff_name with
        | Some ed ->
          let lid = U.dm4f_lid ed txt in
          S.fvar_with_dd lid None, noaqs
        | None ->
          failwith (BU.format2 "Member %s of effect %s is not accessible \
                                (using an effect abbreviation instead of the original effect ?)"
                               (Ident.string_of_lid eff_name)
                               txt)
      end

    | Var l
    | Name l ->
      desugar_name mk setpos env true l, noaqs

    | Projector (l, i) ->
      let name =
        match Env.try_lookup_datacon env l with
        | Some _ -> Some (true, l)
        | None ->
          match Env.try_lookup_root_effect_name env l with
          | Some new_name -> Some (false, new_name)
          | _ -> None
      in
      begin match name with
      | Some (resolve, new_name) ->
        desugar_name mk setpos env resolve (mk_field_projector_name_from_ident new_name i), noaqs
      | _ ->
        raise_error top Errors.Fatal_EffectNotFound (BU.format1 "Data constructor or effect %s not found" (string_of_lid l))
      end

    | Discrim lid ->
      begin match Env.try_lookup_datacon env lid with
      | None ->
        raise_error top Errors.Fatal_DataContructorNotFound (BU.format1 "Data constructor %s not found" (string_of_lid lid))
      | _ ->
        let lid' = U.mk_discriminator lid in
        desugar_name mk setpos env true lid', noaqs
      end

    | Construct(l, args) ->
        begin match Env.try_lookup_datacon env l with
        | Some head ->
            let head = mk (Tm_fvar head) in
            begin match args with
              | [] -> head, noaqs
              | _ ->
                let universes, args = BU.take (fun (_, imp) -> imp = UnivApp) args in
                let universes = List.map (fun x -> desugar_universe (fst x)) universes in
                let args, aqs = List.map (fun (t, imp) ->
                  let te, aq = desugar_term_aq env t in
                  arg_withimp_t imp te, aq) args |> List.unzip in
                let head = if universes = [] then head else mk (Tm_uinst(head, universes)) in
                let tm =
                  if List.length args = 0
                  then head
                  else mk (Tm_app {hd=head; args}) in
                tm, join_aqs aqs
            end
        | None ->
          match Env.try_lookup_effect_name env l with
          | None ->
            raise_error l Errors.Fatal_ConstructorNotFound
              ("Constructor " ^ (string_of_lid l) ^ " not found")
          | Some _ ->
            raise_error l Errors.Fatal_UnexpectedEffect
              ("Effect " ^ (string_of_lid l) ^ " used at an unexpected position")
        end

    | Sum(binders, t)
      when BU.for_all (function Inr _ -> true | _ -> false) binders ->
      //non-dependent tuple
      let terms =
         (binders |>
          List.map (function Inr x -> x | Inl _ -> failwith "Impossible"))
         @[t]
      in
      let targs, aqs =
        terms |>
        List.map (fun t -> let t', aq = desugar_typ_aq env t in as_arg t', aq) |>
        List.unzip
      in
      let tup = fail_or env (Env.try_lookup_lid env) (C.mk_tuple_lid (List.length targs) top.range) in
      mk (Tm_app {hd=tup; args=targs}), join_aqs aqs

    | Sum(binders, t) -> //dependent tuple
      let env, _, targs = List.fold_left (fun (env, tparams, typs) b ->
                let xopt, t, attrs =
                  match b with
                  | Inl b -> desugar_binder env b
                  | Inr t -> None, desugar_typ env t, []
                in
                let env, x =
                    match xopt with
                    | None -> env, S.new_bv (Some top.range) (setpos tun)
                    | Some x -> push_bv env x in
                (env, tparams@[mk_binder_with_attrs ({x with sort=t}) None attrs],
                 typs@[as_arg <| no_annot_abs tparams t]))
        (env, [], [])
        (binders@[Inl <| mk_binder (NoName t) t.range Type_level None]) in
      let tup = fail_or env (try_lookup_lid env) (C.mk_dtuple_lid (List.length targs) top.range) in
      mk <| Tm_app {hd=tup; args=targs}, noaqs

    | Product(binders, t) ->
      let bs, t = uncurry binders t in
      let rec aux env aqs bs = function
        | [] ->
          let cod = desugar_comp top.range true env t in
          setpos <| U.arrow (List.rev bs) cod, aqs

        | hd::tl ->
          let bb, aqs' = desugar_binder_aq env hd in
          let b, env = as_binder env hd.aqual bb in 
          aux env (aqs'@aqs) (b::bs) tl
      in
      aux env [] [] bs

    | Refine(b, f) ->
      begin match desugar_binder env b with
        | (None, _, _) -> failwith "Missing binder in refinement"

        | b ->
          let b, env = as_binder env None b in
          let f = desugar_formula env f in
          setpos <| U.refine b.binder_bv f, noaqs
      end

    | Function (branches, r1) ->
      let x = Ident.gen r1 in
      let t' =
        mk_term (Abs([mk_pattern (PatVar(x,None,[])) r1],
                   mk_term (Match(mk_term (Var(lid_of_ids [x])) r1 Expr, None, None, branches)) top.range Expr))
        top.range Expr
      in
      desugar_term_maybe_top top_level env t'

    | Abs(binders, body) ->
      (* First of all, forbid definitions such as `f x x = ...` *)
      let bvss = List.map gather_pattern_bound_vars binders in
      let check_disjoint (sets : list (FlatSet.t ident)) : option ident =
        let rec aux acc sets =
            match sets with
            | [] -> None
            | set::sets ->
                let i = inter acc set in
                if is_empty i
                then aux (union acc set) sets
                else Some (List.hd (elems i))
        in
        aux (empty ()) sets
      in
      begin match check_disjoint bvss with
      | None -> ()
      | Some id ->
          let open FStarC.Pprint in
          let open FStarC.Class.PP in
          raise_error id Errors.Fatal_NonLinearPatternNotPermitted [
            text "Non-linear patterns are not permitted.";
            text "The variable " ^/^ squotes (pp id) ^/^ text " appears more than once in this function definition."
          ]
      end;

      let binders = binders |> List.map replace_unit_pattern in
      let _, ftv = List.fold_left (fun (env, ftvs) pat ->
        match pat.pat with
          | PatAscribed(_, (t, None)) -> env, free_type_vars env t@ftvs
          | PatAscribed(_, (t, Some tac)) -> env, free_type_vars env t@free_type_vars env tac@ftvs
          | _ -> env, ftvs) (env, []) binders in
      let ftv = sort_ftv ftv in
      let binders = (ftv |> List.map (fun a ->
                        mk_pattern (PatTvar(a, Some AST.Implicit, [])) top.range))
                    @binders in //close over the free type variables
      (*
         fun (P1 x1) (P2 x2) (P3 x3) -> e

            is desugared to

         fun y1 y2 y3 -> match (y1, y2, y3) with
                | (P1 x1, P2 x2, P3 x3) -> [[e]]
      *)
      let rec aux aqs env bs sc_pat_opt pats : S.term & antiquotations_temp =
        match pats with
        | [] ->
            let body, aq = desugar_term_aq env body in
            let body = match sc_pat_opt with
            | Some (sc, pat) ->
                let body = Subst.close (S.pat_bvs pat |> List.map S.mk_binder) body in
                S.mk (Tm_match {scrutinee=sc;
                                ret_opt=None;
                                brs=[(pat, None, body)];
                                rc_opt=None}) body.pos
            | None -> body in
            setpos (no_annot_abs (List.rev bs) body), aq@aqs

        | p::rest ->
            let (env, b, pat), aq = desugar_binding_pat_aq env p in
            let pat =
                match pat with
                | [] -> None
                | [p, _] -> Some p // NB: We ignore the type annotation here, the typechecker catches that anyway in tc_abs
                | _ ->
                  raise_error p Errors.Fatal_UnsupportedDisjuctivePatterns "Disjunctive patterns are not supported in abstractions"
            in
            let b, sc_pat_opt =
                match b with
                | LetBinder _ -> failwith "Impossible"
                | LocalBinder (x, aq, attrs) ->
                    let sc_pat_opt =
                        match pat, sc_pat_opt with
                        | None, _ -> sc_pat_opt
                        | Some p, None -> Some (S.bv_to_name x, p)
                        | Some p, Some (sc, p') -> begin
                          match sc.n, p'.v with
                          | Tm_name _, _ ->
                            let tup2 = S.lid_and_dd_as_fv (C.mk_tuple_data_lid 2 top.range) (Some Data_ctor) in
                            let sc = S.mk (Tm_app {hd=mk (Tm_fvar tup2);
                                                   args=[as_arg sc; as_arg <| S.bv_to_name x]}) top.range in
                            let p = withinfo (Pat_cons(tup2, None, [(p', false);(p, false)])) (Range.union_ranges p'.p p.p) in
                            Some(sc, p)
                          | Tm_app {args}, Pat_cons(_, _, pats) ->
                            let tupn = S.lid_and_dd_as_fv (C.mk_tuple_data_lid (1 + List.length args) top.range) (Some Data_ctor) in
                            let sc = mk (Tm_app {hd=mk (Tm_fvar tupn);
                                                 args=args@[as_arg <| S.bv_to_name x]}) in
                            let p = withinfo (Pat_cons(tupn, None, pats@[(p, false)])) (Range.union_ranges p'.p p.p) in
                            Some(sc, p)
                          | _ -> failwith "Impossible"
                          end
                    in
                    (mk_binder_with_attrs x aq attrs), sc_pat_opt
            in
            aux (aq@aqs) env (b::bs) sc_pat_opt rest
       in
       aux [] env [] None binders

    | App (_, _, UnivApp) ->
       let rec aux universes e = match (unparen e).tm with
           | App(e, t, UnivApp) ->
               let univ_arg = desugar_universe t in
               aux (univ_arg::universes) e
            | _ ->
                let head, aq = desugar_term_aq env e in
                mk (Tm_uinst(head, universes)), aq
       in aux [] top

    | App (e, t, imp) ->
      let head, aq1 = desugar_term_aq env e in
      let t, aq2 = desugar_term_aq env t in
      let arg = arg_withimp_t imp t in
      S.extend_app head arg top.range, aq1@aq2

    | Bind(x, t1, t2) ->
      let xpat = AST.mk_pattern (AST.PatVar(x, None, [])) (range_of_id x) in
      let k = AST.mk_term (Abs([xpat], t2)) t2.range t2.level in
      let bind_lid = Ident.lid_of_path ["bind"] (range_of_id x) in
      let bind = AST.mk_term (AST.Var bind_lid) (range_of_id x) AST.Expr in
      desugar_term_aq env (AST.mkExplicitApp bind [t1; k] top.range)

    | Seq(t1, t2) ->
      //
      // let _ : unit = e1 in e2
      //
      let p = mk_pattern (PatWild (None, [])) t1.range in
      let p = mk_pattern (PatAscribed (p, (unit_ty p.prange, None))) p.prange in
      let t = mk_term (Let(NoLetQualifier, [None, (p, t1)], t2)) top.range Expr in
      let tm, s = desugar_term_aq env t in

      //
      // keep the Sequence, we will use it for resugaring
      //
      mk (Tm_meta {tm; meta=Meta_desugared Sequence}), s

    | LetOpen (lid, e) ->
      let env = Env.push_namespace env lid Unrestricted in
      (if Env.expect_typ env then desugar_typ_aq else desugar_term_aq) env e

    | LetOpenRecord (r, rty, e) ->
      let rec head_of (t:term) : term =
        match t.tm with
        | App (t, _, _) -> head_of t
        | _ -> t
      in
      let tycon = head_of rty in
      let tycon_name =
        match tycon.tm with
        | Var l -> l
        | _ ->
          raise_error rty Errors.Error_BadLetOpenRecord
            (BU.format1 "This type must be a (possibly applied) record name" (term_to_string rty))
      in
      let record =
        match Env.try_lookup_record_type env tycon_name with
        | Some r -> r
        | None ->
          raise_error rty Errors.Error_BadLetOpenRecord
            (BU.format1 "Not a record type: `%s`" (term_to_string rty))
      in
      let constrname = lid_of_ns_and_id (ns_of_lid record.typename) record.constrname in
      let mk_pattern p = mk_pattern p r.range in
      let elab =
        let pat =
          (* All of the fields are explicit arguments of the constructor, hence the None below *)
          mk_pattern (PatApp (mk_pattern (PatName constrname),
                              List.map (fun (field, _) -> mk_pattern (PatVar (field, None, []))) record.fields))
        in
        let branch = (pat, None, e) in
        let r = mk_term (Ascribed (r, rty, None, false)) r.range Expr in
        { top with tm = Match (r, None, None, [branch]) }
      in
      desugar_term_maybe_top top_level env elab

    | LetOperator(lets, body) ->
      ( match lets with
      | [] -> failwith "Impossible: a LetOperator (e.g. let+, let*...) cannot contain zero let binding"
      | (letOp, letPat, letDef)::tl ->
        let term_of_op op = AST.mk_term (AST.Op (op, [])) (range_of_id op) AST.Expr in
        let mproduct_def = fold_left (fun def (andOp, andPat, andDef) ->
            AST.mkExplicitApp
              (term_of_op andOp)
              [def; andDef] top.range
        ) letDef tl in
        let mproduct_pat = fold_left (fun pat (andOp, andPat, andDef) ->
            AST.mk_pattern (AST.PatTuple ([pat; andPat], false)) andPat.prange
        ) letPat tl in
        let fn = AST.mk_term (Abs([hoist_pat_ascription mproduct_pat], body)) body.range body.level in
        let let_op = term_of_op letOp in
        let t = AST.mkExplicitApp let_op [mproduct_def; fn] top.range in
        desugar_term_aq env t
      )
    | Let(qual, lbs, body) ->
      let is_rec = qual = Rec in
      let ds_let_rec_or_app () =
        let bindings = lbs in
        let funs = bindings |> List.map (fun (attr_opt, (p, def)) ->
          if is_app_pattern p
          then attr_opt, destruct_app_pattern env top_level p, def
          else match un_function p def with
                | Some (p, def) -> attr_opt, destruct_app_pattern env top_level p, def
                | _ -> begin match p.pat with
                        | PatAscribed({pat=PatVar(id,_,_)}, t) ->
                            if top_level
                            then attr_opt, (Inr (qualify env id), [], Some t), def
                            else attr_opt, (Inl id, [], Some t), def
                        | PatVar(id, _, _) ->
                            if top_level
                            then attr_opt, (Inr (qualify env id), [], None), def
                            else attr_opt, (Inl id, [], None), def
                        | _ -> raise_error p Errors.Fatal_UnexpectedLetBinding "Unexpected let binding"
                      end)
        in

        //Generate fresh names and populate an env' with recursive bindings
        //below, we use env' instead of env, only if is_rec
        let env', fnames, rec_bindings, used_markers =
          List.fold_left (fun (env, fnames, rec_bindings, used_markers) (_attr_opt, (f, _, _), _) ->
            let env, lbname, rec_bindings, used_markers = match f with
              | Inl x ->
                let env, xx, used_marker = push_bv' env x in
                let dummy_ref = BU.mk_ref true in
                env, Inl xx, S.mk_binder xx::rec_bindings, used_marker::used_markers
              | Inr l ->
                let env, used_marker = push_top_level_rec_binding env (ident_of_lid l) in
                env, Inr l, rec_bindings, used_marker::used_markers in
            env, (lbname::fnames), rec_bindings, used_markers) (env, [], [], []) funs
        in

        let fnames = List.rev fnames in
        let rec_bindings = List.rev rec_bindings in
        let used_markers = List.rev used_markers in
        (* This comment is taken from Syntax.Subst.open_let_rec
           The desugaring of let recs has to be consistent with their opening

            Consider
                let rec f<u> x = g x
                and g<u'> y = f y in
                f 0, g 0
            In de Bruijn notation, this is
                let rec f x = g@1 x@0
                and g y = f@2 y@0 in
                f@1 0, g@0 0
            i.e., the recursive environment for f is, in order:
                        u, f, g, x
                  for g is
                        u, f, g, y
                  and for the body is
                        f, g
         *)
        let desugar_one_def env lbname (attrs_opt, (_, args, result_t), def)
            : letbinding & antiquotations_temp
            =
            let args = args |> List.map replace_unit_pattern in
            let pos = def.range in
            let def =
              match result_t with
              | None -> def
              | Some (t, tacopt) ->
                let t =
                    if is_comp_type env t
                    then let _ =
                            match args |> List.tryFind (fun x -> not (is_var_pattern x)) with
                            | None -> ()
                            | Some p ->
                              raise_error p Errors.Fatal_ComputationTypeNotAllowed
                                ("Computation type annotations are only permitted on let-bindings \
                                             without inlined patterns; \
                                             replace this pattern with a variable") in
                         t
                    else if Options.ml_ish () //we're type-checking the compiler itself, e.g.
                    && Option.isSome (Env.try_lookup_effect_name env (C.effect_ML_lid())) //ML is in scope (not still in prims, e.g)
                    && (not is_rec || List.length args <> 0) //and we don't have something like `let rec f : t -> t' = fun x -> e`
                    then AST.ml_comp t
                    else AST.tot_comp t
                in
                mk_term (Ascribed(def, t, tacopt, false)) def.range Expr
            in
            let def = match args with
                 | [] -> def
                 | _ -> mk_term (un_curry_abs args def) top.range top.level in
            let body, aq = desugar_term_aq env def in
            let lbname = match lbname with
                | Inl x -> Inl x
                | Inr l -> Inr (S.lid_and_dd_as_fv l None) in
            let body = if is_rec then Subst.close rec_bindings body else body in
            let attrs = match attrs_opt with
              | None -> []
              | Some l -> List.map (desugar_term env) l
            in
            mk_lb (attrs, lbname, setpos tun, body, pos), aq
        in
        let lbs, aqss =
            List.map2 (desugar_one_def (if is_rec then env' else env)) fnames funs
            |> List.unzip
        in
        let body, aq = desugar_term_aq env' body in
        if is_rec then begin
          List.iter2 (fun (_attr_opt, (f, _, _), _) used_marker ->
            if not !used_marker then
              let nm, gl, rng =
                match f with
                | Inl x -> (string_of_id x, "Local binding", range_of_id x)
                | Inr l -> (string_of_lid l, "Global binding", range_of_lid l)
              in
              let open FStarC.Errors.Msg in
              let open FStarC.Pprint in
              Errors.log_issue rng Errors.Warning_UnusedLetRec [
                surround 4 1 (text gl)
                             (squotes (doc_of_string nm))
                             (text "is recursive but not used in its body")
              ]
            ) funs used_markers
        end;
        mk <| (Tm_let {lbs=(is_rec, lbs); body=Subst.close rec_bindings body}), aq @ List.flatten aqss
      in
      //end ds_let_rec_or_app

      let ds_non_rec attrs_opt pat t1 t2 =
        let attrs =
            match attrs_opt with
            | None -> []
            | Some l -> List.map (desugar_term env) l
        in
        let t1, aq0 = desugar_term_aq env t1 in
        let (env, binder, pat), aqs = desugar_binding_pat_maybe_top top_level env pat in
        check_no_aq aqs;
        let tm, aq1 =
         match binder with
         | LetBinder(l, (t, tacopt)) ->
           if tacopt |> is_some
           then Errors.log_issue (tacopt |> must) Errors.Warning_DefinitionNotTranslated
                  "Tactic annotation with a value type is not supported yet, \
                    try annotating with a computation type; this tactic annotation will be ignored";
           let body, aq = desugar_term_aq env t2 in
           let fv = S.lid_and_dd_as_fv l None in
           mk <| Tm_let {lbs=(false, [mk_lb (attrs, Inr fv, t, t1, t1.pos)]); body}, aq

         | LocalBinder (x,_,_) ->
           // TODO unsure if keep _ or [] on second comp below
           let body, aq = desugar_term_aq env t2 in
           let body = match pat with
             | [] -> body
             | _ ->
               S.mk (Tm_match {scrutinee=S.bv_to_name x;
                               ret_opt=None;
                               brs=desugar_disjunctive_pattern pat None body;
                               rc_opt=None}) top.range
           in
           mk <| Tm_let {lbs=(false, [mk_lb (attrs, Inl x, x.sort, t1, t1.pos)]);
                         body=Subst.close [S.mk_binder x] body}, aq
        in
        tm, aq0 @ aq1
      in

      let attrs, (head_pat, defn) = List.hd lbs in
      if is_rec
      || is_app_pattern head_pat
      then ds_let_rec_or_app()
      else ds_non_rec attrs head_pat defn body

    | If(e, Some op, asc_opt, t2, t3) ->
      // A if operator is desugared into a let operator binding
      // with name "uu___if_op_head" followed by a regular if on
      // "uu___if_op_head"
      let var_id = mk_ident(reserved_prefix ^ "if_op_head", e.range) in
      let var = mk_term (Var (lid_of_ids [var_id])) e.range Expr in
      let pat = mk_pattern (PatVar (var_id, None, [])) e.range in
      let if_ = mk_term (If (var, None, asc_opt, t2, t3)) top.range Expr in
      let t   = mk_term (LetOperator ([(op, pat, e)], if_)) e.range Expr in
      desugar_term_aq env t

    | If(t1, None, asc_opt, t2, t3) ->
      let x = Syntax.new_bv (Some t3.range) (tun_r t3.range) in
      let t_bool = mk (Tm_fvar(S.lid_and_dd_as_fv C.bool_lid None)) in
      let t1', aq1 = desugar_term_aq env t1 in
      let t1' = U.ascribe t1' (Inl t_bool, None, false) in
      let asc_opt, aq0 = desugar_match_returns env t1' asc_opt in
      let t2', aq2 = desugar_term_aq env t2 in
      let t3', aq3 = desugar_term_aq env t3 in
      mk (Tm_match {scrutinee=t1';
                    ret_opt=asc_opt;
                    brs=[(withinfo (Pat_constant (Const_bool true)) t1.range, None, t2');
                         (withinfo (Pat_var x) t1.range, None, t3')];
                    rc_opt=None}), join_aqs [aq1;aq0;aq2;aq3]

    | TryWith(e, branches) ->
      let r = top.range in
      let handler = mk_function branches r r in
      let body = mk_function [(mk_pattern (PatConst Const_unit) r, None, e)] r r in
      let try_with_lid = Ident.lid_of_path ["try_with"] r in
      let try_with = AST.mk_term (AST.Var try_with_lid) r AST.Expr in
      let a1 = mk_term (App(try_with, body, Nothing)) r top.level in
      let a2 = mk_term (App(a1, handler, Nothing)) r top.level in
      desugar_term_aq env a2

    | Match(e, Some op, topt, branches) ->
      // A match operator is desugared into a let operator binding
      // with name "uu___match_op_head" followed by a regular match on
      // "uu___match_op_head"
      let var_id = mk_ident(reserved_prefix ^ "match_op_head", e.range) in
      let var = mk_term (Var (lid_of_ids [var_id])) e.range Expr in
      let pat = mk_pattern (PatVar (var_id, None, [])) e.range in
      let mt  = mk_term (Match (var, None, topt, branches)) top.range Expr in
      let t   = mk_term (LetOperator ([(op, pat, e)], mt)) e.range Expr in
      desugar_term_aq env t
    | Match(e, None, topt, branches) ->
      let desugar_branch (pat, wopt, b) =
        let (env, pat), aqP = desugar_match_pat env pat in
        let wopt = match wopt with
          | None -> None
          | Some e -> Some (desugar_term env e)
        in
        let b, aqB = desugar_term_aq env b in
        desugar_disjunctive_pattern pat wopt b, aqP@aqB
      in
      let e, aq = desugar_term_aq env e in
      let asc_opt, aq0 = desugar_match_returns env e topt in
      let brs, aqs = List.map desugar_branch branches |> List.unzip |> (fun (x, y) -> (List.flatten x, y)) in
      mk <| Tm_match {scrutinee=e;ret_opt=asc_opt;brs;rc_opt=None}, join_aqs (aq::aq0::aqs)

    | Ascribed(e, t, tac_opt, use_eq) ->
      let asc, aq0 = desugar_ascription env t tac_opt use_eq in
      let e, aq = desugar_term_aq env e in
      mk <| Tm_ascribed {tm=e; asc; eff_opt=None}, aq0@aq

    | Record(_, []) ->
      raise_error top Errors.Fatal_UnexpectedEmptyRecord "Unexpected empty record"

    | Record(eopt, fields) ->
      (* Record literals have to wait for type information to be fully resolved *)
      let record_opt =
        let (f, _) = List.hd fields in
        try_lookup_record_by_field_name env f
      in
      let fields, aqs =
          List.map
              (fun (fn, fval) ->
                let fval, aq = desugar_term_aq env fval in
                (fn, fval), aq)
              fields
          |> List.unzip
      in
      (* Note, we have to unzip the fields and maintain the field
         names in the qualifier and the field assignments in the term.

         This is because the qualifiers intentionally are not meant to
         contain terms (only lidents, fv etc.).

         If they did contain terms, then we'd have to substitute in
         them, close, open etc. which I wanted to avoid.
      *)
      let field_names, assignments = List.unzip fields in
      let args = List.map (fun f -> f, None) assignments in
      let aqs = List.flatten aqs in
      let uc =
        match record_opt with
        | None ->
          { uc_base_term = Option.isSome eopt;
            uc_typename = None;
            uc_fields = field_names }
        | Some record ->
          { uc_base_term = Option.isSome eopt;
            uc_typename = Some record.typename;
            uc_fields = qualify_field_names record.typename field_names }
      in
      let head =
          let lid = lid_of_path ["__dummy__"] top.range in
          S.fvar_with_dd lid
                 (Some (Unresolved_constructor uc))
      in
      let mk_result args = S.mk_Tm_app head args top.range in
      begin
      match eopt with
      | None -> mk_result args, aqs
      | Some e ->
        let e, aq = desugar_term_aq env e in
        let tm =
          match (SS.compress e).n with
          | Tm_name _
          | Tm_fvar _ ->
            //no need to hoist
            mk_result ((e, None)::args)
          | _ ->
            (* If the base term is not a name, we hoist it *)
            let x = FStarC.Ident.gen e.pos in
            let env', bv_x = push_bv env x in
            let nm = S.bv_to_name bv_x in
            let body = mk_result ((nm, None)::args) in
            let body = SS.close [S.mk_binder bv_x] body in
            let lb = mk_lb ([], Inl bv_x, S.tun, e, e.pos) in
            mk (Tm_let {lbs=(false, [lb]); body})
        in
        tm,
        aq@aqs
      end

    | Project(e, f) ->
      (* Projections have to wait for type information to be fully resolved *)
      let e, s = desugar_term_aq env e in
      let head =
        match try_lookup_dc_by_field_name env f with
        | None ->
          S.fvar_with_dd f (Some (Unresolved_projector None))

        | Some (constrname, is_rec) ->
          let projname = mk_field_projector_name_from_ident constrname (ident_of_lid f) in
          let qual = if is_rec then Some (Record_projector (constrname, ident_of_lid f)) else None in
          let candidate_projector = S.lid_and_dd_as_fv (Ident.set_lid_range projname top.range) qual in
          let qual = Unresolved_projector (Some candidate_projector) in
          let f = List.hd (qualify_field_names constrname [f]) in
          S.fvar_with_dd f (Some qual)
      in
      //The fvar at the head of the term just records the fieldname that the user wrote
      //and in TcTerm, we use that field name combined with type info to disambiguate
      mk <| Tm_app {hd=head; args=[as_arg e]}, s

    | NamedTyp(n, e) ->
      (* See issue #1905 *)
      log_issue n Warning_IgnoredBinding "This name is being ignored";
      desugar_term_aq env e

    | Paren e -> failwith "impossible"

    | VQuote e ->
      { U.exp_string (desugar_vquote env e top.range) with pos = e.range }, noaqs

    | Quote (e, Static) ->
      let tm, vts = desugar_term_aq env e in
      let vt_binders = List.map (fun (bv, _tm) -> S.mk_binder bv) vts in
      let vt_tms = List.map snd vts in // not closing these, they are already well-scoped
      let tm = SS.close vt_binders tm in // but we need to close the variables in tm
      let () =
        let fvs = Free.names tm in
        if not (is_empty fvs) then
          raise_error e Errors.Fatal_MissingFieldInRecord
                     (BU.format1 "Static quotation refers to external variables: %s" (show fvs))
      in

      let qi = { qkind = Quote_static; antiquotations = (0, vt_tms) } in
      mk <| Tm_quoted (tm, qi), noaqs

    | Antiquote e ->
      let bv = S.new_bv (Some e.range) S.tun in
      (* We use desugar_term, so there can be double antiquotations *)
      let tm = desugar_term env e in
      S.bv_to_name bv, [(bv, tm)]

    | Quote (e, Dynamic) ->
      let qi = { qkind = Quote_dynamic
               ; antiquotations = (0, [])
               } in
      mk <| Tm_quoted (desugar_term env e, qi), noaqs

    | CalcProof (rel, init_expr, steps) ->
      (* We elaborate it into surface syntax and recursively desugar it *)

      let is_impl (rel:term) : bool =
        let is_impl_t (t:S.term) : bool =
          match t.n with
          | Tm_fvar fv -> S.fv_eq_lid fv C.imp_lid
          | _ -> false
        in
        match (unparen rel).tm with
        | Op (id, _) ->
            begin match op_as_term env 2 id with
            | Some t -> is_impl_t t
            | None -> false
            end

        | Var lid ->
            begin match desugar_name' (fun x->x) env true lid with
            | Some t -> is_impl_t t
            | None -> false
            end
        | Tvar id ->
        (* GM: This case does not seem exercised even if the user writes "l_imp"
         * as the relation... I thought those are meant to be Tvar nodes but
         * it ends up as a Var. Bug? *)
            begin match try_lookup_id env id with
            | Some t -> is_impl_t t
            | None -> false
            end
        | _ -> false
      in

      (* Annoying: (<) is not a preorder since it has type
       * `int -> int -> Tot bool`, and it's not subtyped to
       * `int -> int -> Tot Type0`, so we eta-expand and annotate
       * to make it kick in. *)
      let eta_and_annot rel =
        let x = Ident.gen' "x" rel.range in
        let y = Ident.gen' "y" rel.range in
        let xt = mk_term (Tvar x) rel.range Expr in
        let yt = mk_term (Tvar y) rel.range Expr in
        let pats = [mk_pattern (PatVar (x, None, [])) rel.range; mk_pattern (PatVar (y, None,[])) rel.range] in
        mk_term (Abs (pats,
            mk_term (Ascribed (
                mkApp rel [(xt, Nothing); (yt, Nothing)] rel.range,
                mk_term (Name (Ident.lid_of_str "Type0")) rel.range Expr,
                None, false)) rel.range Expr)) rel.range Expr
      in
      let rel = eta_and_annot rel in

      let wild r = mk_term Wild r Expr in
      let init   = mk_term (Var C.calc_init_lid) init_expr.range Expr in
      let push_impl r = mk_term (Var C.calc_push_impl_lid) r Expr in
      let last_expr = match List.last_opt steps with
                      | Some (CalcStep (_, _, last_expr)) -> last_expr
                      | None -> init_expr
      in
      let step r = mk_term (Var C.calc_step_lid) r Expr in
      let finish = mkApp (mk_term (Var C.calc_finish_lid) top.range Expr) [(rel, Nothing)] top.range in

      let e = mkApp init [(init_expr, Nothing)] init_expr.range in
      let (e, _) = List.fold_left (fun (e, prev) (CalcStep (rel, just, next_expr)) ->
                          let just =
                            if is_impl rel
                            then mkApp (push_impl just.range) [(thunk just, Nothing)] just.range
                            else just
                          in
                          let pf = mkApp (step rel.range)
                                          [(wild rel.range, Hash);
                                           (init_expr, Hash);
                                           (prev, Hash);
                                           (eta_and_annot rel, Nothing); (next_expr, Nothing);
                                           (thunk e, Nothing); (thunk just, Nothing)]
                                           Range.dummyRange // GM: using any other range here
                                                            // seems to make things worse,
                                                            // see test_1763 in
                                                            // tests/error-messages/Calc.fst.
                                                            // A mistery for some later day.
                          in
                          (pf, next_expr))
                   (e, init_expr) steps in
      let e = mkApp finish [(init_expr, Hash); (last_expr, Hash); (thunk e, Nothing)] top.range in
      desugar_term_maybe_top top_level env e

    | IntroForall (bs, p, e) ->
      let env', bs = desugar_binders env bs in
      let p = desugar_term env' p in
      let e = desugar_term env' e in
      (*
         forall_intro a0 (fun x0 -> forall xs. p) (fun x0 ->
         forall_intro a1 (fun x1 -> forall xs. p) (fun x1 ->
         ...
         forall_intro an (fun xn -> p) (fun xn -> e)))
       *)
      let mk_forall_intro t p pf =
        let head = S.fv_to_tm (S.lid_and_dd_as_fv C.forall_intro_lid None) in
        let args = [(t, None);
                    (p, None);
                    (pf, None)] in
        S.mk_Tm_app head args top.range
      in
      let rec aux bs =
        match bs with
        | [] ->
          let sq_p = U.mk_squash U_unknown p in
          U.ascribe e (Inl sq_p, None, false)

        | b::bs ->
          let tail = aux bs in
          let x = unqual_bv_of_binder b in
          mk_forall_intro
            x.sort
            (U.abs [b] (U.close_forall_no_univs bs p) None)
            (U.abs [b] tail None)
      in
      aux bs, noaqs

    | IntroExists (bs, p, vs, e) ->
      let env', bs = desugar_binders env bs in
      let p = desugar_term env' p in
      let vs = List.map (desugar_term env) vs in
      let e = desugar_term env e in
      (*
        (exists_intro a1 (fun x1 -> exists xs. p)
         (exists_intro a2 (fun x2 -> exists xs.p[v1/x1])
         ...
          (exists_intro an (fun xn -> p[vs/xs]) vn e)))

      *)
      let mk_exists_intro t p v e =
        let head = S.fv_to_tm (S.lid_and_dd_as_fv C.exists_intro_lid None) in
        let args = [(t, None);
                    (p, None);
                    (v, None);
                    (mk_thunk e, None)] in
        S.mk_Tm_app head args top.range
      in
      let rec aux bs vs sub token =
        match bs, vs with
        | [], [] -> token
        | b::bs, v::vs ->
          let x = unqual_bv_of_binder b in
          let token = aux (SS.subst_binders (NT(x, v)::sub) bs) vs (NT(x, v)::sub) token in
          let token =
            mk_exists_intro
              x.sort
              (U.abs [b] (close_exists_no_univs bs (SS.subst sub p)) None)
              v
              token
          in
          token
        | _ ->
          raise_error top Fatal_UnexpectedTerm "Unexpected number of instantiations in _intro_ exists"
       in
       aux bs vs [] e, noaqs

    | IntroImplies (p, q, x, e) ->
      let p = desugar_term env p in
      let q = desugar_term env q in
      let env', [x] = desugar_binders env [x] in
      let e = desugar_term env' e in
      let head = S.fv_to_tm (S.lid_and_dd_as_fv C.implies_intro_lid None) in
      let args = [(p, None);
                  (mk_thunk q, None);
                  (U.abs [x] e None, None)] in
      S.mk_Tm_app head args top.range, noaqs


    | IntroOr (lr, p, q, e) ->
      let p = desugar_term env p in
      let q = desugar_term env q in
      let e = desugar_term env e in
      let lid =
        if lr
        then C.or_intro_left_lid
        else C.or_intro_right_lid
      in
      let head = S.fv_to_tm (S.lid_and_dd_as_fv lid None) in
      let args = [(p, None);
                  (mk_thunk q, None);
                  (mk_thunk e, None)] in
      S.mk_Tm_app head args top.range, noaqs

    | IntroAnd (p, q, e1, e2) ->
      let p = desugar_term env p in
      let q = desugar_term env q in
      let e1 = desugar_term env e1 in
      let e2 = desugar_term env e2 in
      let head = S.fv_to_tm (S.lid_and_dd_as_fv C.and_intro_lid None) in
      let args = [(p, None);
                  (mk_thunk q, None);
                  (mk_thunk e1, None);
                  (mk_thunk e2, None)] in
      S.mk_Tm_app head args top.range, noaqs

    | ElimForall (bs, p, vs) ->
      let env', bs = desugar_binders env bs in
      let p = desugar_term env' p in
      let vs = List.map (desugar_term env) vs in
      (*
        (forall_elim #an #(fun xn -> p[vs/xs]) vn
        ...
         (forall_elim #a1 #(fun x1 -> forall xs. p[v0/x]) v1
          (forall_elim #a0 #(fun x0 -> forall xs. p) v0 ())))
      *)
      let mk_forall_elim a p v tok =
        let head = S.fv_to_tm (S.lid_and_dd_as_fv C.forall_elim_lid None) in
        let args = [(a, S.as_aqual_implicit true);
                    (p, S.as_aqual_implicit true);
                    (v, None);
                    (tok, None)] in
        S.mk_Tm_app head args tok.pos
      in
      let rec aux bs vs sub token : S.term =
        match bs, vs with
        | [], [] -> token
        | b::bs, v::vs ->
          let x = unqual_bv_of_binder b in
          let token =
            mk_forall_elim
              x.sort
              (U.abs [b] (U.close_forall_no_univs bs (SS.subst sub p)) None)
              v
              token
          in
          let sub = NT(x, v)::sub in
          aux (SS.subst_binders sub bs) vs sub token
        | _ ->
          raise_error top Fatal_UnexpectedTerm "Unexpected number of instantiations in _elim_forall_"
      in
      let range = List.fold_right (fun bs r -> Range.union_ranges (S.range_of_bv bs.binder_bv) r) bs p.pos in
      aux bs vs [] { U.exp_unit with pos = range }, noaqs

    | ElimExists (binders, p, q, binder, e) -> (
      let env', bs = desugar_binders env binders in
      let p = desugar_term env' p in
      let q = desugar_term env q in
      let sq_q = U.mk_squash U_unknown q in
      let env'', [b_pf_p] = desugar_binders env' [binder] in
      let e = desugar_term env'' e in
      let rec mk_exists bs p =
        match bs with
        | [] -> failwith "Impossible"
        | [b] ->
          let x = b.binder_bv in
          let head = S.fv_to_tm (S.lid_and_dd_as_fv C.exists_lid None) in
          let args = [(x.sort, S.as_aqual_implicit true);
                      (U.abs [List.hd bs] p None, None)] in
          S.mk_Tm_app head args p.pos
        | b::bs ->
          let body = mk_exists bs p in
          mk_exists [b] body
      in
      let mk_exists_elim t x_p s_ex_p f r =
        let head = S.fv_to_tm (S.lid_and_dd_as_fv C.exists_elim_lid None) in
        let args = [(t, S.as_aqual_implicit true);
                    (x_p, S.as_aqual_implicit true);
                    (s_ex_p, None);
                    (f, None)] in
        mk_Tm_app head args r
      in
      let rec aux binders squash_token =
        match binders with
        | [] -> raise_error top Fatal_UnexpectedTerm "Empty binders in ELIM_EXISTS"
        | [b] ->
          let x = unqual_bv_of_binder b in
          (*
               exists_elim
                  #(x.sort)
                  #(fun b -> p)
                  squash_token
                  (fun b pf_p -> e)
          *)
          mk_exists_elim
              x.sort
              (U.abs [b] p None)
              squash_token
              (U.abs [b;b_pf_p] (U.ascribe e (Inl sq_q, None, false)) None)
              squash_token.pos

        | b::bs ->
          let pf_i =
            S.gen_bv "pf"
              (Some (range_of_bv b.binder_bv))
              S.tun
          in
          let k = aux bs (S.bv_to_name pf_i) in
          let x = unqual_bv_of_binder b in
          (*
             exists_elim
               #(x.sort)
               #(fun b -> exists bs. p)
               squash_token
               (fun b pf_i -> k)
          *)
          mk_exists_elim
            x.sort
            (U.abs [b] (mk_exists bs p) None)
            squash_token
            (U.abs [b; S.mk_binder pf_i] k None)
            squash_token.pos
      in
      let range = List.fold_right (fun bs r -> Range.union_ranges (S.range_of_bv bs.binder_bv) r) bs p.pos in
      aux bs { U.exp_unit with pos = range }, noaqs
      )

    | ElimImplies (p, q, e) ->
      let p = desugar_term env p in
      let q = desugar_term env q in
      let e = desugar_term env e in
      let head = S.fv_to_tm (S.lid_and_dd_as_fv C.implies_elim_lid None) in
      let args = [(p, None);
                  (q, None);
                  ({ U.exp_unit with pos = Range.union_ranges p.pos q.pos }, None);
                  (mk_thunk e, None)] in
      mk_Tm_app head args top.range, noaqs

    | ElimOr(p, q, r, x, e1, y, e2) ->
      let p = desugar_term env p in
      let q = desugar_term env q in
      let r = desugar_term env r in
      let env_x, [x] = desugar_binders env [x] in
      let e1 = desugar_term env_x e1 in
      let env_y, [y] = desugar_binders env [y] in
      let e2 = desugar_term env_y e2 in
      let head = S.fv_to_tm (S.lid_and_dd_as_fv C.or_elim_lid None) in
      let extra_binder = S.mk_binder (S.new_bv None S.tun) in
      let args = [(p, None);
                  (mk_thunk q, None);
                  (r, None);
                  ({ U.exp_unit with pos = Range.union_ranges p.pos q.pos }, None);
                  (U.abs [x] e1 None, None);
                  (U.abs [extra_binder; y] e2 None, None)] in
      mk_Tm_app head args top.range, noaqs

    | ElimAnd(p, q, r, x, y, e) ->
      let p = desugar_term env p in
      let q = desugar_term env q in
      let r = desugar_term env r in
      let env', [x;y] = desugar_binders env [x;y] in
      let e = desugar_term env' e in
      let head = S.fv_to_tm (S.lid_and_dd_as_fv C.and_elim_lid None) in
      let args = [(p, None);
                  (mk_thunk q, None);
                  (r, None);
                  ({ U.exp_unit with pos = Range.union_ranges p.pos q.pos }, None);
                  (U.abs [x;y] e None, None)] in
      mk_Tm_app head args top.range, noaqs

    | ListLiteral ts ->
      let nil r = mk_term (Construct (C.nil_lid, [])) r Expr in
      let cons r hd tl= mk_term (Construct (C.cons_lid, [ (hd, Nothing); (tl, Nothing)])) r Expr in
      let t' = List.fold_right (cons top.range) ts (nil top.range) in
      desugar_term_aq env t'

    | SeqLiteral ts ->
      let nil r = mk_term (Var C.seq_empty_lid) r Expr in
      let cons r hd tl = mkApp (mk_term (Var C.seq_cons_lid) r Expr) [ (hd, Nothing); (tl, Nothing)] r in
      let t' = List.fold_right (cons top.range) ts (nil top.range) in
      desugar_term_aq env t'

    | _ when (top.level=Formula) -> desugar_formula env top, noaqs

    | _ ->
      raise_error top Fatal_UnexpectedTerm ("Unexpected term: " ^ term_to_string top)
  end

and desugar_match_returns env scrutinee asc_opt =
  match asc_opt with
  | None -> None, []
  | Some asc ->
    let asc_b, asc_tc, asc_use_eq = asc in
    let env_asc, b =
      match asc_b with
      | None ->
        //no binder is specified, generate a fresh one
        let bv = S.gen_bv C.match_returns_def_name (Some scrutinee.pos) S.tun in
        env, S.mk_binder bv
      | Some b ->
        let env, bv = Env.push_bv env b in
        env, S.mk_binder bv in
    let asc, aq = desugar_ascription env_asc asc_tc None asc_use_eq in
    //if scrutinee is a name, it may appear in the ascription
    //  substitute it with the (new or annotated) binder
    let asc =
      match (scrutinee |> U.unascribe).n with
      | Tm_name sbv -> SS.subst_ascription [NT (sbv, S.bv_to_name b.binder_bv)] asc
      | _ -> asc in
    let asc = SS.close_ascription [b] asc in
    let b = List.hd (SS.close_binders [b]) in
    Some (b, asc), aq

and desugar_ascription env t tac_opt use_eq : S.ascription & antiquotations_temp =
  let annot, aq0 =
    if is_comp_type env t
    then if use_eq
         then raise_error t Errors.Fatal_NotSupported "Equality ascription with computation types is not supported yet"
         else let comp = desugar_comp t.range true env t in
              (Inr comp, [])
    else let tm, aq = desugar_term_aq env t in
         (Inl tm, aq) in
  (annot, BU.map_opt tac_opt (desugar_term env), use_eq), aq0

and desugar_args env args =
    args |> List.map (fun (a, imp) -> arg_withimp_t imp (desugar_term env a))

and desugar_comp r (allow_type_promotion:bool) env t =
    let fail #a code msg : a= raise_error r code msg in
    let is_requires (t, _) = match (unparen t).tm with
      | Requires _ -> true
      | _ -> false
    in
    let is_ensures (t, _) = match (unparen t).tm with
      | Ensures _ -> true
      | _ -> false
    in
    let is_decreases (t, _) = match (unparen t).tm with
      | Decreases _ -> true
      | _ -> false
    in
    let is_smt_pat1 (t:term) : bool =
      match (unparen t).tm with
      // TODO: remove this first match once we fully migrate
      | Construct (smtpat, _) ->
        BU.for_some (fun s -> (string_of_lid smtpat) = s)
          (* the smt pattern does not seem to be disambiguated yet at this point *)
          ["SMTPat"; "SMTPatT"; "SMTPatOr"]
          (* [C.smtpat_lid ; C.smtpatT_lid ; C.smtpatOr_lid] *)

      | Var smtpat ->
        BU.for_some (fun s -> (string_of_lid smtpat) = s)
          (* the smt pattern does not seem to be disambiguated yet at this point *)
          ["smt_pat" ; "smt_pat_or"]
          (* [C.smtpat_lid ; C.smtpatT_lid ; C.smtpatOr_lid] *)

      | _ -> false
    in
    let is_smt_pat (t,_) : bool =
      match (unparen t).tm with
      | ListLiteral ts -> BU.for_all is_smt_pat1 ts
      | _ -> false
    in
    let pre_process_comp_typ (t:AST.term) =
      let head, args = head_and_args t in
      match head.tm with
      | Name lemma when ((string_of_id (ident_of_lid lemma)) = "Lemma") ->
        (* need to add the unit result type and the empty smt_pat list, if n *)
        let unit_tm = mk_term (Name C.unit_lid) t.range Type_level, Nothing in
        let nil_pat = mk_term (Name C.nil_lid) t.range Expr, Nothing in
        let req_true =
          let req = Requires (mk_term (Name C.true_lid) t.range Formula, None) in
          mk_term req t.range Type_level, Nothing
        in
        (* The postcondition for Lemma is thunked, to allow to assume the precondition
         * (c.f. #57), so add the thunking here *)
        let thunk_ens (e, i) = (thunk e, i) in
        let fail_lemma () =
             let open FStarC.Pprint in
             let expected_one_of = ["Lemma post";
                                    "Lemma (ensures post)";
                                    "Lemma (requires pre) (ensures post)";
                                    "Lemma post [SMTPat ...]";
                                    "Lemma (ensures post) [SMTPat ...]";
                                    "Lemma (ensures post) (decreases d)";
                                    "Lemma (ensures post) (decreases d) [SMTPat ...]";
                                    "Lemma (requires pre) (ensures post) (decreases d)";
                                    "Lemma (requires pre) (ensures post) [SMTPat ...]";
                                    "Lemma (requires pre) (ensures post) (decreases d) [SMTPat ...]"] in
             raise_error t Errors.Fatal_InvalidLemmaArgument [
                text "Invalid arguments to 'Lemma'; expected one of the following"
                  ^^ sublist empty (List.map doc_of_string expected_one_of)
             ]
        in
        let args = match args with
          | [] -> fail_lemma ()

          | [req] //a single requires clause (cf. Issue #1208)
               when is_requires req ->
            fail_lemma()

          | [smtpat]
                when is_smt_pat smtpat ->
            fail_lemma()

          | [dec]
                when is_decreases dec ->
            fail_lemma()

          | [ens] -> //otherwise, a single argument is always treated as just an ensures clause
            [unit_tm;req_true;thunk_ens ens;nil_pat]

          | [req;ens]
                when is_requires req
                  && is_ensures ens ->
            [unit_tm;req;thunk_ens ens;nil_pat]

          | [ens;smtpat] //either Lemma p [SMTPat ...]; or Lemma (ensures p) [SMTPat ...]
                when not (is_requires ens)
                  && not (is_smt_pat ens)
                  && not (is_decreases ens)
                  && is_smt_pat smtpat ->
            [unit_tm;req_true;thunk_ens ens;smtpat]

          | [ens;dec]
                when is_ensures ens
                  && is_decreases dec ->
            [unit_tm;req_true;thunk_ens ens;nil_pat;dec]

          | [ens;dec;smtpat]
                when is_ensures ens
                  && is_decreases dec
                  && is_smt_pat smtpat ->
            [unit_tm;req_true;thunk_ens ens;smtpat;dec]

          | [req;ens;dec]
                when is_requires req
                  && is_ensures ens
                  && is_decreases dec ->
            [unit_tm;req;thunk_ens ens;nil_pat;dec]

          | [req;ens;smtpat]
                when is_requires req
                  && is_ensures ens
                  && is_smt_pat smtpat ->
            [unit_tm;req;thunk_ens ens;smtpat]

          | [req;ens;dec;smtpat]
                when is_requires req
                  && is_ensures ens
                  && is_smt_pat smtpat
                  && is_decreases dec ->
            [unit_tm;req;thunk_ens ens;dec;smtpat]

          | _other ->
            fail_lemma()
        in
        let head_and_attributes = fail_or env
          (Env.try_lookup_effect_name_and_attributes env)
          lemma in
        head_and_attributes, args

      | Name l when Env.is_effect_name env l ->
        (* we have an explicit effect annotation ... no need to add anything *)
        fail_or env (Env.try_lookup_effect_name_and_attributes env) l, args


      (* we're right at the beginning of Prims, when Tot isn't yet fully defined *)
      | Name l when (lid_equals (Env.current_module env) C.prims_lid
                          && (string_of_id (ident_of_lid l)) = "Tot") ->
        (* we have an explicit effect annotation ... no need to add anything *)
        (Ident.set_lid_range Const.effect_Tot_lid head.range,  []), args

      (* we're right at the beginning of Prims, when GTot isn't yet fully defined *)
      | Name l when (lid_equals (Env.current_module env) C.prims_lid
                          && (string_of_id (ident_of_lid l)) = "GTot") ->
        (* we have an explicit effect annotation ... no need to add anything *)
        (Ident.set_lid_range Const.effect_GTot_lid head.range, []), args

      | Name l when ((string_of_id (ident_of_lid l))="Type"
                      || (string_of_id (ident_of_lid l))="Type0"
                      || (string_of_id (ident_of_lid l))="Effect") ->
        (* the default effect for Type is always Tot *)
        (Ident.set_lid_range Const.effect_Tot_lid head.range, []), [t, Nothing]

      | _ when allow_type_promotion ->
        let default_effect =
          if Options.ml_ish ()
          then Const.effect_ML_lid()
          else (if Options.warn_default_effects()
                then FStarC.Errors.log_issue head Errors.Warning_UseDefaultEffect "Using default effect Tot";
                Const.effect_Tot_lid) in
        (Ident.set_lid_range default_effect head.range, []), [t, Nothing]

      | _ ->
        raise_error t Errors.Fatal_EffectNotFound "Expected an effect constructor"
    in
    let (eff, cattributes), args = pre_process_comp_typ t in
    if List.length args = 0 then
      fail Errors.Fatal_NotEnoughArgsToEffect (BU.format1 "Not enough args to effect %s" (show eff));
    let is_universe (_, imp) = imp = UnivApp in
    let universes, args = BU.take is_universe args in
    let universes = List.map (fun (u, imp) -> desugar_universe u) universes in
    let result_arg, rest = List.hd args, List.tl args in
    let result_typ = desugar_typ env (fst result_arg) in
    let dec, rest =
      let is_decrease t = match (unparen (fst t)).tm with
        | Decreases _ -> true
        | _ -> false
      in
      rest |> List.partition is_decrease
    in
    let rest = desugar_args env rest in
    let decreases_clause = dec |>
      List.map (fun t -> match (unparen (fst t)).tm with
                      | Decreases (t, _) ->
                        let dec_order =
                          let t = unparen t in
                          match t.tm with
                          | LexList l -> l |> List.map (desugar_term env) |> Decreases_lex
                          | WFOrder (t1, t2) -> (desugar_term env t1, desugar_term env t2) |> Decreases_wf
                          | _ -> [desugar_term env t] |> Decreases_lex in  //by-default a lex list of length 1
                        DECREASES dec_order
                      | _ ->
                        fail Errors.Fatal_UnexpectedComputationTypeForLetRec "Unexpected decreases clause") in

    let no_additional_args =
        (* F# complains about not being able to use = on some types.. *)
        let is_empty (l:list 'a) = match l with | [] -> true | _ -> false in
        is_empty decreases_clause &&
        is_empty rest &&
        is_empty cattributes &&
        is_empty universes
    in
    if no_additional_args
    && lid_equals eff C.effect_Tot_lid
    then mk_Total result_typ
    else if no_additional_args
         && lid_equals eff C.effect_GTot_lid
    then mk_GTotal result_typ
    else
      let flags =
        if      lid_equals eff C.effect_Lemma_lid then [LEMMA]
        else if lid_equals eff C.effect_Tot_lid   then [TOTAL]
        else if lid_equals eff (C.effect_ML_lid()) then [MLEFFECT]
        else if lid_equals eff C.effect_GTot_lid  then [SOMETRIVIAL]
        else []
      in
      let flags = flags @ cattributes in
      let rest =
        if lid_equals eff C.effect_Lemma_lid
        then
          match rest with
          | [req;ens;(pat, aq)] ->
            let pat = match pat.n with
              (* we really want the empty pattern to be in universe 0 rather than generalizing it *)
              | Tm_fvar fv when S.fv_eq_lid fv Const.nil_lid ->
                let nil = S.mk_Tm_uinst pat [U_zero] in
                let pattern =
                  S.fvar_with_dd (Ident.set_lid_range Const.pattern_lid pat.pos) None
                in
                S.mk_Tm_app nil [(pattern, S.as_aqual_implicit true)] pat.pos
              | _ -> pat
            in
            [req; ens; (S.mk (Tm_meta {tm=pat;meta=Meta_desugared Meta_smt_pat}) pat.pos, aq)]
          | _ -> rest
        else rest
      in
      mk_Comp ({comp_univs=universes;
                effect_name=eff;
                result_typ=result_typ;
                effect_args=rest;
                flags=flags@decreases_clause})

and desugar_formula env (f:term) : S.term =
  let mk t = S.mk t f.range in
  let setpos t = {t with pos=f.range} in
  let desugar_quant (q_head:S.term) b pats should_wrap_with_pat body =
    let tk = desugar_binder env ({b with blevel=Formula}) in
    let with_pats env (names, pats) body =
      match names, pats with
      | [], [] -> body
      | [], _::_ ->
        //violates an internal invariant
        failwith "Impossible: Annotated pattern without binders in scope"
      | _ ->
        let names =
          names |> List.map
          (fun i ->
          { fail_or2 (try_lookup_id env) i with pos=(range_of_id i) })
        in
        let pats =
          pats |> List.map
          (fun es -> es |> List.map
                  (fun e -> arg_withimp_t Nothing <| desugar_term env e))
        in
        match pats with
        | [] when not should_wrap_with_pat -> body
        | _ -> mk (Tm_meta {tm=body;meta=Meta_pattern (names, pats)})
    in
    match tk with
      | Some a, k, _ ->  //AR: ignoring the attributes here
        let env, a = push_bv env a in
        let a = {a with sort=k} in
        let body = desugar_formula env body in
        let body = with_pats env pats body in
        let body = setpos <| no_annot_abs [S.mk_binder a] body in
        mk <| Tm_app {hd=q_head;
                      args=[as_arg body]}

      | _ -> failwith "impossible" in

 let push_quant
      (q:(list AST.binder & AST.patterns & AST.term) -> AST.term')
      (binders:list AST.binder)
      pats (body:term) =
    match binders with
    | b::(b'::_rest) ->
      let rest = b'::_rest in
      let body = mk_term (q(rest, pats, body)) (Range.union_ranges b'.brange body.range) Formula in
      mk_term (q([b], ([], []), body)) f.range Formula
    | _ -> failwith "impossible" in

  match (unparen f).tm with
    | Labeled(f, l, p) ->
      let f = desugar_formula env f in
      // GM: I don't think this case really happens?
      mk <| Tm_meta {tm=f; meta=Meta_labeled(Errors.Msg.mkmsg l, f.pos, p)}

    | QForall([], _, _)
    | QExists([], _, _)
    | QuantOp(_, [], _, _) -> failwith "Impossible: Quantifier without binders"

    | QForall((_1::_2::_3), pats, body) ->
      let binders = _1::_2::_3 in
      desugar_formula env (push_quant (fun x -> QForall x) binders pats body)

    | QExists((_1::_2::_3), pats, body) ->
      let binders = _1::_2::_3 in
      desugar_formula env (push_quant (fun x -> QExists x) binders pats body)

    | QuantOp(i, (_1::_2::_3), pats, body) ->
      let binders = _1::_2::_3 in
      desugar_formula env (push_quant (fun (x,y,z) -> QuantOp(i, x, y, z)) binders pats body)

    | QForall([b], pats, body) ->
      let q = C.forall_lid in
      let q_head = S.fvar_with_dd (set_lid_range q b.brange) None in
      desugar_quant q_head b pats true body

    | QExists([b], pats, body) ->
      let q = C.exists_lid in
      let q_head = S.fvar_with_dd (set_lid_range q b.brange) None in
      desugar_quant q_head b pats true body
    
    | QuantOp(i, [b], pats, body) ->
      let q_head =
        match op_as_term env 0 i with
        | None -> 
          raise_error i Errors.Fatal_VariableNotFound
                      (BU.format1 "quantifier operator %s not found" (Ident.string_of_id i))
        | Some t -> t
      in
      desugar_quant q_head b pats false body

    | Paren f -> failwith "impossible"

    | _ -> desugar_term env f

and desugar_binder_aq env b : (option ident & S.term & list S.attribute) & antiquotations_temp =
  let attrs = b.battributes |> List.map (desugar_term env) in
  match b.b with
   | TAnnotated(x, t)
   | Annotated(x, t) ->
     let ty, aqs = desugar_typ_aq env t in
     (Some x, ty, attrs), aqs

   | NoName t        ->
     let ty, aqs = desugar_typ_aq env t in
     (None, ty, attrs), aqs

   | TVariable x     -> 
    (Some x, mk (Tm_type U_unknown) (range_of_id x), attrs), []

   | Variable x      ->
    (Some x, tun_r (range_of_id x), attrs), []

and desugar_binder env b : option ident & S.term & list S.attribute =
  let r, aqs = desugar_binder_aq env b in
  check_no_aq aqs;
  r

and desugar_vquote env e r: string =
  (* Returns the string representation of the lid behind [e], fails if it is not an FV *)
  let tm = desugar_term env e in
  match (Subst.compress tm).n with
  | Tm_fvar fv -> string_of_lid (lid_of_fv fv)
  | _ -> raise_error r Fatal_UnexpectedTermVQuote ("VQuote, expected an fvar, got: " ^ show tm)

and as_binder env imp = function
  | (None, k, attrs) ->
    mk_binder_with_attrs (null_bv k) (trans_bqual env imp) attrs, env
  | (Some a, k, attrs) ->
    let env, a = Env.push_bv env a in
    (mk_binder_with_attrs ({a with sort=k}) (trans_bqual env imp) attrs), env

and trans_bqual env = function
  | Some AST.Implicit -> Some S.imp_tag
  | Some AST.Equality -> Some S.Equality
  | Some (AST.Meta t) ->
    Some (S.Meta (desugar_term env t))
  | Some (AST.TypeClassArg) ->
    let tcresolve = desugar_term env (mk_term (Var C.tcresolve_lid) Range.dummyRange Expr) in
    Some (S.Meta tcresolve)
  | None -> None

let typars_of_binders env bs : _ & binders =
    let env, tpars = List.fold_left (fun (env, out) b ->
        let tk = desugar_binder env ({b with blevel=Formula}) in  (* typars follow the same binding conventions as formulas *)
        match tk with
            | Some a, k, attrs ->
                let env, a = push_bv env a in
                let a = {a with sort=k} in
                env, (mk_binder_with_attrs a (trans_bqual env b.aqual) attrs)::out
            | _ -> raise_error b Errors.Fatal_UnexpectedBinder "Unexpected binder") (env, []) bs in
    env, List.rev tpars


let desugar_attributes (env:env_t) (cattributes:list term) : list cflag =
    let desugar_attribute t =
        match (unparen t).tm with
            | Var lid when string_of_lid lid = "cps" -> CPS
            | _ -> raise_error t Errors.Fatal_UnknownAttribute ("Unknown attribute " ^ term_to_string t)
    in List.map desugar_attribute cattributes

let binder_ident (b:binder) : option ident =
  match b.b with
  | TAnnotated (x, _)
  | Annotated (x, _)
  | TVariable x
  | Variable x -> Some x
  | NoName _ -> None

let binder_idents (bs:list binder) : list ident =
  List.collect (fun b -> FStarC.Common.list_of_option (binder_ident b)) bs


let mk_data_discriminators quals env datas attrs =
    let quals = quals |> List.filter (function
        | S.NoExtract
        | S.Private -> true
        | _ -> false)
    in
    let quals q = if not (Env.iface env)
                  || Env.admitted_iface env
                  then S.Assumption::q@quals
                  else q@quals
    in
    datas |> List.map (fun d ->
        let disc_name = U.mk_discriminator d in
        { sigel = Sig_declare_typ {lid=disc_name; us=[]; t=Syntax.tun};
          sigrng = range_of_lid disc_name;// FIXME: Isn't that range wrong?
          sigquals =  quals [(* S.Logic ; *) S.OnlyName ; S.Discriminator d];
          sigmeta = default_sigmeta;
          sigattrs = attrs;
          sigopts = None;
          sigopens_and_abbrevs = DsEnv.opens_and_abbrevs env
        })

let mk_indexed_projector_names iquals fvq attrs env lid (fields:list S.binder) =
    let p = range_of_lid lid in

    fields |> List.mapi (fun i fld ->
        let x = fld.binder_bv in
        let field_name = U.mk_field_projector_name lid x i in
        let only_decl =
            lid_equals C.prims_lid  (Env.current_module env)
            || fvq<>Data_ctor
            || U.has_attribute attrs C.no_auto_projectors_attr
        in
        let no_decl = Syntax.is_type x.sort in
        let quals q =
            if only_decl
            then S.Assumption::q
            else q
        in
        let quals =
            let iquals = iquals |> List.filter (function
                | S.NoExtract
                | S.Private -> true
                | _ -> false)
            in
            quals (OnlyName :: S.Projector(lid, x.ppname) :: iquals)
        in
        let decl = { sigel = Sig_declare_typ {lid=field_name; us=[]; t=Syntax.tun};
                     sigquals = quals;
                     sigrng = range_of_lid field_name;
                     sigmeta = default_sigmeta ;
                     sigattrs = attrs;
                     sigopts = None;
                     sigopens_and_abbrevs = opens_and_abbrevs env } in
        if only_decl
        then [decl] //only the signature
        else
            let lb = {
                lbname=Inr (S.lid_and_dd_as_fv field_name None);
                lbunivs=[];
                lbtyp=tun;
                lbeff=C.effect_Tot_lid;
                lbdef=tun;
                lbattrs=[];
                lbpos=Range.dummyRange;
            } in
            let impl = { sigel = Sig_let {lbs=(false, [lb]);
                                          lids=[lb.lbname |> right |> (fun fv -> fv.fv_name.v)]};
                         sigquals = quals;
                         sigrng = p;
                         sigmeta = default_sigmeta;
                         sigattrs = attrs;
                         sigopts = None;
                         sigopens_and_abbrevs = opens_and_abbrevs env
                        } in
            if no_decl then [impl] else [decl;impl]) |> List.flatten

let mk_data_projector_names iquals env se : list sigelt =
  match se.sigel with
  | _ when U.has_attribute se.sigattrs C.no_auto_projectors_decls_attr
        || U.has_attribute se.sigattrs C.meta_projectors_attr ->
    []
  | Sig_datacon {lid;t;num_ty_params=n} ->
    let formals, _ = U.arrow_formals t in
    begin match formals with
        | [] -> [] //no fields to project
        | _ ->
            let filter_records = function
                | RecordConstructor (_, fns) -> Some (Record_ctor(lid, fns))
                | _ -> None
            in
            let fv_qual =
                match BU.find_map se.sigquals filter_records with
                | None -> Data_ctor
                | Some q -> q
            in
            (* ignoring parameters *)
            let _, rest = BU.first_N n formals in
            mk_indexed_projector_names iquals fv_qual se.sigattrs env lid rest
    end

  | _ -> []

let mk_typ_abbrev env d lid uvs typars kopt t lids quals rng =
    (* fetch attributes here to support `deprecated`, just as for
     * TopLevelLet (see comment there) *)
    let attrs = U.deduplicate_terms (List.map (desugar_term env) d.attrs) in
    let val_attrs = Env.lookup_letbinding_quals_and_attrs env lid |> snd in
    let lb = {
        lbname=Inr (S.lid_and_dd_as_fv lid None);
        lbunivs=uvs;
        lbdef=no_annot_abs typars t;
        lbtyp=if is_some kopt then U.arrow typars (S.mk_Total (kopt |> must)) else tun;
        lbeff=C.effect_Tot_lid;
        lbattrs=[];
        lbpos=rng;
    } in
    { sigel = Sig_let {lbs=(false, [lb]); lids};
      sigquals = quals;
      sigrng = rng;
      sigmeta = default_sigmeta ;
      sigattrs = U.deduplicate_terms (val_attrs @ attrs);
      sigopts = None;
      sigopens_and_abbrevs = opens_and_abbrevs env
    }

let rec desugar_tycon env (d: AST.decl) (d_attrs_initial:list S.term) quals tcs : (env_t & sigelts) =
  let rng = d.drange in
  let tycon_id = function
    | TyconAbstract(id, _, _)
    | TyconAbbrev(id, _, _, _)
    | TyconRecord(id, _, _, _, _)
    | TyconVariant(id, _, _, _) -> id in
  let binder_to_term b = match b.b with
    | Annotated (x, _)
    | Variable x -> mk_term (Var (lid_of_ids [x])) (range_of_id x) Expr
    | TAnnotated(a, _)
    | TVariable a -> mk_term (Tvar a) (range_of_id a) Type_level
    | NoName t -> t in
  let desugar_tycon_variant_record = function
    // for every variant, each constructor whose payload is a record
    // is desugared into a reference to a _generated_ record type
    // declaration
    | TyconVariant (id, bds, k, variants) -> 
        let additional_records, variants = map (fun (cid, payload, attrs) ->
              match payload with
              | Some (VpRecord (r, k)) -> 
                  let record_id = mk_ident (string_of_id id ^ "__" ^ string_of_id cid ^ "__payload", range_of_id cid) in
                  let record_id_t = {tm = lid_of_ns_and_id [] record_id |> Var; range = range_of_id cid; level = Type_level} in
                  let payload_typ = mkApp record_id_t (List.map (fun bd -> binder_to_term bd, Nothing) bds) (range_of_id record_id) in
                  let desugar_marker = 
                    let range = range_of_id record_id in
                    let desugar_attr_fv = {fv_name = {v = FStarC.Parser.Const.desugar_of_variant_record_lid; p = range}; fv_qual = None} in
                    let desugar_attr = S.mk (Tm_fvar desugar_attr_fv) range in
                    let cid_as_constant = EMB.embed (string_of_lid (qualify env cid)) range None EMB.id_norm_cb in
                    S.mk_Tm_app desugar_attr [(cid_as_constant, None)] range
                  in
                  (TyconRecord (record_id, bds, None, attrs, r), desugar_marker::d_attrs_initial) |> Some
                , (cid, Some ( match k with
                             | None   -> VpOfNotation payload_typ
                             | Some k -> 
                                    VpArbitrary 
                                       { tm = Product ([mk_binder (NoName payload_typ) (range_of_id record_id) Type_level None], k)
                                       ; range = payload_typ.range
                                       ; level = Type_level
                                       }
                             ), attrs)
              | _ -> None, (cid, payload, attrs)
            ) variants |> unzip in
         // TODO: [concat_options] should live somewhere else
         let concat_options = filter_map (fun r -> r) in
         concat_options additional_records @ [(TyconVariant (id, bds, k, variants), d_attrs_initial)]
    | tycon -> [(tycon, d_attrs_initial)] in
  let tcs = concatMap desugar_tycon_variant_record tcs in
  let tot rng = mk_term (Name (C.effect_Tot_lid)) rng Expr in
  let with_constructor_effect t = mk_term (App(tot t.range, t, Nothing)) t.range t.level in
  let apply_binders t binders =
    let imp_of_aqual (b:AST.binder) = match b.aqual with
        | Some Implicit
        | Some (Meta _)
        | Some TypeClassArg -> Hash
        | _ -> Nothing in
    List.fold_left (fun out b -> mk_term (App(out, binder_to_term b, imp_of_aqual b)) out.range out.level)
      t binders in
  let tycon_record_as_variant = function
    | TyconRecord(id, parms, kopt, attrs, fields) ->
      let constrName = mk_ident("Mk" ^ (string_of_id id), (range_of_id id)) in
      let mfields = List.map (fun (x,q,attrs,t) -> FStarC.Parser.AST.mk_binder_with_attrs (Annotated(x,t)) (range_of_id x) Expr q attrs) fields in
      let result = apply_binders (mk_term (Var (lid_of_ids [id])) (range_of_id id) Type_level) parms in
      let constrTyp = mk_term (Product(mfields, with_constructor_effect result)) (range_of_id id) Type_level in
      //let _ = BU.print_string (BU.format2 "Translated record %s to constructor %s\n" ((string_of_id id)) (term_to_string constrTyp)) in

      let names = id :: binder_idents parms in
      List.iter (fun (f, _, _, _) ->
          if BU.for_some (fun i -> ident_equals f i) names then
              raise_error f Errors.Error_FieldShadow
                (BU.format1 "Field %s shadows the record's name or a parameter of it, please rename it" (string_of_id f)))
          fields;

      TyconVariant(id, parms, kopt, [(constrName, Some (VpArbitrary constrTyp), attrs)]), fields |> List.map (fun (f, _, _, _) -> f)
    | _ -> failwith "impossible" in
  let desugar_abstract_tc quals _env mutuals d_attrs = function
    | TyconAbstract(id, binders, kopt) ->
      let _env', typars = typars_of_binders _env binders in
      let k = match kopt with
        | None -> U.ktype
        | Some k -> desugar_term _env' k in
      let tconstr = apply_binders (mk_term (Var (lid_of_ids [id])) (range_of_id id) Type_level) binders in
      let qlid = qualify _env id in
      let typars = Subst.close_binders typars in
      let k = Subst.close typars k in
      let se = { sigel = Sig_inductive_typ {lid=qlid;
                                            us=[];
                                            params=typars;
                                            num_uniform_params=None;
                                            t=k;
                                            mutuals;
                                            ds=[];
                                            injective_type_params=false};
                 sigquals = quals;
                 sigrng = range_of_id id;
                 sigmeta = default_sigmeta;
                 sigattrs = d_attrs;
                 sigopts = None;
                 sigopens_and_abbrevs = opens_and_abbrevs env
               } in
      let _env, _ = Env.push_top_level_rec_binding _env id in
      let _env2, _ = Env.push_top_level_rec_binding _env' id in
      _env, _env2, se, tconstr
    | _ -> failwith "Unexpected tycon" in
  let push_tparams env bs =
    let env, bs = List.fold_left (fun (env, tps) b ->
        let env, y = Env.push_bv env b.binder_bv.ppname in
        env, (mk_binder_with_attrs y b.binder_qual b.binder_attrs)::tps) (env, []) bs in
    env, List.rev bs in
  match tcs with
    | [(TyconAbstract(id, bs, kopt), d_attrs)] ->
        let kopt = match kopt with
            | None -> Some (tm_type_z (range_of_id id))
            | _ -> kopt in
        let tc = TyconAbstract(id, bs, kopt) in
        let _, _, se, _ = desugar_abstract_tc quals env [] d_attrs tc in
        let se = match se.sigel with
           | Sig_inductive_typ {lid=l; params=typars; t=k; mutuals=[]; ds=[]} ->
             let quals = se.sigquals in
             let quals = if List.contains S.Assumption quals
                         then quals
                         else (if not (Options.ml_ish ()) then
                                 log_issue se Errors.Warning_AddImplicitAssumeNewQualifier
                                   (BU.format1 "Adding an implicit 'assume new' qualifier on %s" (show l));
                                 S.Assumption :: S.New :: quals) in
             let t = match typars with
                | [] -> k
                | _ -> mk (Tm_arrow {bs=typars; comp=mk_Total k}) se.sigrng in
             { se with sigel = Sig_declare_typ {lid=l; us=[]; t};
                       sigquals = quals }
           | _ -> failwith "Impossible" in
        let env = push_sigelt env se in
        (* let _ = pr "Pushed %s\n" (string_of_lid (qualify env (tycon_id tc))) in *)
        env, [se]

    | [(TyconAbbrev(id, binders, kopt, t), _d_attrs)] ->
        let env', typars = typars_of_binders env binders in
        let kopt = match kopt with
            | None ->
              if BU.for_some (function S.Effect -> true | _ -> false) quals
              then Some teff
              else None
            | Some k -> Some (desugar_term env' k) in
        let t0 = t in
        let quals = if quals |> BU.for_some (function S.Logic -> true | _ -> false)
                    then quals
                    else if t0.level = Formula
                    then S.Logic::quals
                    else quals in
        let qlid = qualify env id in
        let se =
            if quals |> List.contains S.Effect
            then
                let t, cattributes =
                    match (unparen t).tm with
                        (* TODO : we are only handling the case Effect args (attributes ...) *)
                        | Construct (head, args) ->
                            let cattributes, args =
                                match List.rev args with
                                    | (last_arg, _) :: args_rev ->
                                        begin match (unparen last_arg).tm with
                                            | Attributes ts -> ts, List.rev (args_rev)
                                            | _ -> [], args
                                        end
                                    | _ -> [], args
                            in
                            mk_term (Construct (head, args)) t.range t.level,
                            desugar_attributes env cattributes
                         | _ -> t, []
                 in
                 let c = desugar_comp t.range false env' t in
                 let typars = Subst.close_binders typars in
                 let c = Subst.close_comp typars c in
                 let quals = quals |> List.filter (function S.Effect -> false | _ -> true) in
                 { sigel = Sig_effect_abbrev {lid=qlid; us=[]; bs=typars; comp=c;
                                              cflags=cattributes @ comp_flags c};
                   sigquals = quals;
                   sigrng = range_of_id id;
                   sigmeta = default_sigmeta  ;
                   sigattrs = [];
                   sigopts = None;
                   sigopens_and_abbrevs = opens_and_abbrevs env
                  }
            else let t = desugar_typ env' t in
                 mk_typ_abbrev env d qlid [] typars kopt t [qlid] quals (range_of_id id) in

        let env = push_sigelt env se in
        env, [se]

    | [(TyconRecord payload, d_attrs)] ->
      let trec = TyconRecord payload in
      let t, fs = tycon_record_as_variant trec in
      desugar_tycon env d d_attrs (RecordType (ids_of_lid (current_module env), fs)::quals) [t]

    |  _::_ ->
      let env0 = env in
      let mutuals = List.map (fun (x, _) -> qualify env <| tycon_id x) tcs in
      let rec collect_tcs quals et (tc, d_attrs) =
        let (env, tcs) = et in
        match tc with
          | TyconRecord _ ->
            let trec = tc in
            let t, fs = tycon_record_as_variant trec in
            collect_tcs (RecordType (ids_of_lid (current_module env), fs)::quals) (env, tcs) (t, d_attrs)
          | TyconVariant(id, binders, kopt, constructors) ->
            let env, _, se, tconstr = desugar_abstract_tc quals env mutuals d_attrs (TyconAbstract(id, binders, kopt)) in
            env, (Inl(se, constructors, tconstr, quals), d_attrs)::tcs
          | TyconAbbrev(id, binders, kopt, t) ->
            let env, _, se, tconstr = desugar_abstract_tc quals env mutuals d_attrs (TyconAbstract(id, binders, kopt)) in
            env, (Inr(se, binders, t, quals), d_attrs)::tcs
          | _ -> raise_error rng Errors.Fatal_NonInductiveInMutuallyDefinedType "Mutually defined type contains a non-inductive element" in
      let env, tcs = List.fold_left (collect_tcs quals) (env, []) tcs in
      let tcs = List.rev tcs in
      let tps_sigelts = tcs |> List.collect (fun (tc, d_attrs) -> 
          match tc with
        | Inr ({ sigel = Sig_inductive_typ {lid=id;
                                            us=uvs;
                                            params=tpars;
                                            t=k} }, binders, t, quals) -> //type abbrevs in mutual type definitions
              let t =
                  let env, tpars = typars_of_binders env binders in
                  let env_tps, tpars = push_tparams env tpars in
                  let t = desugar_typ env_tps t in
                  let tpars = Subst.close_binders tpars in
                  Subst.close tpars t
          in
          [([], mk_typ_abbrev env d id uvs tpars (Some k) t [id] quals (range_of_lid id))]

        | Inl ({ sigel = Sig_inductive_typ {lid=tname;
                                            us=univs;
                                            params=tpars;
                                            num_uniform_params=num_uniform;
                                            t=k;
                                            mutuals;
                                            injective_type_params}; sigquals = tname_quals },
               constrs, tconstr, quals) ->
          let mk_tot t =
            let tot = mk_term (Name C.effect_Tot_lid) t.range t.level in
            mk_term (App(tot, t, Nothing)) t.range t.level in
          let tycon = (tname, tpars, k) in
          let env_tps, tps = push_tparams env tpars in
          let data_tpars = List.map (fun tp -> { tp with S.binder_qual = Some (S.Implicit true) }) tps in
          let tot_tconstr = mk_tot tconstr in
          let val_attrs = Env.lookup_letbinding_quals_and_attrs env0 tname |> snd in
          let constrNames, constrs = List.split <|
              (constrs |> List.map (fun (id, payload, cons_attrs) ->
                let t = match payload with
                      | Some (VpArbitrary  t) -> t
                      | Some (VpOfNotation t) -> mk_term (Product([mk_binder (NoName t) t.range t.level None], tot_tconstr)) t.range t.level
                      | Some (VpRecord     _) -> failwith "Impossible: [VpRecord _] should have disappeared after [desugar_tycon_variant_record]"
                      | None                  -> { tconstr with range = range_of_id id }
                in
                let t = desugar_term env_tps (close env_tps t) in
                let name = qualify env id in
                let quals = tname_quals |> List.collect (function
                    | RecordType fns -> [RecordConstructor fns]
                    | _ -> []) in
                let ntps = List.length data_tpars in
                (name, (tps, { sigel = Sig_datacon {lid=name;
                                                    us=univs;
                                                    t=U.arrow data_tpars (mk_Total (t |> U.name_function_binders));
                                                    ty_lid=tname;
                                                    num_ty_params=ntps;
                                                    mutuals;
                                                    injective_type_params};
                                            sigquals = quals;
                                            sigrng = range_of_lid name;
                                            sigmeta = default_sigmeta  ;
                                            sigattrs = U.deduplicate_terms (val_attrs @ d_attrs @ map (desugar_term env) cons_attrs);
                                            sigopts = None;
                                            sigopens_and_abbrevs = opens_and_abbrevs env
                              }))))
          in
          if !dbg_attrs
          then (
            BU.print3 "Adding attributes to type %s: val_attrs=[@@%s] attrs=[@@%s]\n" 
              (show tname) (show val_attrs) (show d_attrs)
          );
          ([], { sigel = Sig_inductive_typ {lid=tname;
                                            us=univs;
                                            params=tpars;
                                            num_uniform_params=num_uniform;
                                            t=k;
                                            mutuals;
                                            ds=constrNames;
                                            injective_type_params};
                                 sigquals = tname_quals;
                                 sigrng = range_of_lid tname;
                                 sigmeta = default_sigmeta  ;
                                 sigattrs = U.deduplicate_terms (val_attrs @ d_attrs);
                                 sigopts = None;
                                 sigopens_and_abbrevs = opens_and_abbrevs env
                })::constrs
        | _ -> failwith "impossible")
      in
      let sigelts = tps_sigelts |> List.map (fun (_, se) -> se) in
      let bundle, abbrevs = FStarC.Syntax.MutRecTy.disentangle_abbrevs_from_bundle sigelts quals (List.collect U.lids_of_sigelt sigelts) rng in
      if !dbg_attrs
      then (
        BU.print1 "After disentangling: %s\n" (show bundle)
      );
      let env = push_sigelt env0 bundle in
      let env = List.fold_left push_sigelt env abbrevs in
      (* NOTE: derived operators such as projectors and discriminators are using the type names before unfolding. *)
      let data_ops = tps_sigelts |> List.collect (fun (tps, se) -> mk_data_projector_names quals env se) in
      let discs = sigelts |> List.collect (fun se -> match se.sigel with
        | Sig_inductive_typ {lid=tname; params=tps; t=k; ds=constrs} ->
          let quals = se.sigquals in
          mk_data_discriminators quals env 
            (constrs |> List.filter (fun data_lid ->  //AR: create data discriminators only for non-record data constructors
                                     let data_quals =
                                       let data_se = sigelts |> List.find (fun se -> match se.sigel with
                                                                                     | Sig_datacon {lid=name} -> lid_equals name data_lid
                                                                                     | _ -> false) |> must in
                                       data_se.sigquals in
                                     not (data_quals |> List.existsb (function | RecordConstructor _ -> true | _ -> false))))
            se.sigattrs
        | _ -> []) in
      let ops = discs@data_ops in
      let env = List.fold_left push_sigelt env ops in
      env, [bundle]@abbrevs@ops

    | [] -> failwith "impossible"

let desugar_binders env binders =
    let env, binders = List.fold_left (fun (env,binders) b ->
    match desugar_binder env b with
      | Some a, k, attrs ->
        let binder, env = as_binder env b.aqual (Some a, k, attrs) in
        env, binder::binders

      | _ -> raise_error b Errors.Fatal_MissingNameInBinder "Missing name in binder") (env, []) binders in
    env, List.rev binders

let push_reflect_effect env quals (effect_name:Ident.lid) range =
    if quals |> BU.for_some (function S.Reflectable _ -> true | _ -> false)
    then let monad_env = Env.enter_monad_scope env (ident_of_lid effect_name) in
         let reflect_lid = Ident.id_of_text "reflect" |> Env.qualify monad_env in
         let quals = [S.Assumption; S.Reflectable effect_name] in
         let refl_decl = { sigel = S.Sig_declare_typ {lid=reflect_lid; us=[]; t=S.tun};
                           sigrng = range;
                           sigquals = quals;
                           sigmeta = default_sigmeta  ;
                           sigattrs = [];
                           sigopts = None;
                           sigopens_and_abbrevs = opens_and_abbrevs env
                         } in
         Env.push_sigelt env refl_decl // FIXME: Add docs to refl_decl?
    else env

let parse_attr_with_list warn (at:S.term) (head:lident) : option (list int & Range.range) & bool =
  let warn () =
    if warn then
      Errors.log_issue at Errors.Warning_UnappliedFail
        (BU.format1 "Found ill-applied '%s', argument should be a non-empty list of integer literals" (string_of_lid head))
  in
  let hd, args = U.head_and_args at in
   match (SS.compress hd).n with
   | Tm_fvar fv when S.fv_eq_lid fv head ->
     begin
       match args with
       | [] -> Some ([], at.pos), true
       | [(a1, _)] ->
         begin
         match EMB.unembed a1 EMB.id_norm_cb with
         | Some es ->
           Some (List.map FStarC.BigInt.to_int_fs es, at.pos), true
         | _ ->
           warn();
           None, true
         end
      | _ ->
        warn ();
        None, true
     end

   | _ ->
     None, false


// If this is an expect_failure attribute, return the listed errors and whether it's a expect_lax_failure or not
let get_fail_attr1 warn (at : S.term) : option (list int & Range.range & bool) =
    let rebind res b =
      match res with
      | None -> None
      | Some (l, rng) -> Some (l, rng, b)
    in
    let res, matched = parse_attr_with_list warn at C.fail_attr in
    if matched then rebind res false
    else let res, _ = parse_attr_with_list warn at C.fail_lax_attr in
         rebind res true

// Traverse a list of attributes to find all expect_failures and combine them
let get_fail_attr warn (ats : list S.term) : option (list int & Range.range & bool) =
    let comb f1 f2 =
      match f1, f2 with
      | Some (e1, rng1, l1), Some (e2, rng2, l2) ->
        Some (e1@e2, rng1 `Range.union_ranges` rng2, l1 || l2)

      | Some x, None
      | None, Some x ->
        Some x

      | _ -> None
    in
    List.fold_right (fun at acc -> comb (get_fail_attr1 warn at) acc) ats None

let lookup_effect_lid env (l:lident) (r:Range.range) : S.eff_decl =
  match Env.try_lookup_effect_defn env l with
  | None ->
    raise_error r Errors.Fatal_EffectNotFound
      ("Effect name " ^ show l ^ " not found")
  | Some l -> l

let rec desugar_effect env d (d_attrs:list S.term) (quals: qualifiers) (is_layered:bool) eff_name eff_binders eff_typ eff_decls =
    let env0 = env in
    // qualified with effect name
    let monad_env = Env.enter_monad_scope env eff_name in
    let env, binders = desugar_binders monad_env eff_binders in
    let eff_t = desugar_term env eff_typ in

    let num_indices = List.length (fst (U.arrow_formals eff_t)) in

    (* An effect for free has a type of the shape "a:Type -> Effect" *)
    let for_free = num_indices = 1 && not is_layered in
    if for_free
    then Errors.log_issue d Errors.Warning_DeprecatedGeneric
            (BU.format1 "DM4Free feature is deprecated and will be removed soon, \
              use layered effects to define %s" (Ident.string_of_id eff_name));

    let mandatory_members =
      let rr_members = ["repr" ; "return" ; "bind"] in
      if for_free then rr_members
        (*
         * AR: subcomp, if_then_else, and close are optional
         *     but adding here so as not to count them as actions
         *)
      else if is_layered then rr_members @ [ "subcomp"; "if_then_else"; "close" ]
        (* the first 3 are optional but must not be counted as actions *)
      else rr_members @ [
        "return_wp";
        "bind_wp";
        "if_then_else";
        "ite_wp";
        "stronger";
        "close_wp";
        "trivial"
      ]
    in

    let name_of_eff_decl decl =
      match decl.d with
      | Tycon(_, _, [TyconAbbrev(name, _, _, _)]) -> Ident.string_of_id name
      | _ -> failwith "Malformed effect member declaration."
    in

    let mandatory_members_decls, actions =
      List.partition (fun decl -> List.mem (name_of_eff_decl decl) mandatory_members) eff_decls
    in

    let env, decls = mandatory_members_decls |> List.fold_left (fun (env, out) decl ->
        let env, ses = desugar_decl env decl in
        env, List.hd ses::out)
      (env, [])
    in
    let binders = Subst.close_binders binders in
    let actions = actions |> List.map (fun d ->
        match d.d with
        | Tycon(_, _,[TyconAbbrev(name, action_params, _, { tm = Construct (_, [ def, _; cps_type, _ ])})]) when not for_free ->
            // When the effect is not for free, user has to provide a pair of
            // the definition and its cps'd type.
            let env, action_params = desugar_binders env action_params in
            let action_params = Subst.close_binders action_params in
            {
              action_name=Env.qualify env name;
              action_unqualified_name = name;
              action_univs=[];
              action_params = action_params;
              action_defn=Subst.close (binders @ action_params) (desugar_term env def);
              action_typ=Subst.close (binders @ action_params) (desugar_typ env cps_type)
            }
        | Tycon(_, _, [TyconAbbrev(name, action_params, _, defn)]) when for_free || is_layered ->
            // When for free, the user just provides the definition and the rest
            // is elaborated
            // For layered effects also, user just provides the definition
            let env, action_params = desugar_binders env action_params in
            let action_params = Subst.close_binders action_params in
            {
              action_name=Env.qualify env name;
              action_unqualified_name = name;
              action_univs=[];
              action_params = action_params;
              action_defn=Subst.close (binders@action_params) (desugar_term env defn);
              action_typ=S.tun
            }
        | _ ->
            raise_error d Errors.Fatal_MalformedActionDeclaration
              ("Malformed action declaration; if this is an \"effect \
              for free\", just provide the direct-style declaration. If this is \
              not an \"effect for free\", please provide a pair of the definition \
              and its cps-type with arrows inserted in the right place (see \
              examples).")
    ) in
    let eff_t = Subst.close binders eff_t in
    let lookup s =
        let l = Env.qualify env (mk_ident(s, d.drange)) in
        [], Subst.close binders <| fail_or env (try_lookup_definition env) l in
    let mname       =qualify env0 eff_name in
    let qualifiers  =List.map (trans_qual d.drange (Some mname)) quals in
    let dummy_tscheme = [], S.tun in
    let eff_sig, combinators =
      if for_free then
        WP_eff_sig ([], eff_t),
        DM4F_eff ({
          ret_wp = dummy_tscheme;
          bind_wp = dummy_tscheme;
          stronger = dummy_tscheme;
          if_then_else = dummy_tscheme;
          ite_wp = dummy_tscheme;
          close_wp = dummy_tscheme;
          trivial = dummy_tscheme;

          repr = Some (lookup "repr");
          return_repr = Some (lookup "return");
          bind_repr = Some (lookup "bind");
        })
      else if is_layered then
        let has_subcomp = List.existsb (fun decl -> name_of_eff_decl decl = "subcomp") eff_decls in
        let has_if_then_else = List.existsb (fun decl -> name_of_eff_decl decl = "if_then_else") eff_decls in
        let has_close = List.existsb (fun decl -> name_of_eff_decl decl = "close") eff_decls in

        //setting the second component to dummy_ts,
        //  and kind to None, typechecker fills them in
        let to_comb (us, t) = (us, t), dummy_tscheme, None in

 
        let eff_t, num_effect_params =
          match (SS.compress eff_t).n with
          | Tm_arrow {bs; comp=c} ->
            // peel off the first a:Type binder
            let a::bs = bs in
            //
            // allow_param checks that all effect parameters
            //   are upfront
            // it is true initially, and is set to false as soon as
            //   we see a non-parameter binder
            // and if some parameter appears after that, we raise an error
            //
            let n, _, bs = List.fold_left (fun (n, allow_param, bs) b ->
              let b_attrs = b.binder_attrs in
              let is_param = U.has_attribute b_attrs C.effect_parameter_attr in
              if is_param && not allow_param
              then raise_error d Errors.Fatal_UnexpectedEffect "Effect parameters must all be upfront";
              let b_attrs = U.remove_attr C.effect_parameter_attr b_attrs in
              (if is_param then n+1 else n),
              allow_param && is_param,
              bs@[{b with binder_attrs=b_attrs}]) (0, true, []) bs in
            {eff_t with n=Tm_arrow {bs=a::bs; comp=c}},
            n
          | _ -> failwith "desugaring indexed effect: effect type not an arrow" in

        (*
         * AR: if subcomp or if_then_else are not specified, then fill in dummy_tscheme
         *     typechecker will fill in an appropriate default
         *)

        Layered_eff_sig (num_effect_params, ([], eff_t)),
        Layered_eff ({
          l_repr = lookup "repr", dummy_tscheme;
          l_return = lookup "return", dummy_tscheme;
          l_bind = lookup "bind" |> to_comb;
          l_subcomp =
            if has_subcomp then lookup "subcomp" |> to_comb
            else dummy_tscheme, dummy_tscheme, None;
          l_if_then_else =
            if has_if_then_else then lookup "if_then_else" |> to_comb
            else dummy_tscheme, dummy_tscheme, None;
          l_close =
            if has_close then Some (lookup "close", dummy_tscheme)
            else None;  // If close is not specified, leave it to None
                        // The typechecker will also not fill it in
        })
      else
        let rr = BU.for_some (function S.Reifiable | S.Reflectable _ -> true | _ -> false) qualifiers in
        WP_eff_sig ([], eff_t),
        Primitive_eff ({
          ret_wp = lookup "return_wp";
          bind_wp = lookup "bind_wp";
          stronger = lookup "stronger";
          if_then_else = lookup "if_then_else";
          ite_wp = lookup "ite_wp";
          close_wp = lookup "close_wp";
          trivial = lookup "trivial";

          repr = if rr then Some (lookup "repr") else None;
          return_repr = if rr then Some (lookup "return") else None;
          bind_repr = if rr then Some (lookup "bind") else None
        }) in

    let extraction_mode =
      if is_layered
      then S.Extract_none ""  // will be populated by the typechecker
      else if for_free
      then if BU.for_some (function S.Reifiable -> true | _ -> false) qualifiers
           then S.Extract_reify
           else S.Extract_primitive
      else S.Extract_primitive in

    let sigel = Sig_new_effect ({
      mname = mname;
      cattributes = [];
      univs = [];
      binders = binders;
      signature = eff_sig;
      combinators = combinators;
      actions = actions;
      eff_attrs = d_attrs;
      extraction_mode
    }) in

    let se = ({
      sigel = sigel;
      sigquals = qualifiers;
      sigrng = d.drange;
      sigmeta = default_sigmeta  ;
      sigattrs = d_attrs;
      sigopts = None;
      sigopens_and_abbrevs = opens_and_abbrevs env
    }) in

    let env = push_sigelt env0 se in
    let env = actions |> List.fold_left (fun env a ->
        //printfn "Pushing action %s\n" (string_of_lid a.action_name);
        push_sigelt env (U.action_as_lb mname a a.action_defn.pos)) env
    in
    let env = push_reflect_effect env qualifiers mname d.drange in
    env, [se]

and desugar_redefine_effect env d d_attrs trans_qual quals eff_name eff_binders defn =
    let env0 = env in
    let env = Env.enter_monad_scope env eff_name in
    let env, binders = desugar_binders env eff_binders in
    let ed_lid, ed, args, cattributes =
        let head, args = head_and_args defn in
        let lid = match head.tm with
          | Name l -> l
          | _ -> raise_error d Errors.Fatal_EffectNotFound ("Effect " ^AST.term_to_string head^ " not found")
        in
        let ed = fail_or env (Env.try_lookup_effect_defn env) lid in
        let cattributes, args =
            match List.rev args with
            | (last_arg, _) :: args_rev ->
                begin match (unparen last_arg).tm with
                    | Attributes ts -> ts, List.rev (args_rev)
                    | _ -> [], args
                end
            | _ -> [], args
        in
        lid, ed, desugar_args env args, desugar_attributes env cattributes in
//    printfn "ToSyntax got eff_decl: %s\n" (Print.eff_decl_to_string false ed);
    let binders = Subst.close_binders binders in
    if List.length args <> List.length ed.binders
    then raise_error defn Errors.Fatal_ArgumentLengthMismatch "Unexpected number of arguments to effect constructor";
    let ed_binders, _, ed_binders_opening = Subst.open_term' ed.binders S.t_unit in
    let sub' shift_n (us, x) =
        let x = Subst.subst (Subst.shift_subst (shift_n + List.length us) ed_binders_opening) x in
        let s = U.subst_of_list ed_binders args in
        Subst.close_tscheme binders (us, (Subst.subst s x))
    in
    let sub = sub' 0 in
    let mname=qualify env0 eff_name in
    let ed = {
            mname         = mname;
            cattributes   = cattributes;
            univs         = ed.univs;
            binders       = binders;
            signature     = U.apply_eff_sig sub ed.signature;
            combinators   = apply_eff_combinators sub ed.combinators;
            actions       = List.map (fun action ->
                let nparam = List.length action.action_params in
                {
                    // Since we called enter_monad_env before, this is going to generate
                    // a name of the form FStarC.Effect.uu___proj__STATE__item__get
                    action_name = Env.qualify env (action.action_unqualified_name);
                    action_unqualified_name = action.action_unqualified_name;
                    action_univs = action.action_univs ;
                    action_params = action.action_params ;
                    (* These need to be shifted further since they have the action's parameters also in scope *)
                    action_defn =snd (sub' nparam ([], action.action_defn)) ;
                    action_typ =snd (sub' nparam ([], action.action_typ))
                        // GM: ^ Although isn't this one always Tm_unknown at this point?
                })
                ed.actions;
            eff_attrs   = ed.eff_attrs;
            extraction_mode = ed.extraction_mode;
    } in
    let se =
      { sigel = Sig_new_effect ed;
        sigquals = List.map (trans_qual (Some mname)) quals;
        sigrng = d.drange;
        sigmeta = default_sigmeta  ;
        sigattrs = d_attrs;
        sigopts = None;
        sigopens_and_abbrevs = opens_and_abbrevs env
      }
    in
    let monad_env = env in
    let env = push_sigelt env0 se in
    let env =
      ed.actions |> List.fold_left
        (fun env a -> push_sigelt env (U.action_as_lb mname a a.action_defn.pos))
        env
    in
    let env =
        if quals |> List.contains Reflectable
        then let reflect_lid = Ident.id_of_text "reflect" |> Env.qualify monad_env in
             let quals = [S.Assumption; S.Reflectable mname] in
             let refl_decl = { sigel = S.Sig_declare_typ {lid=reflect_lid; us=[]; t=S.tun};
                               sigquals = quals;
                               sigrng = d.drange;
                               sigmeta = default_sigmeta  ;
                               sigattrs = [];
                               sigopts = None;
                               sigopens_and_abbrevs = opens_and_abbrevs env
                              } in
             push_sigelt env refl_decl
        else env in
    env, [se]


and desugar_decl_maybe_fail_attr env (d: decl): (env_t & sigelts) =
  let no_fail_attrs (ats : list S.term) : list S.term =
      List.filter (fun at -> Option.isNone (get_fail_attr1 false at)) ats
  in

  (* If this is an expect_failure, check to see if it fails.
   * If it does, check that the errors match as we normally do.
   * If it doesn't fail, leave it alone! The typechecker will check the failure. *)
  let env, sigelts =
    let attrs = List.map (desugar_term env) d.attrs in
    let attrs = U.deduplicate_terms attrs in
    match get_fail_attr false attrs with
    | Some (expected_errs, err_rng, lax) ->
      // The `fail` attribute behaves
      // differentrly! We only keep that one on the first new decl.
      let env0 =
          Env.snapshot env |> snd  (* we need the snapshot since pushing the let
                                    * will shadow a previous val *)
      in
      let d = { d with attrs = [] } in
      let errs, r = Errors.catch_errors (fun () ->
                      Options.with_saved_options (fun () ->
                        desugar_decl_core env attrs d)) in
      begin match errs, r with
      | [], Some (env, ses) ->
        (* Succeeded desugaring, carry on, but make a Sig_fail *)
        (* Restore attributes, except for fail *)
        let ses = List.map (fun se -> { se with sigattrs = no_fail_attrs attrs }) ses in
        let se = { sigel = Sig_fail {rng=err_rng;errs=expected_errs; fail_in_lax=lax; ses};
                   sigquals = [];
                   sigrng = d.drange;
                   sigmeta = default_sigmeta;
                   sigattrs = attrs;
                   sigopts = None;
                   sigopens_and_abbrevs = opens_and_abbrevs env
                  } in
        env0, [se]

      | errs, ropt -> (* failed! check that it failed as expected *)
        let errnos = List.concatMap (fun i -> FStarC.Common.list_of_option i.issue_number) errs in
        if Options.print_expected_failures () then (
          (* Print errors if asked for *)
          BU.print_string ">> Got issues: [\n";
          List.iter Errors.print_issue errs;
          BU.print_string ">>]\n"
        );
        if expected_errs = [] then
          env0, []
        else begin
          match Errors.find_multiset_discrepancy expected_errs errnos with
          | None -> env0, []
          | Some (e, n1, n2) ->
            let open FStarC.Class.PP in
            let open FStarC.Pprint in
            List.iter Errors.print_issue errs;
            Errors.log_issue err_rng Errors.Error_DidNotFail [
                prefix 2 1
                  (text "This top-level definition was expected to raise error codes")
                  (pp expected_errs) ^/^
                prefix 2 1 (text "but it raised")
                  (pp errnos) ^^ text "(at desugaring time)" ^^ dot;
                text (BU.format3 "Error #%s was raised %s times, instead of %s."
                                      (show e) (show n2) (show n1));
              ];
            env0, []
        end
      end
    | None ->
      desugar_decl_core env attrs d
  in
  env, sigelts

and desugar_decl env (d:decl) :(env_t & sigelts) =
  FStarC.GenSym.reset_gensym ();
  let env, ses = desugar_decl_maybe_fail_attr env d in
  env, ses |> List.map generalize_annotated_univs

and desugar_decl_core env (d_attrs:list S.term) (d:decl) : (env_t & sigelts) =
  let trans_qual = trans_qual d.drange in
  match d.d with
  | Pragma p ->
    let p = trans_pragma p in
    U.process_pragma p d.drange;
    let se = { sigel = Sig_pragma p;
               sigquals = [];
               sigrng = d.drange;
               sigmeta = default_sigmeta;
               sigattrs = d_attrs;
               sigopts = None;
               sigopens_and_abbrevs = opens_and_abbrevs env
              } in
    env, [se]

  | TopLevelModule id -> env, []

  | Open (lid, restriction) ->
    let env = Env.push_namespace env lid restriction in
    env, []

  | Friend lid ->
    (* Several checks to accept a friend declaration. *)
    let open FStarC.Errors in
    let open FStarC.Pprint in
    let open FStarC.Class.PP in
    if Env.iface env then
      raise_error d Errors.Fatal_FriendInterface [
        text "'friend' declarations are not allowed in interfaces.";
      ];
    if not (FStarC.Parser.Dep.module_has_interface (Env.dep_graph env) (Env.current_module env)) then
      raise_error d Errors.Fatal_FriendInterface [
        text "'friend' declarations are not allowed in modules that lack interfaces.";
        text "Suggestion: add an interface for module" ^/^ pp (Env.current_module env);
      ];
    if not (FStarC.Parser.Dep.deps_has_implementation (Env.dep_graph env) lid) then
      raise_error d Errors.Fatal_FriendInterface [
        text "'friend' module" ^/^ pp lid ^/^ text "not found";
        text "Suggestion: recompute dependences (C-c C-r) if in interactive mode.";
      ];
    if not (FStarC.Parser.Dep.module_has_interface (Env.dep_graph env) lid) then
      raise_error d Errors.Fatal_FriendInterface [
        text "'friend' declarations cannot refer to modules that lack interfaces.";
        text "Suggestion: add an interfce for module" ^/^ pp lid;
      ];
    env, []

  | Include (lid, restriction) ->
    let env = Env.push_include env lid restriction in
    env, []

  | ModuleAbbrev(x, l) ->
    Env.push_module_abbrev env x l, []

  | Tycon(is_effect, typeclass, tcs) ->
    let quals = d.quals in
    let quals = if is_effect then Effect_qual :: quals else quals in
    let quals =
        if typeclass then
            match tcs with
            | [(TyconRecord _)] -> Noeq :: quals
            | _ -> raise_error d Errors.Error_BadClassDecl "Ill-formed `class` declaration: definition must be a record type"
        else quals
    in
    let env, ses = desugar_tycon env d d_attrs (List.map (trans_qual None) quals) tcs in
    if !dbg_attrs
    then (
      BU.print2 "Desugared tycon from {%s} to {%s}\n" (show d) (show ses)
    );
    (* Handling typeclasses: we typecheck the tcs as usual, and then need to add
     * %splice[new_meth_lids] (mk_class type_lid)
     * where the tricky bit is getting the new_meth_lids. To do so,
     * we traverse the new declarations marked with "Projector", and get
     * the field names. This is pretty ugly. *)
    let mkclass lid =
      let r = range_of_lid lid in
      let body =
      if U.has_attribute d_attrs C.meta_projectors_attr then
        (* new meta projectors *)
        U.mk_app (S.tabbrev C.mk_projs_lid)
                 [S.as_arg (U.exp_bool true);
                  S.as_arg (U.exp_string (string_of_lid lid))]
      else
        (* old mk_class *)
        U.mk_app (S.tabbrev C.mk_class_lid)
                 [S.as_arg (U.exp_string (string_of_lid lid))]
      in
      U.abs [S.mk_binder (S.new_bv (Some r) (tun_r r))] body None
    in
    let get_meths se =
        let rec get_fname quals =
            match quals with
            | S.Projector (_, id) :: _ -> Some id
            | _ :: quals -> get_fname quals
            | [] -> None
        in
        match get_fname se.sigquals with
        | None -> []
        | Some id ->
            [qualify env id]
    in
    let formals =
      let bndl = BU.try_find (function {sigel=Sig_bundle _} -> true | _ -> false) ses in
      match bndl with
      | None -> None
      | Some bndl ->
        match bndl.sigel with
        | Sig_bundle {ses} ->
          BU.find_map
            ses
            (fun se ->
              match se.sigel with
              | Sig_datacon {t} ->
                let formals, _ = U.arrow_formals t in
                Some formals
              | _ -> None)
        | _ -> None
    in
    let rec splice_decl meths se =
        match se.sigel with
        | Sig_bundle {ses} -> List.concatMap (splice_decl meths) ses
        | Sig_inductive_typ {lid; t=ty} ->
          let formals =
            match formals with
            | None -> []
            | Some formals -> formals
          in
          let has_no_method_attr (meth:Ident.lident) =
              let i = Ident.ident_of_lid meth in
              BU.for_some
                (fun formal ->
                   if Ident.ident_equals i formal.binder_bv.ppname
                   then BU.for_some
                         (fun attr ->
                           match (SS.compress attr).n with
                           | Tm_fvar fv -> S.fv_eq_lid fv FStarC.Parser.Const.no_method_lid
                           | _ -> false)
                         formal.binder_attrs
                   else false)
              formals
          in
          let meths = List.filter (fun x -> not (has_no_method_attr x)) meths in
          let is_typed = false in
          [{ sigel = Sig_splice {is_typed; lids=meths; tac=mkclass lid};
             sigquals = [];
             sigrng = d.drange;
             sigmeta = default_sigmeta;
             sigattrs = [];
             sigopts = None;
             sigopens_and_abbrevs = opens_and_abbrevs env }]
        | _ -> []
    in
    let ses, extra =
        if typeclass
        then let meths = List.concatMap get_meths ses in
             let rec add_class_attr se =
               match se.sigel with
               | Sig_bundle {ses; lids} ->
                 let ses = List.map add_class_attr ses in
                 { se with sigel = Sig_bundle {ses; lids}
                         ; sigattrs = U.deduplicate_terms
                                    (S.fvar_with_dd FStarC.Parser.Const.tcclass_lid None
                                      :: se.sigattrs) }

               | Sig_inductive_typ _ ->
                 { se 
                  with sigattrs = U.deduplicate_terms
                                    (S.fvar_with_dd FStarC.Parser.Const.tcclass_lid None
                                      :: se.sigattrs) }

               | _ -> se
             in
             List.map add_class_attr ses,
             List.concatMap (splice_decl meths) ses
        else ses, []
    in
    let env = List.fold_left push_sigelt env extra in
    env, ses @ extra

  | TopLevelLet(isrec, lets) ->
    let quals = d.quals in
    (* If a toplevel let has a non-trivial pattern it needs to be desugared to a serie of top-level lets *)
    let expand_toplevel_pattern =
      isrec = NoLetQualifier &&
      begin match lets with
        | [ { pat = PatOp _}, _ ]
        | [ { pat = PatVar _}, _ ]
        | [ { pat = PatAscribed ({ pat = PatOp  _}, _) }, _ ]
        | [ { pat = PatAscribed ({ pat = PatVar _}, _) }, _ ] -> false
        | [ p, _ ] -> not (is_app_pattern p)
        | _ -> false
      end
    in
    if not expand_toplevel_pattern
    then begin
      (* Usual case *)
      let lets = List.map (fun x -> None, x) lets in
      let as_inner_let =
        mk_term (Let(isrec, lets, mk_term (Const Const_unit) d.drange Expr)) d.drange Expr
      in
      let ds_lets, aq = desugar_term_maybe_top true env as_inner_let in
      check_no_aq aq;
      match (Subst.compress <| ds_lets).n with
        | Tm_let {lbs} ->
          let fvs = snd lbs |> List.map (fun lb -> right lb.lbname) in
          let val_quals, val_attrs =
            List.fold_right (fun fv (qs, ats) ->
                let qs', ats' = Env.lookup_letbinding_quals_and_attrs env fv.fv_name.v in
                (List.rev_append qs' qs, List.rev_append ats' ats))
                fvs
                ([], [])
          in
          (* Propagate top-level attrs to each lb. The lb.lbattrs field should be empty,
           * but just being safe here. *)
          let top_attrs = U.deduplicate_terms <| List.rev_append val_attrs d_attrs in
          let lbs =
            let (isrec, lbs0) = lbs in
            let lbs0 = lbs0 |> List.map (fun lb -> { lb with lbattrs = U.deduplicate_terms (List.rev_append lb.lbattrs top_attrs) }) in
            (isrec, lbs0)
          in
          // BU.print3 "Desugaring %s, val_quals are %s, val_attrs are %s\n"
          //   (List.map show fvs |> String.concat ", ")
          //   (show val_quals)
          //   (List.map show val_attrs |> String.concat ", ");
          let quals =
            match quals with
            | _::_ -> List.map (trans_qual None) quals
            | _ -> val_quals
          in
          let quals =
            if lets |> BU.for_some (fun (_, (_, t)) -> t.level=Formula)
            then S.Logic::quals
            else quals
          in
          let names = fvs |> List.map (fun fv -> fv.fv_name.v) in
          let s = { sigel = Sig_let {lbs; lids=names};
                    sigquals = quals;
                    sigrng = d.drange;
                    sigmeta = default_sigmeta;
                    sigattrs = top_attrs;
                    sigopts = None;
                    sigopens_and_abbrevs = opens_and_abbrevs env;
                   } in
          let env = push_sigelt env s in
          env, [s]
        | _ -> failwith "Desugaring a let did not produce a let"
    end
    else
      (* Need to expand the toplevel pattern into more toplevel lets *)
      (* If there is a top-level pattern we first bind the result of the body *)
      (* to some private anonymous name then we gather each idents bounded in *)
      (* the pattern and introduce one toplevel binding for each of them      *)
      let (pat, body) = match lets with
        | [pat, body] -> pat, body
        | _ -> failwith "expand_toplevel_pattern should only allow single definition lets"
      in
      let rec gen_fresh_toplevel_name () =
        let nm = Ident.gen Range.dummyRange in
        if Some? <| DsEnv.resolve_name env (Ident.lid_of_ids [nm])
        then gen_fresh_toplevel_name()
        else nm
      in
      let fresh_toplevel_name = gen_fresh_toplevel_name() in
      let fresh_pat =
        let var_pat = mk_pattern (PatVar (fresh_toplevel_name, None, [])) Range.dummyRange in
        (* TODO : What about inner type ascriptions ? Is there any way to retrieve those ? *)
        match pat.pat with
          | PatAscribed (pat, ty) -> { pat with pat = PatAscribed (var_pat, ty) }
          | _ -> var_pat
      in
      let main_let =
        (* GM: I'm not sure why we are even marking this private,
         * since it has a reserved name, but anyway keeping it
         * and making it not duplicate the qualifier. *)
        let quals = if List.mem Private d.quals
                    then d.quals
                    else Private :: d.quals
        in
        desugar_decl env ({ d with
          d = TopLevelLet (isrec, [fresh_pat, body]) ;
          quals = quals })
      in

      let main : term = mk_term (Var (lid_of_ids [fresh_toplevel_name])) pat.prange Expr in

      let build_generic_projection (env, ses) (id_opt : option ident) =
        (* When id_opt = Some id, we build a new toplevel definition
         * as follows and then desugar it
         *
         * let id = match fresh_toplevel_name with | pat -> id
         *
         * Otherwise, generate a "coverage check" of the shape
         *
         * let uu___X : unit = match fresh_toplevel_name with | pat -> ()
         *
         *)
        let bv_pat, branch =
          match id_opt with
          | Some id ->
            let lid = lid_of_ids [id] in
            let branch = mk_term (Var lid) (range_of_lid lid) Expr in
            let bv_pat = mk_pattern (PatVar (id, None, [])) (range_of_id id) in
            bv_pat, branch

          | None ->
            let id = gen_fresh_toplevel_name () in
            let branch = mk_term (Const FStarC.Const.Const_unit) Range.dummyRange Expr in
            let bv_pat = mk_pattern (PatVar (id, None, [])) (range_of_id id) in
            let bv_pat = mk_pattern (PatAscribed (bv_pat, (unit_ty (range_of_id id), None)))
                                    (range_of_id id) in
            bv_pat, branch
        in
        let body = mk_term (Match (main, None, None, [pat, None, branch])) main.range Expr in
        let id_decl = mk_decl (TopLevelLet(NoLetQualifier, [bv_pat, body])) Range.dummyRange [] in
        let id_decl = { id_decl with quals = d.quals } in
        let env, ses' = desugar_decl env id_decl in
        env, ses @ ses'
      in

      let build_projection (env, ses) id  = build_generic_projection (env, ses) (Some id) in
      let build_coverage_check (env, ses) = build_generic_projection (env, ses) None in

      let bvs = gather_pattern_bound_vars pat |> elems in

      (* If there are no variables in the pattern (and it is not a
       * wildcard), we should still check to see that it is complete,
       * otherwise things like:
       *   let false = true
       *   let Some 42 = None
       * would be accepted. To do so, we generate a declaration
       * of shape
       *   let uu___X : unit = match body with | pat -> ()
       * which will trigger a check for completeness of pat
       * wrt the body. (See issues #829 and #1903)
       *)
      if List.isEmpty bvs && not (is_var_pattern pat)
      then build_coverage_check main_let
      else List.fold_left build_projection main_let bvs

  | Assume(id, t) ->
    let f = desugar_formula env t in
    let lid = qualify env id in
    env, [{ sigel = Sig_assume {lid; us=[]; phi=f};
            sigquals = [S.Assumption];
            sigrng = d.drange;
            sigmeta = default_sigmeta  ;
            sigattrs = d_attrs;
            sigopts = None;
            sigopens_and_abbrevs = opens_and_abbrevs env
             }]

  | Val(id, t) ->
    let quals = d.quals in
    let t = desugar_term env (close_fun env t) in
    let quals =
        if Env.iface env
        && Env.admitted_iface env
        then Assumption::quals
        else quals in
    let lid = qualify env id in
    let se = { sigel = Sig_declare_typ {lid; us=[]; t};
               sigquals = List.map (trans_qual None) quals;
               sigrng = d.drange;
               sigmeta = default_sigmeta  ;
               sigattrs = d_attrs;
               sigopts = None;
               sigopens_and_abbrevs = opens_and_abbrevs env } in
    let env = push_sigelt env se in
    env, [se]

  | Exception(id, t_opt) ->
    let t =
        match t_opt with
        | None -> fail_or env (try_lookup_lid env) C.exn_lid
        | Some term ->
            let t = desugar_term env term in
            U.arrow ([null_binder t]) (mk_Total <| fail_or env (try_lookup_lid env) C.exn_lid)
    in
    let l = qualify env id in
    let qual = [ExceptionConstructor] in
    let top_attrs = d_attrs in
    let se = { sigel = Sig_datacon {lid=l;us=[];t;ty_lid=C.exn_lid;num_ty_params=0;mutuals=[C.exn_lid];injective_type_params=false};
               sigquals = qual;
               sigrng = d.drange;
               sigmeta = default_sigmeta  ;
               sigattrs = top_attrs;
               sigopts = None;
               sigopens_and_abbrevs = opens_and_abbrevs env } in
    let se' = { sigel = Sig_bundle {ses=[se]; lids=[l]};
                sigquals = qual;
                sigrng = d.drange;
                sigmeta = default_sigmeta  ;
                sigattrs = top_attrs;
                sigopts = None;
                sigopens_and_abbrevs = opens_and_abbrevs env } in
    let env = push_sigelt env se' in
    let data_ops = mk_data_projector_names [] env se in
    let discs = mk_data_discriminators [] env [l] top_attrs in
    let env = List.fold_left push_sigelt env (discs@data_ops) in
    env, se'::discs@data_ops

  | NewEffect (RedefineEffect(eff_name, eff_binders, defn)) ->
    let quals = d.quals in
    desugar_redefine_effect env d d_attrs trans_qual quals eff_name eff_binders defn

  | NewEffect (DefineEffect(eff_name, eff_binders, eff_typ, eff_decls)) ->
    let quals = d.quals in
    desugar_effect env d d_attrs quals false eff_name eff_binders eff_typ eff_decls

  | LayeredEffect (DefineEffect (eff_name, eff_binders, eff_typ, eff_decls)) ->
    let quals = d.quals in
    desugar_effect env d d_attrs quals true eff_name eff_binders eff_typ eff_decls

  | LayeredEffect (RedefineEffect _) ->
    failwith "Impossible: LayeredEffect (RedefineEffect _) (should not be parseable)"

  | SubEffect l ->
    let src_ed = lookup_effect_lid env l.msource d.drange in
    let dst_ed = lookup_effect_lid env l.mdest d.drange in
    let top_attrs = d_attrs in
    if not (U.is_layered src_ed || U.is_layered dst_ed)
    then let lift_wp, lift = match l.lift_op with
           | NonReifiableLift t -> Some ([],desugar_term env t), None
           | ReifiableLift (wp, t) -> Some ([],desugar_term env wp), Some([], desugar_term env t)
           | LiftForFree t -> None, Some ([],desugar_term env t)
         in
         let se = { sigel = Sig_sub_effect({source=src_ed.mname;
                                            target=dst_ed.mname;
                                            lift_wp=lift_wp;
                                            lift=lift;
                                            kind=None});
                    sigquals = [];
                    sigrng = d.drange;
                    sigmeta = default_sigmeta  ;
                    sigattrs = top_attrs;
                    sigopts = None;
                    sigopens_and_abbrevs = opens_and_abbrevs env } in
         env, [se]
    else
      (match l.lift_op with
       | NonReifiableLift t ->
         let sub_eff = {
           source = src_ed.mname;
           target = dst_ed.mname;
           lift_wp = None;
           lift = Some ([], desugar_term env t);
           kind = None
         } in
         env, [{
           sigel = Sig_sub_effect sub_eff;
           sigquals = [];
           sigrng = d.drange;
           sigmeta = default_sigmeta;
           sigattrs = top_attrs;
           sigopts = None;
           sigopens_and_abbrevs = opens_and_abbrevs env}]
       | _ -> failwith "Impossible! unexpected lift_op for lift to a layered effect")

  | Polymonadic_bind (m_eff, n_eff, p_eff, bind) ->
    let m = lookup_effect_lid env m_eff d.drange in
    let n = lookup_effect_lid env n_eff d.drange in
    let p = lookup_effect_lid env p_eff d.drange in
    let top_attrs = d_attrs in
    env, [{
      sigel = Sig_polymonadic_bind {
        m_lid=m.mname;
        n_lid=n.mname;
        p_lid=p.mname;
        tm=([], desugar_term env bind);
        typ=([], S.tun);
        kind=None };
      sigquals = [];
      sigrng = d.drange;
      sigmeta = default_sigmeta;
      sigattrs = top_attrs;
      sigopts = None;
      sigopens_and_abbrevs = opens_and_abbrevs env }]

  | Polymonadic_subcomp (m_eff, n_eff, subcomp) ->
    let m = lookup_effect_lid env m_eff d.drange in
    let n = lookup_effect_lid env n_eff d.drange in
    let top_attrs = d_attrs in    
    env, [{
      sigel = Sig_polymonadic_subcomp {
        m_lid=m.mname;
        n_lid=n.mname;
        tm=([], desugar_term env subcomp);
        typ=([], S.tun);
        kind=None };
      sigquals = [];
      sigrng = d.drange;
      sigmeta = default_sigmeta;
      sigattrs = top_attrs;
      sigopts = None;
      sigopens_and_abbrevs = opens_and_abbrevs env }]

  | Splice (is_typed, ids, t) ->
    let ids =
      if d.interleaved
      then []
      else ids
    in
    let t = desugar_term env t in
    let top_attrs = d_attrs in    
    let se = { sigel = Sig_splice {is_typed; lids=List.map (qualify env) ids; tac=t};
               sigquals = List.map (trans_qual None) d.quals;
               sigrng = d.drange;
               sigmeta = default_sigmeta;
               sigattrs = top_attrs;
               sigopts = None;
               sigopens_and_abbrevs = opens_and_abbrevs env } in
    let env = push_sigelt env se in
    env, [se]

  | UseLangDecls _ ->
    env, []

  | Unparseable ->
    raise_error d Errors.Fatal_SyntaxError "Syntax error"

  | DeclSyntaxExtension (extension_name, code, _, range) -> (
    let extension_parser = FStarC.Parser.AST.Util.lookup_extension_parser extension_name in
    match extension_parser with
    | None ->
      raise_error range Errors.Fatal_SyntaxError
         (BU.format1 "Unknown syntax extension %s" extension_name)
    | Some parser ->
      let open FStarC.Parser.AST.Util in
      let opens = {
        open_namespaces = open_modules_and_namespaces env;
        module_abbreviations = module_abbrevs env
      } in
      match parser.parse_decl opens code range with
      | Inl error ->
        raise_error error.range Errors.Fatal_SyntaxError error.message
      | Inr d' ->
        let quals = d'.quals @ d.quals in
        let attrs = d'.attrs @ d.attrs in
        desugar_decl_maybe_fail_attr env { d' with quals; attrs; drange=d.drange; interleaved=d.interleaved }
  )

  | DeclToBeDesugared tbs -> (
    match lookup_extension_tosyntax tbs.lang_name with
    | None -> 
      raise_error d Errors.Fatal_SyntaxError
        (BU.format1 "Could not find desugaring callback for extension %s" tbs.lang_name)
    | Some desugar ->
      let mk_sig sigel = 
        let top_attrs = d_attrs in
        let sigel =
          if d.interleaved
          then (
            match sigel with
            | Sig_splice s -> Sig_splice { s with lids = [] }
            | _ -> sigel
          )
          else sigel
        in
        let se = { 
            sigel;
            sigquals = List.map (trans_qual None) d.quals;
            sigrng = d.drange;
            sigmeta = default_sigmeta;
            sigattrs = top_attrs;
            sigopts = None;
            sigopens_and_abbrevs = opens_and_abbrevs env
          } 
        in
        se
      in
      let lids = List.map (qualify env) tbs.idents in
      let sigelts' = desugar env tbs.blob lids d.drange in
      let sigelts = List.map mk_sig sigelts' in
      let env = List.fold_left push_sigelt env sigelts in
      env, sigelts
  )

let desugar_decls env decls =
  let env, sigelts =
    List.fold_left (fun (env, sigelts) d ->
      let env, se = desugar_decl env d in
      env, List.rev_append se sigelts) (env, []) decls
  in
  env, List.rev sigelts

(* Top-level functionality: from AST to a module
   Keeps track of the name of variables and so on (in the context)
 *)
let desugar_modul_common (curmod: option S.modul) env (m:AST.modul) : env_t & Syntax.modul & bool =
  let env = match curmod, m with
    | None, _ ->
        env
    | Some ({ name = prev_lid }), Module (current_lid, _)
      when lid_equals prev_lid current_lid && Options.interactive () ->
        // If we're in the interactive mode reading the contents of an fst after
        // desugaring the corresponding fsti, don't finish the fsti
        env
    | Some prev_mod, _ ->
        fst (Env.finish_module_or_interface env prev_mod) in
  let (env, pop_when_done), mname, decls, intf = match m with
    | Interface(mname, decls, admitted) ->
      Env.prepare_module_or_interface true admitted env mname Env.default_mii, mname, decls, true
    | Module(mname, decls) ->
      Env.prepare_module_or_interface false false env mname Env.default_mii, mname, decls, false in
  let env, sigelts = desugar_decls env decls in
  let modul = {
    name = mname;
    declarations = sigelts;
    is_interface=intf
  } in
  env, modul, pop_when_done

let as_interface (m:AST.modul) : AST.modul =
    match m with
    | AST.Module(mname, decls) -> AST.Interface(mname, decls, true)
    | i -> i

let desugar_partial_modul curmod (env:env_t) (m:AST.modul) : env_t & Syntax.modul =
  let m =
    if Options.interactive () &&
      List.mem (get_file_extension (List.hd (Options.file_list ()))) ["fsti"; "fsi"]
    then as_interface m
    else m
  in
  let env, modul, pop_when_done = desugar_modul_common curmod env m in
  if pop_when_done then Env.pop (), modul
  else env, modul

let desugar_modul env (m:AST.modul) : env_t & Syntax.modul =
  Errors.with_ctx ("While desugaring module " ^ Class.Show.show (lid_of_modul m)) (fun () ->
    let env, modul, pop_when_done = desugar_modul_common None env m in
    let env, modul = Env.finish_module_or_interface env modul in
    if Options.dump_module (string_of_lid modul.name)
    then BU.print1 "Module after desugaring:\n%s\n" (show modul);
    (if pop_when_done then export_interface modul.name env else env), modul
  )

/////////////////////////////////////////////////////////////////////////////////////////
//External API for modules
/////////////////////////////////////////////////////////////////////////////////////////
let with_options (f:unit -> 'a) : 'a =
  let light, r =
    Options.with_saved_options (fun () ->
      let r = f () in
      let light = Options.ml_ish () in
      light, r
    )
  in
  if light then Options.set_ml_ish ();
  r

let ast_modul_to_modul modul : withenv S.modul =
    fun env ->
        with_options (fun () ->
        let e, m = desugar_modul env modul in
        m, e)

let decls_to_sigelts decls : withenv S.sigelts =
    fun env ->
        with_options (fun () ->
        let env, sigelts = desugar_decls env decls in
        sigelts, env)

let partial_ast_modul_to_modul modul a_modul : withenv S.modul =
    fun env ->
        with_options (fun () ->
        let env, modul = desugar_partial_modul modul env a_modul in
        modul, env)

let add_modul_to_env_core (finish: bool) (m:Syntax.modul)
                     (mii:module_inclusion_info)
                     (erase_univs:S.term -> S.term) : withenv unit =
  fun en ->
      let erase_univs_ed ed =
          let erase_binders bs =
              match bs with
              | [] -> []
              | _ ->
                let t = erase_univs (S.mk (Tm_abs {bs; body=S.t_unit; rc_opt=None}) Range.dummyRange) in
                match (Subst.compress t).n with
                | Tm_abs {bs} -> bs
                | _ -> failwith "Impossible"
          in
          let binders, _, binders_opening =
              Subst.open_term' (erase_binders ed.binders) S.t_unit in
          let erase_term t =
              Subst.close binders (erase_univs (Subst.subst binders_opening t))
          in
          let erase_tscheme (us, t) =
              let t = Subst.subst (Subst.shift_subst (List.length us) binders_opening) t in
              [], Subst.close binders (erase_univs t)
          in
          let erase_action action =
              let opening = Subst.shift_subst (List.length action.action_univs) binders_opening in
              let erased_action_params =
                  match action.action_params with
                  | [] -> []
                  | _ ->
                    let bs = erase_binders <| Subst.subst_binders opening action.action_params in
                    let t = S.mk (Tm_abs {bs; body=S.t_unit; rc_opt=None}) Range.dummyRange in
                    match (Subst.compress (Subst.close binders t)).n with
                    | Tm_abs {bs} -> bs
                    | _ -> failwith "Impossible"
              in
              let erase_term t =
                  Subst.close binders (erase_univs (Subst.subst opening t))
              in
                { action with
                    action_univs = [];
                    action_params = erased_action_params;
                    action_defn = erase_term action.action_defn;
                    action_typ = erase_term action.action_typ
                }
          in
            { ed with
              univs         = [];
              binders       = Subst.close_binders binders;
              signature     = U.apply_eff_sig erase_tscheme ed.signature;
              combinators   = apply_eff_combinators erase_tscheme ed.combinators;
              actions       = List.map erase_action ed.actions
          }
      in
      let push_sigelt env se =
          match se.sigel with
          | Sig_new_effect ed ->
            let se' = {se with sigel=Sig_new_effect (erase_univs_ed ed)} in
            let env = Env.push_sigelt env se' in
            push_reflect_effect env se.sigquals ed.mname se.sigrng
          | _ -> Env.push_sigelt env se
      in
      let en, pop_when_done = Env.prepare_module_or_interface false false en m.name mii in
      let en = List.fold_left
                    push_sigelt
                    (Env.set_current_module en m.name)
                    m.declarations in
      let en = if finish then Env.finish en m else en in
      (), (if pop_when_done then export_interface m.name en else en)

let add_partial_modul_to_env = add_modul_to_env_core false
let add_modul_to_env = add_modul_to_env_core true
