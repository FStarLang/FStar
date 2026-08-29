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
open FStarC
open FStarC.Effect
open FStarC.List
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
open FStarC.Class.Setlike
open FStarC.Class.Show
open FStarC.Syntax.Print {}
open FStarC.ToSyntax.TickedVars

module C   = FStarC.Parser.Const
module S   = FStarC.Syntax.Syntax
module U   = FStarC.Syntax.Util
module BU  = FStarC.Util
module Env = FStarC.Syntax.DsEnv
module EMB = FStarC.Syntax.Embeddings
module SS  = FStarC.Syntax.Subst

let extension_tosyntax_table 
  : SMap.t extension_tosyntax_decl_t
  = SMap.create 20

let register_extension_tosyntax
    (lang_name:string)
    (cb:extension_tosyntax_decl_t)
: ML unit
= SMap.add extension_tosyntax_table lang_name cb

let lookup_extension_tosyntax
    (lang_name:string)
: ML _
= SMap.try_find extension_tosyntax_table lang_name

let dbg_attrs    = Debug.get_toggle "attrs"
let dbg_ToSyntax = Debug.get_toggle "ToSyntax"

type antiquotations_temp = list (bv & S.term)

let tun_r (r:Range.t) : ML S.term = { tun with pos = r }

type annotated_pat = Syntax.pat & list (bv & Syntax.typ & list S.term)

let mk_thunk e =
  let b = S.mk_binder (S.new_bv None S.tun) in
  U.abs [b] e None

let mk_binder_with_attrs bv aq attrs : ML _ = 
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
let qualify_field_names record_or_dc_lid field_names : ML _ =
    let qualify_to_record l =
        let ns = ns_of_lid record_or_dc_lid in
        Ident.lid_of_ns_and_id ns (ident_of_lid l)
    in
    let _, field_names_rev =
      List.fold_left
        (fun (ns_opt, out) l ->
          match nsstr l with
          | "" ->
            if Some? ns_opt
            then (ns_opt, qualify_to_record l::out)
            else (ns_opt, l::out)

          | ns ->
            match ns_opt with
            | Some ns' ->
              if ns <> ns'
              then raise_error l Errors.Fatal_MissingFieldInRecord
                     (Format.fmt2 "Field %s of record type was expected to be scoped to namespace %s" (show l) ns')
              else (
                ns_opt, qualify_to_record l :: out
              )

            | None ->
              Some ns, qualify_to_record l :: out)
        (None, [])
        field_names
    in
    List.rev field_names_rev

let desugar_disjunctive_pattern annotated_pats when_opt branch : ML _ =
    annotated_pats |> List.map (fun (pat, annots) ->
        let branch = List.fold_left (fun br (bv, ty, _) ->
                        let lb = U.mk_letbinding (Inl bv) [] ty C.effect_Tot_lid (S.bv_to_name bv) [] br.pos in
                        let branch = SS.close [S.mk_binder bv] branch in
                        mk (Tm_let {lbs=(false, [lb]); body=branch}) br.pos) branch annots in
        U.branch(pat, when_opt, branch)
    )

let trans_qual (r:Range.t) maybe_effect_id (_x_:AST.qualifier) : ML _ = match _x_ with
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
  | AST.Inline
  | AST.Visible ->
    raise_error r Errors.Fatal_UnsupportedQualifier "Unsupported qualifier"

let as_imp (_x_:imp) : ML _ = match _x_ with
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
let rec is_comp_type env t : ML _ =
    match (unparen t).tm with
    (* we're right at the beginning of Prims, when (G)Tot isn't yet fully defined *)
    | Name l when lid_equals (Env.current_module env) C.prims_lid &&
                  (let s = string_of_id (ident_of_lid l) in
                   s = "Tot" || s = "GTot") ->
      true

    | Name l
    | Construct(l, _) -> Env.try_lookup_effect_name env l |> Some?
    | App(head, _, _) -> is_comp_type env head
    | Paren t -> failwith "impossible"
    | Ascribed(t, _, _, _)
    | LetOpen(_, t) -> is_comp_type env t
    | _ -> false

let unit_ty rng = mk_term (Name C.unit_lid) rng Type_level

type env_t = Env.env
type lenv_t = list bv

(* --- Type-based overloading: attaching candidate lists ---------------

   See FStarC.TypeChecker.Overload. When a name resolves to several
   top-level definitions we resolve it by scope order as usual (the
   innermost one wins) but record the shadowed alternatives on the fv,
   as [Unresolved_name alts]. The typechecker may later pick a different
   candidate, but only when the scope-order one is definitely
   type-incorrect, so a program that typechecks under scope-order
   resolution keeps its meaning.

   The qualifier is only ever attached to an fv that has no qualifier of
   its own; data constructors and record projectors keep their existing
   Data_ctor / Record_ctor / Record_projector qualifiers and are handled
   by the pre-existing Unresolved_constructor / Unresolved_projector
   machinery. *)

(* Only qualifier-less fvs (and fvs that already carry alternatives) take
   part in overloading. Data constructors and record projectors keep
   their own qualifiers and go through the pre-existing
   Unresolved_constructor / Unresolved_projector machinery. *)
let overloadable_qual (q:option fv_qual) : bool =
  match q with
  | None -> true
  | Some (Unresolved_name _) -> true
  | _ -> false

(* Record [alts] as the overloading candidates of [t]. Anything that is
   not an overloadable fvar is returned untouched. *)
let set_alternatives (t:S.term) (alts:list fv) : ML S.term =
  match alts with
  | [] -> t
  | _ ->
    match (SS.compress t).n with
    | Tm_fvar fv when overloadable_qual fv.fv_qual ->
      S.mk (Tm_fvar ({fv with fv_qual = Some (Unresolved_name alts)})) t.pos
    | _ -> t

(* Attach the alternatives that [l] resolves to, if [t] is indeed the
   primary candidate. If it is not (e.g. because the primary is a data
   constructor, which we filter out) we attach nothing: it is always
   sound to have fewer candidates. *)
let maybe_add_alternatives (env:env_t) (l:lid) (t:S.term) : ML S.term =
  match (SS.compress t).n with
  | Tm_fvar fv when None? fv.fv_qual ->
    begin match Env.try_lookup_lid_alternatives env l with
    | fv0 :: alts ->
      if Cons? alts && S.fv_eq fv fv0
      then set_alternatives t alts
      else t
    | _ -> t
    end
  | _ -> t

let desugar_name' setpos (env: env_t) (resolve: bool) (l: lid) : ML (option S.term) =
    let tm_attrs_opt =
        if resolve
        then Env.try_lookup_lid_with_attributes env l
        else Env.try_lookup_lid_with_attributes_no_resolve env l
    in
    match tm_attrs_opt with
    | None -> None
    | Some (tm, attrs) ->
        let tm = if resolve then maybe_add_alternatives env l tm else tm in
        let tm = setpos tm in
        Some tm

let desugar_name mk setpos env resolve l : ML _ =
    fail_or env (desugar_name' setpos env resolve) l

let compile_op_lid s r = [mk_ident(compile_op s r, r)] |> lid_of_ids

(* Some operators are notations for entities that have ordinary names,
   rather than operators defined under their mangled name. They are
   resolved here, if the mangled name is not in scope. *)
let op_as_term env op : ML (option S.term) =
  let r l = Some (S.lid_and_dd_as_fv (set_lid_range l (range_of_id op)) None |> S.fv_to_tm) in
  let fallback () =
    match Ident.string_of_id op with
    | "@" ->
      FStarC.Errors.log_issue op FStarC.Errors.Warning_DeprecatedGeneric [
          Errors.Msg.text "The operator '@' has been resolved to FStar.List.Tot.append even though \
                           FStar.List.Tot is not in scope. Please add an 'open FStar.List.Tot' to \
                           stop relying on this deprecated, special treatment of '@'."];
      r C.list_tot_append_lid

    | "~"   -> r C.not_lid
    | "=="  -> r C.eq2_lid
    | "<<" -> r C.precedes_lid
    | "/\\" -> r C.and_lid
    | "\\/" -> r C.or_lid
    | "==>" -> r C.imp_lid
    | "<==>" -> r C.iff_lid
    | _ -> None
  in
  let setpos t = {t with pos=(range_of_id op)} in
  match desugar_name' setpos env true (compile_op_lid (string_of_id op) (range_of_id op)) with
  | Some t -> Some t
  | None -> fallback()

let head_and_args_full t =
    let rec aux args t : ML _ = match (unparen t).tm with
        | App(t, arg, imp) -> aux ((arg,imp)::args) t
        | Construct(l, args') -> {tm=Name l; range=t.range; level=t.level}, args'@args
        | _ -> t, args in
    aux [] t

let rec uncurry bs t = match t.tm with
    | Product(binders, t) -> uncurry (bs@binders) t
    | _ -> bs, t

let rec is_var_pattern p = match p.pat with
  | PatWild _
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
  : ML (either ident lid              // name at the head
  & list pattern                  // arguments the head is applied to
  & option (term & option term))  // a possible (outermost) ascription on the pattern
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

let rec gather_pattern_bound_vars_maybe_top (acc : FlatSet.t ident) p : ML _ =
  let gather_pattern_bound_vars_from_list =
      List.fold_left gather_pattern_bound_vars_maybe_top acc
  in
  match p.pat with
  | PatWild _
  | PatConst _
  | PatVQuote _
  | PatName _
  | PatRest
  | PatOp _ -> acc
  | PatApp (phead, pats) -> gather_pattern_bound_vars_from_list (phead::pats)
  | PatVar (x, _, _) -> add x acc
  | PatList pats
  | PatTuple  (pats, _)
  | PatOr pats -> gather_pattern_bound_vars_from_list pats
  | PatRecord guarded_pats -> gather_pattern_bound_vars_from_list (List.map snd guarded_pats)
  | PatAscribed (pat, _) -> gather_pattern_bound_vars_maybe_top acc pat

let gather_pattern_bound_vars : (pattern -> ML (FlatSet.t Ident.ident)) =
  let acc = empty #ident () in
  fun p -> gather_pattern_bound_vars_maybe_top acc p

type bnd =
  | LocalBinder of bv     & S.bqual & list S.term  //binder attributes
  | LetBinder   of lident & (S.term & option S.term)

let is_implicit (b:bnd) : bool =
  match b with
  | LocalBinder (_, Some (S.Implicit _), _) -> true
  | _ -> false

let binder_of_bnd (_x_:bnd) : ML _ = match _x_ with
  | LocalBinder (a, aq, attrs) -> a, aq, attrs
  | _ -> failwith "Impossible"

(* TODO : shouldn't this be Tot by default ? *)
let mk_lb _x_ : ML _ = let (attrs, n, t, e, pos) = _x_ in {
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
let rec generalize_annotated_univs (s:sigelt) : ML sigelt =
  (* NB!! Order is very important here, so a definition like
      type t = Type u#a -> Type u#b
    gets is two universe parameters in the order in which
    they appear. So we do not use a set, and instead just use a mutable
    list that we update as we find universes. We also keep a set of 'seen'
    universes, whose order we do not care, just for efficiency. *)
  let vars : ref (list univ_name) = mk_ref [] in
  let seen : ref (RBSet.t univ_name) = mk_ref (empty ()) in
  let reg (u:univ_name) : ML unit =
    if not (mem u !seen) then (
      seen := add u !seen;
      vars := u::!vars
    )
  in
  let get () : ML (list univ_name) = List.rev !vars in

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
      | Sig_datacon {lid;t;ty_lid=tlid;num_ty_params=n;mutuals=lids;proj_disc_lids} ->
        { se with sigel = Sig_datacon {lid;
                                       us=unames;
                                       t=Subst.subst usubst t;
                                       ty_lid=tlid;
                                       num_ty_params=n;
                                       mutuals=lids;
                                       injective_type_params=false;
                                       proj_disc_lids;
                                      } }
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

  | Sig_new_effect _
  | Sig_sub_effect _
  | Sig_splice _
  | Sig_pragma _ ->
    s

let rec sum_to_universe u n =
    if n = 0 then u else U_succ (sum_to_universe u (n-1))

let int_to_universe n = sum_to_universe U_zero n

let rec desugar_maybe_non_constant_universe t
  : ML (either int Syntax.universe)  (* level of universe or desugared universe *)
=
  match (unparen t).tm with
  | Wild -> Inr U_unknown
  | Uvar u -> Inr (U_name u)

  | Const (Const_int (n, _)) ->
      if n < 0
      then raise_error t Errors.Fatal_NegativeUniverseConstNotSupported
             ("Negative universe constant  are not supported : " ^ show n);
      Inl n
  | Op (_op_plus, [t1 ; t2]) ->
      assert (Ident.string_of_id _op_plus = "+") ;
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
      let rec aux t univargs  : ML _ =
        match (unparen t).tm with
        | App(t, targ, _) ->
            let uarg = desugar_maybe_non_constant_universe targ in
            aux t (uarg::univargs)
        | Var _max_lid ->
            assert (Ident.string_of_lid _max_lid = "max") ;
            if List.existsb (function Inr _ -> true | _ -> false) univargs
            then Inr (U_max (List.map (function Inl n -> int_to_universe n | Inr u -> u) univargs))
            else
              let nargs = List.map (function Inl n -> n | Inr _ -> failwith "impossible") univargs in
              Inl (List.fold_left (fun m n -> if m > n then m else n) 0 nargs)
        (* TODO : Might not be the best place to raise the error... *)
        | _ -> raise_error t Errors.Fatal_UnexpectedTermInUniverse ("Unexpected term " ^ term_to_string t ^ " in universe context")
      in aux t []
  | _ -> raise_error t Errors.Fatal_UnexpectedTermInUniverse ("Unexpected term " ^ term_to_string t ^ " in universe context")

let desugar_universe t : ML Syntax.universe =
    let u = desugar_maybe_non_constant_universe t in
    match u with
        | Inl n -> int_to_universe n
        | Inr u -> u

let check_no_aq (aq : antiquotations_temp) : ML unit =
    match aq with
    | [] -> ()
    | (bv, { n = Tm_quoted (e, { qkind = Quote_dynamic })})::_ ->
        raise_error e Errors.Fatal_UnexpectedAntiquotation
          (Format.fmt1 "Unexpected antiquotation: `@(%s)" (show e))
    | (bv, e)::_ ->
        raise_error e Errors.Fatal_UnexpectedAntiquotation
          (Format.fmt1 "Unexpected antiquotation: `#(%s)" (show e))

let check_linear_pattern_variables pats (r:Range.t) : ML _ =
  // returns the set of pattern variables
  let rec pat_vars p : ML (RBSet.t bv) =
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
            raise_error duplicate_bv Errors.Fatal_NonLinearPatternNotPermitted
              (Format.fmt1 "Non-linear patterns are not permitted: ‘%s’ appears more than once in this pattern."
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
      raise_error first_nonlinear_var Errors.Fatal_IncoherentPatterns [
        text "Patterns in this match are incoherent.";
        text (Format.fmt1 "Variable %s is bound in some but not all patterns."
                       (show first_nonlinear_var.ppname));
      ]
    in
    List.iter aux ps

let smt_pat_lid (r:Range.t) = Ident.set_lid_range C.smtpat_lid r
let smt_pat_or_lid (r:Range.t) = Ident.set_lid_range C.smtpatOr_lid r

// [hoist_pat_ascription' pat] pulls [PatAscribed] nodes out of [pat]
// and construct a tuple that consists in a non-ascribed pattern and a
// type abscription.  Note [hoist_pat_ascription'] only works with
// patterns whose ascriptions live under tuple or list nodes. This
// function is used for [LetOperator] desugaring in
// [resugar_data_pat], because direct ascriptions in patterns are
// dropped (see issue #2678).
let rec hoist_pat_ascription' (pat: pattern): ML (pattern & option term)
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
    let lid =
      if dep
      then C.mk_dtuple_lid (List.length pats) pat.prange
      else C.mk_tuple_lid (List.length pats) pat.prange in
    handle_list
      (Var lid)
      (fun pats -> PatTuple (pats, dep)) pats
  | PatAscribed (pat, (typ, None)) -> pat, Some typ
  // if [pat] is not a list, a tuple or an ascription, we cannot
  // compose (at least not in a simple way) sub ascriptions, thus we
  // return the pattern directly
  | _ -> pat, None

let rest_pat_for_lid (env : env_t) (l : lid) : ML (list pattern) =
  let l, se = fail_or env (try_lookup_datacon env) l in
  match se.sigel with
  | Sig_datacon { t; num_ty_params } ->
    let bs, _ = U.arrow_formals t in
    (* drop the type parameters *)
    let _, bs = List.splitAt num_ty_params bs in
    bs |> List.map (fun b ->
      let q =
        match b.binder_qual with
        | Some (Syntax.Implicit _) -> Some Implicit
        | _ -> None
      in
      mk_pattern (PatWild (q, [])) (pos l))
  | _ ->
    failwith "unexpected: try_lookup_datacon returned odd sigelt"

let hoist_pat_ascription (pat: pattern): ML pattern
  = let pat, typ = hoist_pat_ascription' pat in
    match typ with
  | Some typ -> { pat with pat = PatAscribed (pat, (typ, None)) }
  | None     -> pat

(* [comp_requires t] is the [requires] clause of the AST computation type [t],
   if it has one and it is not trivially [True].  The triviality test must
   agree with [Syntax.Util.is_t_true] as applied in [desugar_comp], or a
   definition would acquire a binder that its [val] does not have. *)
let comp_requires (t:AST.term) : ML (option AST.term) =
  let is_true (t:AST.term) =
    match (unparen t).tm with
    | Name l | Var l ->
      let s = string_of_id (ident_of_lid l) in
      s = "True" || s = "l_True"
    | _ -> false
  in
  let _, args = head_and_args_full t in
  let is_req (a, _) = match (unparen a).tm with Requires _ -> true | _ -> false in
  match args |> BU.try_find is_req with
  | Some (a, _) ->
    (match (unparen a).tm with
     | Requires p when not (is_true p) -> Some p
     | _ -> None)
  | None -> None

(* [comp_drop_requires t] is the AST computation type [t] with its [requires]
   clause weakened to [True].  Used once the clause has been turned into a
   binder, so that it is not also re-checked as an assertion. *)
let comp_drop_requires (t:AST.term) : ML AST.term =
  let head, args = head_and_args_full t in
  let args = args |> List.map (fun (a, imp) ->
    match (unparen a).tm with
    | Requires _ ->
      let tru = mk_term (Name C.true_lid) a.range Formula in
      mk_term (Requires tru) a.range Type_level, imp
    | _ -> a, imp)
  in
  mkApp head args t.range

(* [mk_assert_before p e] is [let _ = _assert p in e]: it discharges [p] as a
   proof obligation at this point, and makes it available while checking [e].
   Used for the precondition of an ascription, which -- unlike that of an
   arrow -- cannot become a binder. *)
let mk_assert_before (p:S.term) (e:S.term) : ML S.term =
  let assertion =
    S.mk_Tm_app (S.fvar_with_dd (Ident.set_lid_range C.assert_lid p.pos) None)
                [S.as_arg p] p.pos
  in
  let x = S.new_bv (Some p.pos) S.t_unit in
  let lb = U.mk_letbinding (Inl x) [] S.t_unit C.effect_Tot_lid assertion [] p.pos in
  S.mk (Tm_let {lbs=(false, [lb]); body=Subst.close [S.mk_binder x] e}) e.pos

(* TODO : Patterns should be checked that there are no incompatible type ascriptions *)
(* and these type ascriptions should not be dropped !!!                              *)
let rec desugar_data_pat
    (top_level_ascr_allowed : bool)
    (env:env_t)
    (p:pattern)
    : ML ((env_t & bnd & list annotated_pat) & antiquotations_temp) =
  let resolvex (l:lenv_t) e x =
    (* This resolution function will be shared across
     * the cases of a PatOr, so different ocurrences of
     * a same (surface) variable are mapped to exactly the
     * same internal variable. *)
    match Option.find (fun y -> (string_of_id y.ppname = string_of_id x)) l with
    | Some y -> l, e, y
    | _ ->
      let e, xbv = push_bv e x in
      (xbv::l), e, xbv
  in

  let rec aux' (top:bool) (loc:lenv_t) (aqs:antiquotations_temp) (env:env_t) (p:pattern)
    : ML (lenv_t                                  (* list of all BVs mentioned *)
    & antiquotations_temp                     (* updated antiquotations_temp *)
    & env_t                                   (* env updated with the BVs pushed in *)
    & bnd                                     (* a binder for the pattern *)
    & pat                                     (* elaborated pattern *)
    & list (bv & Syntax.typ & list S.term))  (* ascripted pattern variables (collected) with attributes *)
    =
    let pos q = Syntax.withinfo q p.prange in
    let pos_r r q = Syntax.withinfo q r in
    let orig = p in
    match p.pat with
      | PatOr _ -> failwith "impossible: PatOr handled below"

      | PatOp op ->
        (* Turn into a PatVar and recurse *)
        let id_op = mk_ident (compile_op (string_of_id op) (range_of_id op), (range_of_id op)) in
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

      | PatVar (x, aq, attrs) ->
        let aq = trans_bqual env aq in
        let attrs = attrs |> List.map (desugar_term env) in
        let loc, env, xbv = resolvex loc env x in
        loc, aqs, env, LocalBinder(xbv, aq, attrs), pos <| Pat_var xbv, []

      | PatName l ->
        let l, _ = fail_or env (try_lookup_datacon env) l in
        let x = S.new_bv (Some p.prange) (tun_r p.prange) in
        loc, aqs, env, LocalBinder(x,  None, []), pos <| Pat_cons(l, None, []), []

      (* Detect matches of the form
           | C ..
         We simply elaborate the pattern to `C _ _` (with
         as many underscores as needed).
      *)
      | PatApp({pat=PatName l}, [{ pat = PatRest }]) ->
        let PatApp (hd, _) = p.pat in
        let argpats = rest_pat_for_lid env l in
        let newpat : pattern =
          mk_pattern (PatApp (hd, argpats)) p.prange
        in
        aux' top loc aqs env newpat

      | PatRest ->
        raise_error p Errors.Fatal_UnexpectedPattern [
          text "Unexpected pattern.";
          text "Using `..` is only allowed as argument to a data constructor, e.g. `C ..`.";
        ]

      | PatApp({pat=PatName l}, args) ->
        let loc, aqs, env, annots, args = List.fold_right (fun arg (loc, aqs, env, annots, args) ->
          let loc, aqs, env, b, arg, ans = aux loc aqs env arg in
          let imp = is_implicit b in
          (loc, aqs, env, ans@annots, (arg, imp)::args)) args (loc, aqs, env, [], []) in
        let l, _ = fail_or env  (try_lookup_datacon env) l in
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
            match try_lookup_record_by_field_name_many env field_names with
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
  and aux loc aqs env p : ML _ = aux' false loc aqs env p
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
  : ML ((env_t                 (* environment with patterns variables pushed in *)
  & bnd                    (* a binder for the pattern *)
  & list annotated_pat)    (* elaborated patterns with their variable annotations *)
  & antiquotations_temp)    (* antiquotations_temp found in binder types *)
  =

  if top then
    let mklet x ty (tacopt : option S.term) : ML (env_t & bnd & list annotated_pat) =
        env, LetBinder(qualify env x, (ty, tacopt)), []
    in
    let op_to_ident x = mk_ident (compile_op (string_of_id x) (range_of_id x), (range_of_id x)) in
    match p.pat with
    | PatOp x ->
        mklet (op_to_ident x) (tun_r (range_of_id x)) None, []
    | PatVar (x, _, _) ->
        mklet x (tun_r (range_of_id x)) None, []
    | PatAscribed({pat=PatOp x}, (t, tacopt)) ->
        let tacopt = Option.map (desugar_term env) tacopt in
        let t, aq = desugar_term_aq env t in
        mklet (op_to_ident x) t tacopt, aq
    | PatAscribed({pat=PatVar (x, _, _)}, (t, tacopt)) ->
        let tacopt = Option.map (desugar_term env) tacopt in
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

and desugar_binding_pat_aq env p : ML _ = desugar_binding_pat_maybe_top false env p

and desugar_match_pat_maybe_top _ env pat : ML _ =
  let (env, _, pat), aqs = desugar_data_pat false env pat in
  (env, pat), aqs

and desugar_match_pat env p : ML _ = desugar_match_pat_maybe_top false env p

and desugar_term_aq env e : ML (S.term & antiquotations_temp) =
    let env = Env.set_expect_typ env false in
    desugar_term_maybe_top false env e

and desugar_term env e : ML S.term =
    let t, aq = desugar_term_aq env e in
    check_no_aq aq;
    t

and desugar_typ_aq env e : ML (S.term & antiquotations_temp) =
    let env = Env.set_expect_typ env true in
    desugar_term_maybe_top false env e

and desugar_typ env e : ML S.term =
    let t, aq = desugar_typ_aq env e in
    check_no_aq aq;
    t

and desugar_machine_integer env (repr:int) (base:int_base) (_sw_:(FStarC.Const.signedness & FStarC.Const.width)) range : ML _ = let (signedness, width) = _sw_ in
  let tnm = if width = Sizet then "FStar.SizeT" else
    "FStar." ^
    (match signedness with | Unsigned -> "U" | Signed -> "") ^ "Int" ^
    (match width with | Int8 -> "8" | Int16 -> "16" | Int32 -> "32" | Int64 -> "64")
  in
  //we do a static check of integer constants
  //and coerce them to the appropriate type using the internal coercion
  // __uint_to_t or __int_to_t
  //Rather than relying on a verification condition to check this trivial property
  (* Note: the authoritative check is in FStarC.TypeChecker.TcTerm.tc_constant;
     this one only exists to give a good error message on the source syntax. *)
  if not (within_bounds repr signedness width)
  then FStarC.Errors.log_issue range Errors.Error_OutOfRange
         (Format.fmt2 "%s is not in the expected range for %s"
            (string_of_int_literal repr base) tnm);
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
        (Format.fmt1 "Unexpected numeric literal.  Restart F* to load %s." tnm) in
  let repr' = S.mk (Tm_constant (Const_int (repr, base))) range in
  let app = S.mk_Tm_app lid [repr', S.as_aqual_implicit false] range in
  S.mk (Tm_meta {tm=app;
                 meta=Meta_desugared (Machine_integer (signedness, width))}) range

and desugar_term_maybe_top (top_level:bool) (env:env_t) (top:term) : ML (S.term & antiquotations_temp) =
  let mk e = S.mk e top.range in
  let noaqs = [] in
  let join_aqs aqs = List.flatten aqs in
  let setpos e = {e with pos=top.range} in
  let desugar_binders env binders : ML _ =
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
    Format.print1 "desugaring (%s)\n\n" (show top);
  begin match (unparen top).tm with
    | Wild -> setpos tun, noaqs

    | Labeled _ -> desugar_formula env top, noaqs

    | Requires t ->
      desugar_formula env t, noaqs

    | Ensures t ->
      desugar_formula env t, noaqs

    | Attributes ts ->
        failwith "Attributes should not be desugared by desugar_term_maybe_top"
        // desugar_attributes env ts

    | Const (Const_machine_int (i, b, sw, w)) ->
        desugar_machine_integer env i b (sw, w) top.range, noaqs

    | Const c ->
        mk (Tm_constant c), noaqs

    | Op(id, args) when string_of_id id = "=!=" ->
      let r = range_of_id id in
      let e = mk_term (Op(Ident.mk_ident ("==", r), args)) top.range top.level in
      desugar_term_aq env (mk_term(Op(Ident.mk_ident ("~",r), [e])) top.range top.level)

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
      match op_as_term env s with
      | None ->
        raise_error s Errors.Fatal_UnexpectedOrUnboundOperator
                    ("Unexpected or unbound operator: " ^
                     Ident.string_of_id s)
      | Some op ->
            if Cons? args then
              let args, aqs = args |> List.map (fun t -> let t', s = desugar_term_aq env t in
                                                         (t', None), s) |> List.unzip in
              S.mk_Tm_app op args top.range, join_aqs aqs
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
        raise_error top Errors.Fatal_EffectNotFound (Format.fmt1 "Data constructor or effect %s not found" (string_of_lid l))
      end

    | Discrim lid ->
      begin match Env.try_lookup_datacon env lid with
      | None ->
        raise_error top Errors.Fatal_DataConstructorNotFound (Format.fmt1 "Data constructor %s not found" (string_of_lid lid))
      | _ ->
        let lid' = U.mk_discriminator lid in
        desugar_name mk setpos env true lid', noaqs
      end

    | Construct(l, args) ->
        begin match Env.try_lookup_datacon env l with
        | Some (head, _) ->
            let head = mk (Tm_fvar head) in
            begin match args with
              | [] -> head, noaqs
              | _ ->
                let universes, args = BU.take (fun (_, imp) -> imp = UnivApp) args in
                let universes = List.map (fun x -> desugar_universe (fst x)) universes in
                (* The element type is given explicitly: inferring it makes
                   the result type of the lambda -- which carries the [==] fact
                   for the pair, mentioning [te] -- the solution of a unification
                   variable bound outside the lambda. *)
                let args, aqs =
                  List.map #_ #(S.arg & antiquotations_temp)
                    (fun (t, imp) ->
                      let te, aq = desugar_term_aq env t in
                      arg_withimp_t imp te, aq)
                    args
                  |> List.unzip in
                let head = if universes = [] then head else mk (Tm_uinst(head, universes)) in
                let tm =
                  if Nil? args
                  then head
                  else S.mk_Tm_app head args top.range in
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
      S.mk_Tm_app tup targs top.range, join_aqs aqs

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
      S.mk_Tm_app tup targs top.range, noaqs

    | Product(binders, t) ->
      let bs, t = uncurry binders t in
      let rec aux env aqs bs (_x_:list AST.binder) : ML _ = match _x_ with
        | [] ->
          let cod, pre = desugar_comp top.range true env t in
          (* A precondition on the codomain becomes a trailing implicit
             [squash] binder.  It goes last so that it may mention the
             explicit binders, and so that it is in scope as a hypothesis
             while the codomain's own well-formedness is checked. *)
          let bs =
            if U.is_t_true pre then bs
            else
              let x = S.new_bv (Some pre.pos) (U.mk_squash pre) in
              S.mk_binder_with_attrs x (Some S.imp_tag) None [] :: bs
          in
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
      let check_disjoint (sets : list (FlatSet.t ident)) : ML (option ident) =
        let rec aux acc sets : ML _ =
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
            text "The variable " ^/^ fquotes (pp id) ^/^ text " appears more than once in this function definition."
          ]
      end;

      let binders = binders |> List.map replace_unit_pattern in
      let _, ftv = List.fold_left (fun (env, ftvs) pat ->
        match pat.pat with
          | PatAscribed(_, (t, None)) -> env, free_ticked_vars env t@ftvs
          | PatAscribed(_, (t, Some tac)) -> env, free_ticked_vars env t@free_ticked_vars env tac@ftvs
          | _ -> env, ftvs) (env, []) binders in
      let ftv = Class.Ord.sort_dedup ftv in
      let binders = (ftv |> List.map (fun a ->
                        mk_pattern (PatVar(a, Some AST.Implicit, [])) top.range))
                    @binders in //close over the free type variables
      (*
         fun (P1 x1) (P2 x2) (P3 x3) -> e

            is desugared to

         fun y1 y2 y3 -> match (y1, y2, y3) with
                | (P1 x1, P2 x2, P3 x3) -> [[e]]
      *)
      let rec aux aqs env bs sc_pat_opt pats : ML (S.term & antiquotations_temp) =
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
                  raise_error p Errors.Fatal_UnsupportedDisjunctivePatterns [
                    text "Disjunctive patterns are not supported in abstractions";
                  ]
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
                            let sc = S.mk_Tm_app (mk (Tm_fvar tup2))
                                                 [as_arg sc; as_arg <| S.bv_to_name x] top.range in
                            let p = withinfo (Pat_cons(tup2, None, [(p', false);(p, false)])) (Range.union_ranges p'.p p.p) in
                            Some(sc, p)
                          | Tm_app _, Pat_cons(_, _, pats) ->
                            let _, args = U.head_and_args_full sc in
                            let tupn = S.lid_and_dd_as_fv (C.mk_tuple_data_lid (1 + List.length args) top.range) (Some Data_ctor) in
                            let sc = S.mk_Tm_app (mk (Tm_fvar tupn))
                                                 (args@[as_arg <| S.bv_to_name x]) top.range in
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
       let rec aux universes e : ML _ = match (unparen e).tm with
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
      log_issue top.range Warning_DeprecatedLightDoNotation [
        text "The lightweight do notation [x <-- y; z] or [x ;; z] is deprecated.";
        text "Use let operators (i.e. [let* x = y in z] or [y ;* z], [*] being any sequence of operator characters) instead.";
      ];
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
      let t = mk_term (Let(LocalNoLetQualifier, [None, (p, t1)], t2)) top.range Expr in
      let tm, s = desugar_term_aq env t in

      //
      // keep the Sequence, we will use it for resugaring
      //
      mk (Tm_meta {tm; meta=Meta_desugared Sequence}), s

    | LetOpen (lid, e) ->
      let env = Env.push_namespace env lid Unrestricted in
      if Env.expect_typ env then desugar_typ_aq env e else desugar_term_aq env e

    | LetOpenRecord (r, rty, e) ->
      let rec head_of (t:term) : ML term =
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
            (Format.fmt1 "This type must be a (possibly applied) record name: %s" (term_to_string rty))
      in
      let record =
        match Env.try_lookup_record_type env tycon_name with
        | Some r -> r
        | None ->
          raise_error rty Errors.Error_BadLetOpenRecord
            (Format.fmt1 "Not a record type: ‘%s’" (term_to_string rty))
      in
      let constrname = lid_of_ns_and_id (ns_of_lid record.typename) record.constrname in
      let mk_pattern p = mk_pattern p r.range in
      let elab =
        let pat =
          mk_pattern (PatApp (mk_pattern (PatName constrname),
                              List.map (fun (field, is_imp, _) -> mk_pattern (PatVar (field, (if is_imp then Some Implicit else None), []))) record.fields))
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
      let is_rec = qual = LocalRec in
      if not is_rec && List.length lbs > 1 then (
        let lb = List.nth lbs 1 in
        raise_error lb._2._1 Errors.Fatal_MultipleLetBinding
          "Multiple 'let' bindings are only allowed in 'let rec'"
      );
      let extra_attrs =
        if qual = LocalUnfold
        then [inline_let_attribute; inline_let_vc_attribute]
        else []
      in
      let add_extra_attrs attrs =
        match attrs, extra_attrs with
        | _, [] -> attrs
        | None, _ -> Some extra_attrs
        | Some attrs, _ -> Some (attrs @ extra_attrs)
      in
      let ds_let_rec_or_app () =
        let bindings = lbs in
        let funs = bindings |> List.map (fun (attr_opt, (p, def)) ->
          if is_app_pattern p
          then add_extra_attrs attr_opt, destruct_app_pattern env top_level p, def
          else match un_function p def with
                | Some (p, def) ->
                  add_extra_attrs attr_opt, destruct_app_pattern env top_level p, def
                | _ -> begin
                  match p.pat with
                  | PatAscribed({pat=PatVar(id,_,_)}, t) ->
                    if top_level
                    then add_extra_attrs attr_opt, (Inr (qualify env id), [], Some t), def
                    else add_extra_attrs attr_opt, (Inl id, [], Some t), def
                  | PatVar(id, _, _) ->
                    if top_level
                    then add_extra_attrs attr_opt, (Inr (qualify env id), [], None), def
                    else add_extra_attrs attr_opt, (Inl id, [], None), def
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
                let dummy_ref = mk_ref true in
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
        let desugar_one_def env lbname _x_one_def_
            : ML (letbinding & antiquotations_temp)
            =
            let (attrs_opt, (_, args, result_t), def) = _x_one_def_ in
            let args = args |> List.map replace_unit_pattern in
            let pos = def.range in
            (* A [requires] on a definition's result computation type is the
               caller's obligation, exactly as in a [val]: it must become a
               trailing implicit binder of the function, not an assertion in
               its body.  Add the binder here; the ascription below then
               discharges its own (now redundant) assertion from it. *)
            let args, result_t =
              match result_t with
              | Some (t, tacopt) when Cons? args && is_comp_type env t ->
                (match comp_requires t with
                 | Some p ->
                   let r = p.range in
                   let sq = mkApp (mk_term (Var C.squash_lid) r Expr) [(p, Nothing)] r in
                   args @ [mk_pattern (PatAscribed (mk_pattern (PatWild (Some Implicit, [])) r,
                                                    (sq, None))) r],
                   (* the precondition is the binder's now, so drop it from the
                      ascription: re-asserting it would only obscure the type *)
                   Some (comp_drop_requires t, tacopt)
                 | None -> args, result_t)
              | _ -> args, result_t
            in
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
                              raise_error p Errors.Fatal_ComputationTypeNotAllowed [
                                text "Computation type annotations are only permitted on let-bindings \
                                      without inlined patterns.";
                                text "Suggestion: replace this pattern with a variable."
                              ] in
                         t
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
                             (fquotes (doc_of_string nm))
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
           if tacopt |> Some?
           then Errors.log_issue (tacopt |> Option.must) Errors.Warning_DefinitionNotTranslated
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
      let attrs = add_extra_attrs attrs in
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
      let asc, pre, aq0 = desugar_ascription env t tac_opt use_eq in
      let e, aq = desugar_term_aq env e in
      (* An ascription cannot bind anything, so its precondition is an
         obligation right here rather than a caller's duty -- which is what F*
         has always made of it.  Discharge it with an [assert], inside the
         ascription so that the ascription stays the outermost node: several
         passes (e.g. [TcUtil.extract_let_rec_annotation]) look for it there. *)
      let e = if U.is_t_true pre then e else mk_assert_before pre e in
      let tm = mk <| Tm_ascribed {tm=e; asc; eff_opt=None} in
      tm, aq0@aq

    | Record(_, []) ->
      raise_error top Errors.Fatal_UnexpectedEmptyRecord "Unexpected empty record"

    | Record(eopt, fields) ->
      (* Record literals have to wait for type information to be fully resolved *)
      let record_opt =
        let fns = List.map fst fields in
        try_lookup_record_by_field_name_many env fns
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
          { uc_base_term = Some? eopt;
            uc_typename = None;
            uc_fields = field_names }
        | Some record ->
          { uc_base_term = Some? eopt;
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
      S.mk_Tm_app head [as_arg e] top.range, s

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
                     (Format.fmt1 "Static quotation refers to external variables: %s" (show fvs))
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

      let is_impl (rel:term) : ML bool =
        let is_impl_t (t:S.term) : bool =
          match t.n with
          | Tm_fvar fv -> S.fv_eq_lid fv C.imp_lid
          | _ -> false
        in
        match (unparen rel).tm with
        | Op (id, _) ->
            begin match op_as_term env id with
            | Some t -> is_impl_t t
            | None -> false
            end

        | Var lid ->
            begin match desugar_name' (fun x->x) env true lid with
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
        let xt = mk_term (Var (Ident.id_as_lid x)) rel.range Expr in
        let yt = mk_term (Var (Ident.id_as_lid y)) rel.range Expr in
        let pats = [mk_pattern (PatVar (x, None, [])) rel.range; mk_pattern (PatVar (y, None,[])) rel.range] in
        mk_term (Abs (pats,
            mk_term (Ascribed (
                mkApp rel [(xt, Nothing); (yt, Nothing)] rel.range,
                mk_term (Name C.prop_lid) rel.range Expr,
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
      let rec aux bs : ML _ =
        match bs with
        | [] ->
          let sq_p = U.mk_squash p in
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
      let rec aux bs vs sub token : ML _ =
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

    | IntroImplies (p, q, e) ->
      let p = desugar_term env p in
      let q = desugar_term env q in
      let e = desugar_term env e in
      (* The hypothesis is no longer named; bind it to a fresh anonymous
         variable so that it is still available to the SMT solver. *)
      let x = S.mk_binder (S.new_bv (Some e.pos) S.tun) in
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
      let rec aux bs vs sub token : ML S.term =
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

    | ElimExists (bs, p, e) ->
      (*
         eliminate exists x1 ... xn. p
         with e
         desugars to
         let (| x1, (| ..., xn |) |) = indefinite_descriptionn (fun x1 ... xn -> p) in e
         using a single call whenever n <= max_indefinite_description_arity.
      *)
      let pat_of_binder (b:binder) : ML pattern =
        let v aq attrs x = mk_pattern (PatVar (x, aq, attrs)) b.brange in
        match b.b with
        | Variable x -> v b.aqual b.battributes x
        | Annotated (x, t) ->
          mk_pattern (PatAscribed (v b.aqual b.battributes x, (t, None))) b.brange
        | NoName _ ->
          raise_error b Fatal_UnexpectedTerm
            "Unexpected unnamed binder in 'eliminate exists'"
      in
      (* `indefinite_descriptionk` returns a right-nested chain of dependent
         pairs, so the binding pattern is nested to match. *)
      let rec nested_pat (pats:list pattern) (r:Range.range) : ML pattern =
        match pats with
        | [pat] -> pat
        | pat::pats -> mk_pattern (PatTuple ([pat; nested_pat pats r], true)) r
        | [] -> raise_error top Fatal_UnexpectedTerm "Empty binders in 'eliminate exists'"
      in
      let rec aux (bs:list binder) : ML term =
        match bs with
        | [] -> e
        | _ ->
          let n = List.length bs in
          (* Taking all the binders in one step is important. Chaining several
             calls is bad in two independent ways. First, the obligation of a
             non-final call is `exists x1 ... xk. (exists xk+1 ... xn. p)`, and
             the solver has no trigger for the outer existential that mentions
             the inner binders, so it falls back to a multi-pattern of the
             typing hypotheses of x1 ... xk and enumerates every k-tuple of
             terms of the right type (issue #4405). Second, each step restates
             the remaining existential as its own postcondition, and
             normalizing the resulting VC costs about 2x per extra step, so the
             elaboration time grows exponentially in the number of steps
             (issue #4444).

             Beyond max_indefinite_description_arity we have no combinator of
             the right arity, so we peel off one binder at a time: that at
             least keeps the trigger enumeration linear rather than
             exponential in k. *)
          let k = if n <= C.max_indefinite_description_arity
                  then n
                  else 1
          in
          let hd, tl = List.splitAt k bs in
          let r = List.fold_right (fun (b:binder) r -> Range.union_ranges b.brange r) hd p.range in
          let body =
            if Nil? tl then p
            else mk_term (QExists (tl, ([], []), p)) p.range Formula
          in
          let pred = mk_term (Abs (List.map pat_of_binder hd, body)) r Expr in
          let head = mk_term (Var (C.indefinite_description_lid k)) r Expr in
          let rhs = mkExplicitApp head [pred] r in
          let pat = nested_pat (List.map pat_of_binder hd) r in
          mk_term (Let (LocalNoLetQualifier, [(None, (pat, rhs))], aux tl)) top.range Expr
      in
      if Nil? bs
      then raise_error top Fatal_UnexpectedTerm "Empty binders in 'eliminate exists'"
      else desugar_term_maybe_top top_level env (aux bs)

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

    | ElimOr(p, q, e1, e2) ->
      (* eliminate p \/ q with e1 and e2  ~~>  if or_decide p q then e1 else e2 *)
      let r = Range.union_ranges p.range q.range in
      let head = mk_term (Var C.or_decide_lid) r Expr in
      let b = mkExplicitApp head [p; q] r in
      desugar_term_maybe_top top_level env
        (mk_term (If (b, None, None, e1, e2)) top.range Expr)

    | ElimAnd(p, q, e) ->
      (* eliminate p /\ q with e  ~~>  assert (p /\ q); e *)
      let r = Range.union_ranges p.range q.range in
      let conj = mk_term (Op (mk_ident ("/\\", r), [p; q])) r Formula in
      let a = mkExplicitApp (mk_term (Var C.assert_lid) r Expr) [conj] r in
      desugar_term_maybe_top top_level env
        (mk_term (Seq (a, e)) top.range Expr)

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

and desugar_match_returns env scrutinee asc_opt : ML _ =
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
    let asc, pre, aq = desugar_ascription env_asc asc_tc None asc_use_eq in
    if not (U.is_t_true pre) then
      raise_error asc_tc Errors.Fatal_NotSupported
        "A 'requires' clause is not supported in a match returns annotation";
    //if scrutinee is a name, it may appear in the ascription
    //  substitute it with the (new or annotated) binder
    let asc =
      match (scrutinee |> U.unascribe).n with
      | Tm_name sbv -> SS.subst_ascription [NT (sbv, S.bv_to_name b.binder_bv)] asc
      | _ -> asc in
    let asc = SS.close_ascription [b] asc in
    let b = List.hd (SS.close_binders [b]) in
    Some (b, asc), aq

and desugar_ascription env t tac_opt use_eq : ML (S.ascription & S.term & antiquotations_temp) =
  let annot, pre, aq0 =
    if is_comp_type env t
    then if use_eq
         then raise_error t Errors.Fatal_NotSupported "Equality ascription with computation types is not supported yet"
         else let comp, pre = desugar_comp t.range true env t in
              (Inr comp, pre, [])
    else let tm, aq = desugar_term_aq env t in
         (Inl tm, S.trivial_pre, aq) in
  (annot, Option.map (desugar_term env) tac_opt, use_eq), pre, aq0

and desugar_args env args : ML _ =
    args |> List.map (fun (a, imp) -> arg_withimp_t imp (desugar_term env a))

and desugar_comp r (allow_type_promotion:bool) env t : ML _ =
    let fail #a code msg : ML a = raise_error r code msg in
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
        let s = string_of_lid smtpat in
        s = "SMTPat" || s = "SMTPatT" || s = "SMTPatOr"

      | Var smtpat ->
        let s = string_of_lid smtpat in
        s = "smt_pat" || s = "smt_pat_or"

      | _ -> false
    in
    let is_smt_pat (t,_) =
      match (unparen t).tm with
      | ListLiteral ts -> BU.for_all is_smt_pat1 ts
      | _ -> false
    in
    let pre_process_comp_typ (t:AST.term) =
      let head, args = head_and_args_full t in
      match head.tm with
      | Name lemma when ((string_of_id (ident_of_lid lemma)) = "Lemma") ->
        (* need to add the unit result type and the empty smt_pat list, if n *)
        let unit_tm = mk_term (Name C.unit_lid) t.range Type_level, Nothing in
        let nil_pat = mk_term (Name C.nil_lid) t.range Expr, Nothing in
        let req_true =
          let req = Requires (mk_term (Name C.true_lid) t.range Formula) in
          mk_term req t.range Type_level, Nothing
        in
        let ens_true =
          let ens = Ensures (mk_term (Name C.true_lid) t.range Formula) in
          mk_term ens t.range Type_level, Nothing
        in
        (* The postcondition for Lemma is thunked, to allow to assume the precondition
         * (c.f. #57), so add the thunking here *)
        let thunk_ens (e, i) = (thunk e, i) in
        let fail_lemma #a () : ML a =
             let open FStarC.Pprint in
             let expected_one_of = ["Lemma post";
                                    "Lemma (requires pre)";
                                    "Lemma (ensures post)";
                                    "Lemma (requires pre) (ensures post)"] in
             raise_error t Errors.Fatal_InvalidLemmaArgument [
                text "Invalid arguments to 'Lemma'; expected one of the following"
                  ^^ sublist empty (List.map doc_of_string expected_one_of);
                text "each of which may additionally be followed by a (decreases d) clause and/or an [SMTPat ...] list."
             ]
        in
        (* The precondition and the postcondition are both optional (a missing
           one defaults to [True]), but at least one of them must be given.
           The postcondition may be written positionally, i.e. [Lemma post].
           A (decreases d) clause and an [SMTPat ...] list may be added to any
           of these forms, in any order. *)
        let args =
          let tagged_req, args = List.partition is_requires args in
          let tagged_ens, args = List.partition is_ensures args in
          let dec,        args = List.partition is_decreases args in
          let smtpat,     args = List.partition is_smt_pat args in
          (* Whatever is left over is the untagged postcondition, if any. *)
          let ens =
            match tagged_ens, args with
            | [ens], [] -> Some ens
            | [], [ens] -> Some ens
            | [], [] -> None
            | _ -> fail_lemma ()
          in
          let req =
            match tagged_req with
            | [] -> None
            | [req] -> Some req
            | _ -> fail_lemma ()
          in
          if None? req && None? ens then fail_lemma ();
          if List.length dec > 1 then fail_lemma ();
          let smtpat =
            match smtpat with
            | [] -> nil_pat
            | [p] -> p
            | _ -> fail_lemma ()
          in
          [unit_tm; Option.dflt req_true req; thunk_ens (Option.dflt ens_true ens); smtpat] @ dec
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
          (if Options.warn_default_effects()
           then FStarC.Errors.log_issue head Errors.Warning_UseDefaultEffect "Using default effect Tot";
           Const.effect_Tot_lid) in
        (Ident.set_lid_range default_effect head.range, []), [t, Nothing]

      | _ ->
        raise_error t Errors.Fatal_EffectNotFound "Expected an effect constructor"
    in
    let (eff, cattributes), args = pre_process_comp_typ t in
    if Nil? args then
      fail Errors.Fatal_NotEnoughArgsToEffect (Format.fmt1 "Not enough args to effect %s" (show eff));
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
    let rest0 = rest in
    let rest = desugar_args env rest in
    let decreases_clause = dec |>
      List.map (fun t -> match (unparen (fst t)).tm with
                      | Decreases t ->
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
    (* [Tot t] and [GTot t] with nothing else at all are the dedicated
       [Total]/[GTotal] comps.  Anything more -- a decreases clause, a
       specification, universes -- goes through the general path below, exactly
       like any other effect. *)
    if no_additional_args
       && (lid_equals eff C.effect_Tot_lid || lid_equals eff C.effect_GTot_lid)
    then (if lid_equals eff C.effect_Tot_lid then mk_Total result_typ else mk_GTotal result_typ),
         S.trivial_pre
    else
      let flags =
        if      lid_equals eff C.effect_Lemma_lid then [LEMMA]
        else if lid_equals eff C.effect_Tot_lid   then [TOTAL]
        else if lid_equals eff (C.effect_ML_lid()) then [MLEFFECT]
        else []
      in
      (* An effect abbreviation of [Tot] denotes a total computation just as
         much as [Tot] itself does, so give it the [TOTAL] flag: downstream
         tests such as [Syntax.Util.is_total_comp] see only the flags, and an
         abbreviation is not unfolded until the typechecker.  [Lemma] is the
         motivating case -- without this, a partially-applied lemma is not
         recognised as pure and its trailing implicit is never instantiated.
         The flag is dropped again below if this occurrence carries a
         specification. *)
      let flags =
        if List.existsb (function TOTAL -> true | _ -> false) flags then flags
        else match Env.try_lookup_root_effect_name env eff with
             | Some root when lid_equals root C.effect_Tot_lid -> TOTAL :: flags
             | _ -> flags
      in
      let flags = flags @ cattributes in
      (* Extract the precondition, the postcondition, and (for Lemma) the SMT patterns
         from the remaining arguments of the computation type. *)
      let pre, post, smtpat =
        if lid_equals eff C.effect_Lemma_lid
        then
          (* pre_process_comp_typ has normalized Lemma's arguments to [pre; post; pat] *)
          match rest with
          | [(pre, _); (post, _); (pat, _)] ->
            let pat =
              match pat.n with
              (* we really want the empty pattern to be in universe 0 rather than generalizing it *)
              | Tm_fvar fv when S.fv_eq_lid fv Const.nil_lid ->
                let nil = S.mk_Tm_uinst pat [U_zero] in
                let pattern =
                  S.fvar_with_dd (Ident.set_lid_range Const.pattern_lid pat.pos) None
                in
                S.mk_Tm_app nil [(pattern, S.as_aqual_implicit true)] pat.pos
              | _ -> pat
            in
            pre, post, Some (S.mk (Tm_meta {tm=pat;meta=Meta_desugared Meta_smt_pat}) pat.pos)
          | _ -> fail Errors.Fatal_InvalidLemmaArgument "Invalid arguments to 'Lemma'"
        else
          (* Otherwise the arguments are (requires pre) and (ensures post), either
             explicitly tagged or given positionally, and both are optional. *)
          let tagged_req, rest' = List.partition is_requires rest0 in
          let tagged_ens, rest' = List.partition is_ensures rest' in
          let rest' = desugar_args env rest' in
          let get l = match l with
            | [] -> None
            | [x] -> Some (fst (List.hd (desugar_args env [x])))
            | _ -> fail Errors.Fatal_NotEnoughArgsToEffect
                     "Too many requires/ensures clauses in a computation type"
          in
          let pre, post =
            match get tagged_req, get tagged_ens, rest' with
            | Some p, Some q, [] -> p, q
            | Some p, None, [] -> p, trivial_post result_typ
            | None, Some q, [] -> trivial_pre, q
            | None, None, [] -> trivial_pre, trivial_post result_typ
            | None, None, [(p, _)] -> p, trivial_post result_typ
            | None, None, [(p, _); (q, _)] -> p, q
            | Some p, None, [(q, _)] -> p, q
            | None, Some q, [(p, _)] -> p, q
            | _ ->
              fail Errors.Fatal_NotEnoughArgsToEffect
                (Format.fmt1 "Unexpected arguments to effect %s" (show eff))
          in
          pre, post, None
      in
      let flags = flags @ decreases_clause @ (match smtpat with
                                              | None -> []
                                              | Some p -> [SMTPAT p]) in
      (* A computation type carries no specification: the postcondition becomes
         a property of the result type, and the precondition is handed back to
         the caller, which turns it into an implicit [squash] binder (arrow
         codomain) or an assertion (ascription).  See
         [Syntax.Util.refine_with_post]. *)
      let result_typ = U.refine_with_post result_typ post in
      mk_Comp ({comp_univs=universes;
                effect_name=eff;
                result_typ=result_typ;
                flags=flags}),
      pre

and desugar_formula env (f:term) : ML S.term =
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
          { fail_or2 env (try_lookup_id env) i with pos=(range_of_id i) })
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
        S.mk_Tm_app q_head [as_arg body] f.range

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
        match op_as_term env i with
        | None -> 
          raise_error i Errors.Fatal_VariableNotFound
                      (Format.fmt1 "quantifier operator %s not found" (Ident.string_of_id i))
        | Some t -> t
      in
      desugar_quant q_head b pats false body

    | Paren f -> failwith "impossible"

    | _ -> desugar_term env f

and desugar_binder_aq env b : ML ((option ident & S.term & list S.attribute) & antiquotations_temp) =
  let attrs = b.battributes |> List.map (desugar_term env) in
  match b.b with
  | Annotated(x, t) ->
    let ty, aqs = desugar_typ_aq env t in
    (Some x, ty, attrs), aqs

  | NoName t        ->
    let ty, aqs = desugar_typ_aq env t in
    (None, ty, attrs), aqs

  | Variable x      ->
    let ident_is_ticked (id: ident) : ML bool =
      let nm   = string_of_id id in
      String.length nm > 0 && String.get nm 0 = '\''
    in
    if ident_is_ticked x
    then
      (Some x, setPos (range_of_id x) U.ktype, attrs), []
    else
      (Some x, tun_r (range_of_id x), attrs), []

and desugar_binder env b : ML (option ident & S.term & list S.attribute) =
  let r, aqs = desugar_binder_aq env b in
  check_no_aq aqs;
  r

and desugar_vquote env e r: ML string =
  (* Returns the string representation of the lid behind [e], fails if it is not an FV *)
  let tm = desugar_term env e in
  match (Subst.compress tm).n with
  | Tm_fvar fv -> string_of_lid (lid_of_fv fv)
  | _ -> raise_error r Fatal_UnexpectedTermVQuote ("VQuote, expected an fvar, got: " ^ show tm)

and as_binder env imp (_x_:(option ident & S.term & list S.attribute)) : ML _ = match _x_ with
  | (None, k, attrs) ->
    mk_binder_with_attrs (null_bv k) (trans_bqual env imp) attrs, env
  | (Some a, k, attrs) ->
    let env, a = Env.push_bv env a in
    (mk_binder_with_attrs ({a with sort=k}) (trans_bqual env imp) attrs), env

and trans_bqual env (_x_:option AST.arg_qualifier) : ML _ = match _x_ with
  | Some AST.Implicit -> Some S.imp_tag
  | Some AST.Equality -> Some S.Equality
  | Some (AST.Meta t) ->
    Some (S.Meta (desugar_term env t))
  | Some (AST.TypeClassArg) ->
    let tcresolve = desugar_term env (mk_term (Var C.tcresolve_lid) Range.dummyRange Expr) in
    Some (S.Meta tcresolve)
  | None -> None

let typars_of_binders env bs : ML (_ & binders) =
    let env, tpars = List.fold_left (fun (env, out) b ->
        let tk = desugar_binder env ({b with blevel=Formula}) in  (* typars follow the same binding conventions as formulas *)
        match tk with
            | Some a, k, attrs ->
                let env, a = push_bv env a in
                let a = {a with sort=k} in
                env, (mk_binder_with_attrs a (trans_bqual env b.aqual) attrs)::out
            | _ -> raise_error b Errors.Fatal_UnexpectedBinder "Unexpected binder") (env, []) bs in
    env, List.rev tpars


let desugar_attributes (env:env_t) (cattributes:list term) : ML (list cflag) =
    let desugar_attribute t =
        match (unparen t).tm with
            | _ -> raise_error t Errors.Fatal_UnknownAttribute ("Unknown attribute " ^ term_to_string t)
    in List.map desugar_attribute cattributes

let binder_ident (b:binder) : option ident =
  match b.b with
  | Annotated (x, _)
  | Variable x -> Some x
  | NoName _ -> None

let binder_idents (bs:list binder) : ML (list ident) =
  List.collect (fun b -> FStarC.Common.list_of_option (binder_ident b)) bs

let mk_typ_abbrev env d lid uvs typars kopt t lids quals rng : ML _ =
    (* fetch attributes here to support `deprecated`, just as for
     * TopLevelLet (see comment there) *)
    let attrs = U.deduplicate_terms (List.map (desugar_term env) d.attrs) in
    let val_attrs = Env.lookup_letbinding_quals_and_attrs env lid |> snd in
    let lb = {
        lbname=Inr (S.lid_and_dd_as_fv lid None);
        lbunivs=uvs;
        lbdef=no_annot_abs typars t;
        lbtyp=if Some? kopt then U.arrow typars (S.mk_Total (kopt |> Option.must)) else tun;
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

let rec desugar_tycon env (d: AST.decl) (d_attrs_initial:list S.term) quals tcs : ML (env_t & sigelts) =
  let rng = d.drange in
  let tycon_id = function
    | TyconAbstract(id, _, _)
    | TyconAbbrev(id, _, _, _)
    | TyconRecord(id, _, _, _, _)
    | TyconVariant(id, _, _, _) -> id in
  let binder_to_term b = match b.b with
    | Annotated (x, _)
    | Variable x -> mk_term (Var (lid_of_ids [x])) (range_of_id x) Expr
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
                    let desugar_attr_fv = {fv_name = setPos range FStarC.Parser.Const.desugar_of_variant_record_lid; fv_qual = None} in
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
      //let _ = Format.print_string (Format.fmt2 "Translated record %s to constructor %s\n" ((string_of_id id)) (term_to_string constrTyp)) in

      let names = id :: binder_idents parms in
      List.iter (fun (f, _, _, _) ->
          if BU.for_some (fun i -> ident_equals f i) names then
              raise_error f Errors.Error_FieldShadow
                (Format.fmt1 "Field %s shadows the record's name or a parameter of it, please rename it" (string_of_id f)))
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
                         else (log_issue se Errors.Warning_AddImplicitAssumeNewQualifier
                                 (Format.fmt1 "Adding an implicit 'assume new' qualifier on %s" (show l));
                               S.Assumption :: S.New :: quals) in
             let t = match typars with
                | [] -> k
                | _ -> S.mk_Tm_arrow typars (mk_Total k) se.sigrng in
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
                 let c, pre = desugar_comp t.range false env' t in
                 (* An effect abbreviation is a macro over an effect and a
                    result type; it cannot carry a specification of its own.  A
                    [requires] would have to become an implicit binder on the
                    *arrow* whose codomain the abbreviation is used at, and an
                    abbreviation has no arrow of its own; an [ensures] would
                    have to refine the result type, and the abbreviation is not
                    unfolded at its use sites, so the refinement would silently
                    be lost there.  Reject both. *)
                 let () =
                   if not (U.is_t_true pre)
                   then raise_error t Errors.Fatal_UnexpectedComputationTypeForLetRec
                          "An effect abbreviation may not have a 'requires' clause; \
                           state the precondition at each use site instead"
                 in
                 let () =
                   match (Subst.compress (U.comp_result c)).n with
                   | Tm_refine _ ->
                     raise_error t Errors.Fatal_UnexpectedComputationTypeForLetRec
                       "An effect abbreviation may not have an 'ensures' clause, \
                        nor a refined result type; state the postcondition at each \
                        use site instead"
                   | _ -> ()
                 in
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
      let rec collect_tcs quals et _tc_d_attrs_ : ML _ =
        let (tc, d_attrs) = _tc_d_attrs_ in
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
                let t = U.name_function_binders t in
                let proj_names =
                  let bs, c = U.arrow_formals t in
                  List.mapi (fun i b -> U.mk_field_projector_name name b.binder_bv i) bs
                in
                (name, (tps, { sigel = Sig_datacon {lid=name;
                                                    us=univs;
                                                    t=U.arrow data_tpars (mk_Total t);
                                                    ty_lid=tname;
                                                    num_ty_params=ntps;
                                                    mutuals;
                                                    injective_type_params;
                                                    proj_disc_lids = [U.mk_discriminator name] @ proj_names;
                                                    };
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
            Format.print3 "Adding attributes to type %s: val_attrs=[@@%s] attrs=[@@%s]\n" 
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
        Format.print1 "After disentangling: %s\n" (show bundle)
      );
      let env = push_sigelt env0 bundle in
      let env = List.fold_left push_sigelt env abbrevs in
      env, [bundle] @ abbrevs

    | [] -> failwith "impossible"

let desugar_binders env binders =
    let env, binders = List.fold_left (fun (env,binders) b ->
    match desugar_binder env b with
      | Some a, k, attrs ->
        let binder, env = as_binder env b.aqual (Some a, k, attrs) in
        env, binder::binders

      | _ -> raise_error b Errors.Fatal_MissingNameInBinder "Missing name in binder") (env, []) binders in
    env, List.rev binders

let push_reflect_effect env quals (effect_name:Ident.lid) range : ML _ =
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

let parse_attr_with_list warn (at:S.term) (head:lident) : ML (option (list int & Range.t) & bool) =
  let warn () =
    if warn then
      Errors.log_issue at Errors.Warning_UnappliedFail
        (Format.fmt1 "Found ill-applied ‘%s’, argument should be a non-empty list of integer literals" (string_of_lid head))
  in
  let hd, args = U.head_and_args_full at in
   match (SS.compress hd).n with
   | Tm_fvar fv when S.fv_eq_lid fv head ->
     begin
       match args with
       | [] -> Some ([], at.pos), true
       | [(a1, _)] ->
         begin
         match EMB.unembed a1 EMB.id_norm_cb with
         | Some es ->
           Some (es, at.pos), true
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
let get_fail_attr1 warn (at : S.term) : ML (option (list int & Range.t & bool)) =
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
let get_fail_attr warn (ats : list S.term) : ML (option (list int & Range.t & bool)) =
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

let lookup_effect_lid env (l:lident) (r:Range.t) : ML S.eff_decl =
  match Env.try_lookup_effect_defn env l with
  | None ->
    raise_error r Errors.Fatal_EffectNotFound
      ("Effect name " ^ show l ^ " not found")
  | Some l -> l

(* As [lookup_effect_lid], but resolves an effect abbreviation to the effect it
   abbreviates.  A lift is always declared between two actual effects, but the
   source may well be written with an abbreviation: [PURE] and [DIV] are
   abbreviations of [Tot] and [Div], and a great deal of existing code says
   [sub_effect PURE ~> M]. *)
let lookup_effect_lid_unfold env (l:lident) (r:Range.t) : ML S.eff_decl =
  match Env.try_lookup_effect_defn env l with
  | Some ed -> ed
  | None ->
    match Env.try_lookup_root_effect_name env l with
    | Some l' -> lookup_effect_lid env l' r
    | None ->
      raise_error r Errors.Fatal_EffectNotFound
        ("Effect name " ^ show l ^ " not found")

let trans_pragma env (_x_:AST.pragma) : ML _ = match _x_ with
  | AST.ShowOptions -> S.ShowOptions
  | AST.SetOptions s -> S.SetOptions s
  | AST.ResetOptions sopt -> S.ResetOptions sopt
  | AST.PushOptions sopt -> S.PushOptions sopt
  | AST.PopOptions -> S.PopOptions
  | AST.RestartSolver -> S.RestartSolver
  | AST.PrintEffectsGraph -> S.PrintEffectsGraph
  | AST.Check t ->
    let t, aq = desugar_term_maybe_top true env t in
    check_no_aq aq;
    S.Check t
  | AST.Eval t ->
    let t, aq = desugar_term_maybe_top true env t in
    check_no_aq aq;
    S.Eval t

(* An effect declaration is now just a name (and possibly some binders).
   There are no combinators, no signature and no actions. *)
let rec desugar_declare_effect env d (d_attrs:list S.term) (quals: qualifiers) eff_name eff_binders : ML _ =
    let env0 = env in
    let monad_env = Env.enter_monad_scope env eff_name in
    let env, binders = desugar_binders monad_env eff_binders in
    let binders = Subst.close_binders binders in
    let mname = qualify env0 eff_name in
    let qualifiers = List.map (trans_qual d.drange (Some mname)) quals in
    let sigel = Sig_new_effect ({
      mname = mname;
      cattributes = [];
      univs = [];
      binders = binders;
      combinators = None;
      eff_attrs = d_attrs;
      extraction_mode = S.Extract_primitive
    }) in
    let se = ({
      sigel = sigel;
      sigquals = qualifiers;
      sigrng = d.drange;
      sigmeta = default_sigmeta;
      sigattrs = d_attrs;
      sigopts = None;
      sigopens_and_abbrevs = opens_and_abbrevs env
    }) in
    push_sigelt env0 se, [se]

(* [effect { M with { repr = ...; return = ...; bind = ... } }]

   The combinators are only used for reification (extraction, and running
   tactics); they play no role in typechecking, which is driven entirely by
   the pre/postconditions written at each computation type. *)
and desugar_define_effect env d (d_attrs:list S.term) (quals: qualifiers) eff_name eff_binders (eff_decls:list decl) : ML _ =
    let env0 = env in
    let monad_env = Env.enter_monad_scope env eff_name in
    let env, binders = desugar_binders monad_env eff_binders in
    let binders = Subst.close_binders binders in
    let mname = qualify env0 eff_name in
    let qualifiers = List.map (trans_qual d.drange (Some mname)) quals in
    (* Each combinator is given as [name = term]. *)
    let lookup_comb (s:string) : ML S.tscheme =
      let decl_of_name =
        eff_decls |> BU.try_find (fun d ->
          match d.d with
          | Tycon (_, _, [TyconAbbrev (name, _, _, _)]) -> string_of_id name = s
          | _ -> false)
      in
      match decl_of_name with
      | Some ({ d = Tycon (_, _, [TyconAbbrev (_, _, _, defn)]) }) ->
        [], Subst.close binders (desugar_term env defn)
      | _ ->
        raise_error d Errors.Fatal_UnexpectedEffect
          (Format.fmt2 "Effect %s is missing the '%s' combinator; \
                        an effect definition must provide 'repr', 'return' and 'bind'"
             (string_of_id eff_name) s)
    in
    let () =
      eff_decls |> List.iter (fun d ->
        match d.d with
        | Tycon (_, _, [TyconAbbrev (name, _, _, _)])
            when List.mem (string_of_id name) ["repr"; "return"; "bind"] -> ()
        | _ ->
          raise_error d Errors.Fatal_UnexpectedEffect
            "Unexpected effect combinator: only 'repr', 'return' and 'bind' are supported")
    in
    let combinators = {
      repr        = lookup_comb "repr";
      return_repr = lookup_comb "return";
      bind_repr   = lookup_comb "bind";
    } in
    let sigel = Sig_new_effect ({
      mname = mname;
      cattributes = [];
      univs = [];
      binders = binders;
      combinators = Some combinators;
      eff_attrs = d_attrs;
      extraction_mode =
        if U.has_attribute d_attrs C.primitive_extraction_attr
        then S.Extract_primitive
        else S.Extract_reify
    }) in
    let se = ({
      sigel = sigel;
      sigquals = qualifiers;
      sigrng = d.drange;
      sigmeta = default_sigmeta;
      sigattrs = d_attrs;
      sigopts = None;
      sigopens_and_abbrevs = opens_and_abbrevs env
    }) in
    let env = push_sigelt env0 se in
    (* [reflectable] introduces [M?.reflect] *)
    let env = push_reflect_effect env qualifiers mname d.drange in
    env, [se]

and desugar_redefine_effect env d d_attrs trans_qual quals eff_name eff_binders defn : ML _ =
    let env0 = env in
    let env = Env.enter_monad_scope env eff_name in
    let env, binders = desugar_binders env eff_binders in
    let ed_lid, ed, args, cattributes =
        let head, args = head_and_args_full defn in
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
    let binders = Subst.close_binders binders in
    if List.length args <> List.length ed.binders
    then raise_error defn Errors.Fatal_ArgumentLengthMismatch "Unexpected number of arguments to effect constructor";
    let mname = qualify env0 eff_name in
    let ed = {
            cattributes   = cattributes;
            mname         = mname;
            univs         = ed.univs;
            binders       = binders;
            combinators   = ed.combinators;
            eff_attrs     = ed.eff_attrs;
            extraction_mode = ed.extraction_mode;
    } in
    let se =
      { sigel = Sig_new_effect ed;
        sigquals = List.map (trans_qual (Some mname)) quals;
        sigrng = d.drange;
        sigmeta = default_sigmeta;
        sigattrs = d_attrs;
        sigopts = None;
        sigopens_and_abbrevs = opens_and_abbrevs env
      }
    in
    push_sigelt env0 se, [se]

and desugar_decl_maybe_fail_attr env (d: decl) (attrs : list S.term) : ML (env_t & sigelts) =
  let no_fail_attrs (ats : list S.term) : ML (list S.term) =
      List.filter (fun at -> None? (get_fail_attr1 false at)) ats
  in

  (* If this is an expect_failure, check to see if it fails.
   * If it does, check that the errors match as we normally do.
   * If it doesn't fail, leave it alone! The typechecker will check the failure. *)
  let env, sigelts =
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
        if Options.print_expected_failures () then
          Errors.print_expected_failures errs;
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
                  (pp (Class.Ord.sort expected_errs)) ^/^
                prefix 2 1 (text "but it raised")
                  (pp (Class.Ord.sort errnos)) ^/^ text "(at desugaring time)" ^^ dot;
                text (Format.fmt3 "Error #%s was raised %s times, instead of %s."
                                      (show e) (show n2) (show n1));
              ];
            env0, []
        end
      end
    | None ->
      desugar_decl_core env attrs d
  in
  env, sigelts

and desugar_decl env (d:decl) : ML (env_t & sigelts) =
  FStarC.GenSym.reset_gensym ();
  let attrs = List.map (desugar_term env) d.attrs in
  let attrs = U.deduplicate_terms attrs in
  let env, ses = desugar_decl_maybe_fail_attr env d attrs in
  let ses =
    if U.has_attribute attrs Const.admitted_lid
    then ses |> List.map (fun se -> { se with sigmeta = { se.sigmeta with sigmeta_admit = true } })
    else ses
  in
  env, ses |> List.map generalize_annotated_univs

and desugar_decl_core env (d_attrs:list S.term) (d:decl) : ML (env_t & sigelts) =
  let trans_qual = trans_qual d.drange in
  match d.d with
  | Pragma p ->
    let p = trans_pragma env p in
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
    let env = Env.reshadow_iface_defs (Env.push_namespace env lid restriction) in
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
    let env = Env.reshadow_iface_defs (Env.push_include env lid restriction) in
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
      Format.print2 "Desugared tycon from {%s} to {%s}\n" (show d) (show ses)
    );
    (* Handling typeclasses: we typecheck the tcs as usual, and then need to add
     * %splice[new_meth_lids] (mk_class type_lid)
     * where the tricky bit is getting the new_meth_lids. To do so,
     * we traverse the new declarations marked with "Projector", and get
     * the field names. This is pretty ugly. *)
    let mkclass lid =
      let r = range_of_lid lid in
      let body =
        U.mk_app (S.tabbrev C.mk_class_lid)
                 [S.as_arg (U.exp_string (string_of_lid lid))]
      in
      U.abs [S.mk_binder (S.new_bv (Some r) (tun_r r))] body None
    in

    (* Find methods by looking at the binders of the record's datacon.
    We later filter-out the no_methods. *)
    let rec get_meths se : ML _ =
      match se.sigel with
      | Sig_bundle {ses} ->
        List.concatMap get_meths ses
      | Sig_datacon { t; num_ty_params } ->
        let bs, _ = U.arrow_formals t in
        (* drop the type parameters *)
        let _, bs = List.splitAt num_ty_params bs in
        let bs = U.name_binders bs in
        bs |> List.concatMap (fun b ->
          let id = b.binder_bv.ppname in
          [qualify env id])
      | _ -> []
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
    let rec splice_decl (meths : list lident) se : ML _ =
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
          (* If the name begins with _, or if it has the no_method attribute, then
           * it will not be defined. So we filter it out of the names declared by the splice. *)
          let meths = List.filter (fun x -> not (String.index (string_of_id (ident_of_lid x)) 0 = '_') && not (has_no_method_attr x)) meths in
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
             let rec add_class_attr se : ML _ =
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
      let qual =
        match isrec with
        | NoLetQualifier -> LocalNoLetQualifier
        | Rec -> LocalRec
      in
      let as_inner_let =
        mk_term (Let(qual, lets, mk_term (Const Const_unit) d.drange Expr)) d.drange Expr
      in
      let ds_lets, aq = desugar_term_maybe_top true env as_inner_let in
      check_no_aq aq;
      match (Subst.compress <| ds_lets).n with
        | Tm_let {lbs} ->
          let fvs = snd lbs |> List.map (fun lb -> Inr?.v lb.lbname) in
          let val_quals, val_attrs =
            List.fold_right (fun fv (qs, ats) ->
                let qs', ats' = Env.lookup_letbinding_quals_and_attrs env fv.fv_name in
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
          // Format.print3 "Desugaring %s, val_quals are %s, val_attrs are %s\n"
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
          let names = fvs |> List.map (fun fv -> fv.fv_name) in
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
      let rec gen_fresh_toplevel_name () : ML _ =
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
      if Nil? bvs && not (is_var_pattern pat)
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
    let se = { sigel = Sig_datacon {lid=l;us=[];t;ty_lid=C.exn_lid;num_ty_params=0;mutuals=[C.exn_lid];injective_type_params=false;proj_disc_lids=[]};
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
    env, [se']

  | NewEffect (RedefineEffect(eff_name, eff_binders, defn)) ->
    let quals = d.quals in
    desugar_redefine_effect env d d_attrs trans_qual quals eff_name eff_binders defn

  | NewEffect (DeclareEffect(eff_name, eff_binders)) ->
    let quals = d.quals in
    desugar_declare_effect env d d_attrs quals eff_name eff_binders

  | NewEffect (DefineEffect(eff_name, eff_binders, eff_decls)) ->
    let quals = d.quals in
    desugar_define_effect env d d_attrs quals eff_name eff_binders eff_decls

  | SubEffect l ->
    let src_ed = lookup_effect_lid_unfold env l.msource d.drange in
    let dst_ed = lookup_effect_lid_unfold env l.mdest d.drange in
    let lift =
      match l.lift_op with
      | None -> None
      | Some t -> Some ([], desugar_term env t) in
    let se = { sigel = Sig_sub_effect({source=src_ed.mname; target=dst_ed.mname; lift=lift});
               sigquals = List.map (trans_qual None) d.quals;
               sigrng = d.drange;
               sigmeta = default_sigmeta;
               sigattrs = d_attrs;
               sigopts = None;
               sigopens_and_abbrevs = opens_and_abbrevs env } in
    env, [se]

  | Splice (is_typed, ids, t) ->
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
         (Format.fmt1 "Unknown syntax extension %s" extension_name)
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
        desugar_decl_maybe_fail_attr env { d' with quals; attrs; drange=d.drange }
           (attrs |> List.map (desugar_term env) |> U.deduplicate_terms)
  )

  | DeclToBeDesugared tbs -> (
    match lookup_extension_tosyntax tbs.lang_name with
    | None -> 
      raise_error d Errors.Fatal_SyntaxError
        (Format.fmt1 "Could not find desugaring callback for extension %s" tbs.lang_name)
    | Some desugar ->
      let mk_sig sigel = 
        let top_attrs = d_attrs in
        let se = { 
            sigel;
            sigquals = List.map (trans_qual None) d.quals;
            sigrng = d.drange;
            sigmeta = { default_sigmeta with sigmeta_extension_decl = true };
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

let desugar_decls env decls : ML _ =
  Stats.record "desugar_decls" fun () ->
  let env, sigelts =
    List.fold_left (fun (env, sigelts) d ->
      let env, se = desugar_decl env d in
      env, List.rev_append se sigelts) (env, []) decls
  in
  env, List.rev sigelts

(* Top-level functionality: from AST to a module
   Keeps track of the name of variables and so on (in the context)
 *)
let desugar_modul_common (curmod: option S.modul) env (m:AST.modul) : ML (env_t & Syntax.modul & bool) =
  let env = match curmod, m with
    | None, _ ->
        env
    | Some ({ name = prev_lid }), Module {mname = current_lid }
      when lid_equals prev_lid current_lid && Options.interactive () ->
        // If we're in the interactive mode reading the contents of an fst after
        // desugaring the corresponding fsti, don't finish the fsti
        env
    | Some prev_mod, _ ->
        fst (Env.finish_module_or_interface env prev_mod) in
  let (env, pop_when_done), mname, decls, intf =
    match m with
    | Interface {no_prelude; mname; decls; admitted} ->
      Env.prepare_module_or_interface no_prelude true admitted env mname Env.default_mii, mname, decls, true
    | Module {no_prelude; mname; decls} ->
      Env.prepare_module_or_interface no_prelude false false env mname Env.default_mii, mname, decls, false
  in
  let env, sigelts = desugar_decls env decls in
  let modul = {
    name = mname;
    declarations = sigelts;
    is_interface=intf
  } in
  env, modul, pop_when_done

let desugar_partial_modul curmod (env:env_t) (m:AST.modul) : ML (env_t & Syntax.modul) =
  let env, modul, pop_when_done = desugar_modul_common curmod env m in
  if pop_when_done then Env.pop (), modul
  else env, modul

let desugar_modul env (m:AST.modul) : ML (env_t & Syntax.modul) =
  Errors.with_ctx ("While desugaring module " ^ Class.Show.show (lid_of_modul m)) (fun () ->
    let env, modul, pop_when_done = desugar_modul_common None env m in
    let env, modul = Env.finish_module_or_interface env modul in
    if Options.dump_module (string_of_lid modul.name)
    then Format.print1 "Module after desugaring:\n%s\n" (show modul);
    (if pop_when_done then export_interface modul.name env else env), modul
  )

/////////////////////////////////////////////////////////////////////////////////////////
//External API for modules
/////////////////////////////////////////////////////////////////////////////////////////
let with_options (f:unit -> ML 'a) : ML 'a =
  let r =
    Options.with_saved_options (fun () ->
      let r = f () in
      r
    )
  in
  r

let ast_modul_to_modul modul : ML (withenv S.modul) =
    fun env ->
        with_options (fun () ->
        let e, m = desugar_modul env modul in
        m, e)

let decls_to_sigelts decls : ML (withenv S.sigelts) =
    fun env ->
        with_options (fun () ->
        let env, sigelts = desugar_decls env decls in
        sigelts, env)

let partial_ast_modul_to_modul modul a_modul : ML (withenv S.modul) =
    fun env ->
        with_options (fun () ->
        let env, modul = desugar_partial_modul modul env a_modul in
        modul, env)

let add_modul_to_env_core (finish: bool) (m:Syntax.modul)
                     (mii:module_inclusion_info)
                     (erase_univs:S.term -> ML S.term) : ML (withenv unit) =
  fun en ->
      let erase_univs_ed ed =
          let erase_binders bs =
              match bs with
              | [] -> []
              | _ ->
                let t = erase_univs (S.mk_Tm_abs bs S.t_unit None Range.dummyRange) in
                let bs, _, _ = U.abs_formals_ln t in
                if Nil? bs then failwith "Impossible" else bs
          in
          let binders, _, binders_opening =
              Subst.open_term' (erase_binders ed.binders) S.t_unit in
          let erase_term t =
              Subst.close binders (erase_univs (Subst.subst binders_opening t))
          in
            { ed with
              univs         = [];
              binders       = Subst.close_binders binders;
          }
      in
      let push_sigelt env se =
          match se.sigel with
          | Sig_new_effect ed ->
            let se' = {se with sigel=Sig_new_effect (erase_univs_ed ed)} in
            let env = Env.push_sigelt_force env se' in
            push_reflect_effect env se.sigquals ed.mname se.sigrng
          | _ -> Env.push_sigelt_force env se
      in
      let en, pop_when_done = Env.prepare_module_or_interface false false false en m.name mii in
      let en = List.fold_left
                    push_sigelt
                    (Env.set_current_module en m.name)
                    m.declarations in
      let en = if finish then Env.finish en m else en in
      (), (if pop_when_done then export_interface m.name en else en)

let add_partial_modul_to_env = add_modul_to_env_core false
let add_modul_to_env = add_modul_to_env_core true
