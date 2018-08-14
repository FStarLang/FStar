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
module FStar.ToSyntax.ToSyntax
open FStar.ST
open FStar.Exn
open FStar.All

open FStar
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Util
open FStar.Parser
open FStar.Syntax.DsEnv
open FStar.Parser.AST
open FStar.Ident
open FStar.Const
open FStar.Errors
open FStar.Syntax

module C = FStar.Parser.Const
module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module BU = FStar.Util
module Env = FStar.Syntax.DsEnv
module P = FStar.Syntax.Print
module EMB = FStar.Syntax.Embeddings
module SS = FStar.Syntax.Subst

let desugar_disjunctive_pattern pats when_opt branch =
    pats |> List.map (fun pat -> U.branch(pat, when_opt, branch))

let trans_qual r maybe_effect_id = function
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
  | AST.Abstract ->      S.Abstract
  | AST.Opaque ->        Errors.log_issue r (Errors.Warning_DeprecatedOpaqueQualifier, "The 'opaque' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given 'opaque val f : t', the behavior was to exclude the definition of 'f' to the SMT solver. This corresponds roughly to the new 'irreducible' qualifier. (2) Given 'opaque type t = t'', the behavior was to provide the definition of 't' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of 'unfoldable' (which is currently the default)."); S.Visible_default
  | AST.Reflectable ->
    begin match maybe_effect_id with
    | None -> raise_error (Errors.Fatal_ReflectOnlySupportedOnEffects, "Qualifier reflect only supported on effects") r
    | Some effect_id ->  S.Reflectable effect_id
    end
  | AST.Reifiable ->     S.Reifiable
  | AST.Noeq ->          S.Noeq
  | AST.Unopteq ->       S.Unopteq
  | AST.DefaultEffect -> raise_error (Errors.Fatal_DefaultQualifierNotAllowedOnEffects, "The 'default' qualifier on effects is no longer supported") r
  | AST.Inline
  | AST.Visible -> raise_error (Errors.Fatal_UnsupportedQualifier, "Unsupported qualifier") r

let trans_pragma = function
  | AST.SetOptions s -> S.SetOptions s
  | AST.ResetOptions sopt -> S.ResetOptions sopt
  | AST.PushOptions sopt -> S.PushOptions sopt
  | AST.PopOptions -> S.PopOptions
  | AST.LightOff -> S.LightOff

let as_imp = function
    | Hash -> Some S.imp_tag
    | _ -> None
let arg_withimp_e imp t =
    t, as_imp imp
let arg_withimp_t imp t =
    match imp with
        | Hash -> t, Some S.imp_tag
        | _ -> t, None

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
    | Name l
    | Construct(l, _) -> Env.try_lookup_effect_name env l |> Option.isSome
    | App(head, _, _) -> is_comp_type env head
    | Paren t -> failwith "impossible"
    | Ascribed(t, _, _)
    | LetOpen(_, t) -> is_comp_type env t
    | _ -> false

let unit_ty = mk_term (Name C.unit_lid) Range.dummyRange Type_level

let compile_op_lid n s r = [mk_ident(compile_op n s r, r)] |> lid_of_ids

let op_as_term env arity rng op : option<S.term> =
  let r l dd = Some (S.lid_as_fv (set_lid_range l op.idRange) dd None |> S.fv_to_tm) in
  let fallback () =
    match Ident.text_of_id op with
    | "=" ->
      r C.op_Eq delta_equational
    | ":=" ->
      r C.write_lid delta_equational
    | "<" ->
      r C.op_LT delta_equational
    | "<=" ->
      r C.op_LTE delta_equational
    | ">" ->
      r C.op_GT delta_equational
    | ">=" ->
      r C.op_GTE delta_equational
    | "&&" ->
      r C.op_And delta_equational
    | "||" ->
      r C.op_Or delta_equational
    | "+" ->
      r C.op_Addition delta_equational
    | "-" when (arity=1) ->
      r C.op_Minus delta_equational
    | "-" ->
      r C.op_Subtraction delta_equational
    | "/" ->
      r C.op_Division delta_equational
    | "%" ->
      r C.op_Modulus delta_equational
    | "!" ->
      r C.read_lid delta_equational
    | "@" ->
      if Options.ml_ish ()
      then r C.list_append_lid     (Delta_equational_at_level 2)
      else r C.list_tot_append_lid (Delta_equational_at_level 2)
    | "^" ->
      r C.strcat_lid delta_equational
    | "|>" ->
      r C.pipe_right_lid delta_equational
    | "<|" ->
      r C.pipe_left_lid delta_equational
    | "<>" ->
      r C.op_notEq delta_equational
    | "~"   ->
      r C.not_lid (Delta_constant_at_level 2)
    | "=="  ->
      r C.eq2_lid (Delta_constant_at_level 2)
    | "<<" ->
      r C.precedes_lid delta_constant
    | "/\\" ->
      r C.and_lid (Delta_constant_at_level 1)
    | "\\/" ->
      r C.or_lid (Delta_constant_at_level 1)
    | "==>" ->
      r C.imp_lid (Delta_constant_at_level 1)
    | "<==>" ->
      r C.iff_lid (Delta_constant_at_level 2)
    | _ -> None
  in
  match Env.try_lookup_lid env (compile_op_lid arity op.idText op.idRange) with
  | Some t -> Some (fst t)
  | _ -> fallback()

let sort_ftv ftv =
  BU.sort_with (fun x y -> String.compare x.idText y.idText) <|
      BU.remove_dups (fun x y -> x.idText = y.idText) ftv

let rec free_type_vars_b env binder = match binder.b with
  | Variable _ -> env, []
  | TVariable x ->
    let env, _ = Env.push_bv env x in
    (env, [x])
  | Annotated(_, term) ->
    (env, free_type_vars env term)
  | TAnnotated(id, _) ->
    let env, _ = Env.push_bv env id in
    (env, [])
  | NoName t ->
    (env, free_type_vars env t)
and free_type_vars env t = match (unparen t).tm with
  | Labeled _ -> failwith "Impossible --- labeled source term"

  | Tvar a ->
    (match Env.try_lookup_id env a with
      | None -> [a]
      | _ -> [])

  | Wild
  | Const _
  | Uvar _
  | Var  _
  | Projector _
  | Discrim _
  | Name _  -> []

  | Requires (t, _)
  | Ensures (t, _)
  | NamedTyp(_, t) -> free_type_vars env t
  | Paren t -> failwith "impossible"
  | Ascribed(t, t', tacopt) ->
    let ts = t::t'::(match tacopt with None -> [] | Some t -> [t]) in
    List.collect (free_type_vars env) ts

  | Construct(_, ts) -> List.collect (fun (t, _) -> free_type_vars env t) ts

  | Op(_, ts) -> List.collect (free_type_vars env) ts

  | App(t1,t2,_) -> free_type_vars env t1@free_type_vars env t2

  | Refine (b, t) ->
    let env, f = free_type_vars_b env b in
    f@free_type_vars env t

  | Product(binders, body)
  | Sum(binders, body) ->
    let env, free = List.fold_left (fun (env, free) binder ->
      let env, f = free_type_vars_b env binder in
      env, f@free) (env, []) binders in
    free@free_type_vars env body

  | Project(t, _) -> free_type_vars env t

  | Attributes cattributes ->
      (* attributes should be closed but better safe than sorry *)
      List.collect (free_type_vars env) cattributes

  | Abs _  (* not closing implicitly over free vars in all these forms: TODO: Fixme! *)
  | Let _
  | LetOpen _
  | If _
  | QForall _
  | QExists _
  | Record _
  | Match _
  | TryWith _
  | Bind _
  | Quote _
  | VQuote _
  | Antiquote _
  | Seq _ -> []

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
  else let binders = ftv |> List.map (fun x -> mk_binder (TAnnotated(x, tm_type x.idRange)) x.idRange Type_level (Some Implicit)) in
       let result = mk_term (Product(binders, t)) t.range t.level in
       result

let close_fun env t =
  let ftv = sort_ftv <| free_type_vars env t in
  if List.length ftv = 0
  then t
  else let binders = ftv |> List.map (fun x -> mk_binder (TAnnotated(x, tm_type x.idRange)) x.idRange Type_level (Some Implicit)) in
       let t = match (unparen t).tm with
        | Product _ -> t
        | _ -> mk_term (App(mk_term (Name C.effect_Tot_lid) t.range t.level, t, Nothing)) t.range t.level in
       let result = mk_term (Product(binders, t)) t.range t.level in
       result

let rec uncurry bs t = match t.tm with
    | Product(binders, t) -> uncurry (bs@binders) t
    | _ -> bs, t

let rec is_var_pattern p = match p.pat with
  | PatWild
  | PatTvar(_, _)
  | PatVar(_, _) -> true
  | PatAscribed(p, _) -> is_var_pattern p
  | _ -> false

let rec is_app_pattern p = match p.pat with
  | PatAscribed(p,_) -> is_app_pattern p
  | PatApp({pat=PatVar _}, _) -> true
  | _ -> false

let replace_unit_pattern p = match p.pat with
  | PatConst FStar.Const.Const_unit ->
    mk_pattern (PatAscribed (mk_pattern PatWild p.prange, (unit_ty, None))) p.prange
  | _ -> p

let rec destruct_app_pattern env is_top_level p = match p.pat with
  | PatAscribed(p,t) ->
    let (name, args, _) = destruct_app_pattern env is_top_level p in
    (name, args, Some t)
  | PatApp({pat=PatVar (id, _)}, args) when is_top_level ->
    (Inr (qualify env id), args, None)
  | PatApp({pat=PatVar (id, _)}, args) ->
    (Inl id, args, None)
  | _ ->
    failwith "Not an app pattern"

let rec gather_pattern_bound_vars_maybe_top acc p =
  let gather_pattern_bound_vars_from_list =
      List.fold_left gather_pattern_bound_vars_maybe_top acc
  in
  match p.pat with
  | PatWild
  | PatConst _
  | PatVar (_, Some Implicit)
  | PatName _
  | PatTvar _
  | PatOp _ -> acc
  | PatApp (phead, pats) -> gather_pattern_bound_vars_from_list (phead::pats)
  | PatVar (x, _) -> set_add x acc
  | PatList pats
  | PatTuple  (pats, _)
  | PatOr pats -> gather_pattern_bound_vars_from_list pats
  | PatRecord guarded_pats -> gather_pattern_bound_vars_from_list (List.map snd guarded_pats)
  | PatAscribed (pat, _) -> gather_pattern_bound_vars_maybe_top acc pat

let gather_pattern_bound_vars =
  let acc = new_set (fun id1 id2 -> if id1.idText = id2.idText then 0 else 1) in
  fun p -> gather_pattern_bound_vars_maybe_top acc p

type bnd =
  | LocalBinder of bv     * S.aqual
  | LetBinder   of lident * (S.term * option<S.term>)
let binder_of_bnd = function
  | LocalBinder (a, aq) -> a, aq
  | _ -> failwith "Impossible"

type env_t = Env.env
type lenv_t = list<bv>

(* TODO : shouldn't this be Tot by default ? *)
let mk_lb (attrs, n, t, e, pos) = {
    lbname=n;
    lbunivs=[];
    lbeff=C.effect_ALL_lid;
    lbtyp=t;
    lbdef=e;
    lbattrs=attrs;
    lbpos=pos;
}
let no_annot_abs bs t = U.abs bs t None

let mk_ref_read tm =
  let tm' = Tm_app (
    S.fv_to_tm (S.lid_as_fv C.sread_lid delta_constant None),
    [ tm, S.as_implicit false ]) in
  S.mk tm' None tm.pos

let mk_ref_alloc tm =
  let tm' = Tm_app (
    S.fv_to_tm (S.lid_as_fv C.salloc_lid delta_constant None),
    [ tm, S.as_implicit false ]) in
  S.mk tm' None tm.pos

let mk_ref_assign t1 t2 pos =
  let tm = Tm_app (
    S.fv_to_tm (S.lid_as_fv C.swrite_lid delta_constant None),
    [ t1, S.as_implicit false; t2, S.as_implicit false ]) in
  S.mk tm None pos

(*
 * Collect the explicitly annotated universes in the sigelt, close the sigelt with them, and stash them appropriately in the sigelt
 *)
let generalize_annotated_univs (s:sigelt) :sigelt =
  let bs_univnames (bs:binders) :BU.set<univ_name> =
    bs |> List.fold_left (fun uvs ( { sort = t }, _) -> BU.set_union uvs (Free.univnames t)) (BU.new_set Syntax.order_univ_name)
  in
  let empty_set = BU.new_set Syntax.order_univ_name in

  match s.sigel with
  | Sig_inductive_typ _
  | Sig_datacon _ -> failwith "Impossible: collect_annotated_universes: bare data/type constructor"
  | Sig_bundle (sigs, lids) ->
    let uvs = sigs |> List.fold_left (fun uvs se ->
      let se_univs =
        match se.sigel with
        | Sig_inductive_typ (_, _, bs, t, _, _) -> BU.set_union (bs_univnames bs) (Free.univnames t)
        | Sig_datacon (_, _, t, _, _, _) -> Free.univnames t
        | _ -> failwith "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
      in
      BU.set_union uvs se_univs) empty_set |> BU.set_elements
    in
    let usubst = Subst.univ_var_closing uvs in
    { s with sigel = Sig_bundle (sigs |> List.map (fun se ->
      match se.sigel with
      | Sig_inductive_typ (lid, _, bs, t, lids1, lids2) ->
        { se with sigel = Sig_inductive_typ (lid, uvs, Subst.subst_binders usubst bs, Subst.subst (Subst.shift_subst (List.length bs) usubst) t, lids1, lids2) }
      | Sig_datacon (lid, _, t, tlid, n, lids) ->
        { se with sigel = Sig_datacon (lid, uvs, Subst.subst usubst t, tlid, n, lids) }
      | _ -> failwith "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
      ), lids) }
  | Sig_declare_typ (lid, _, t) ->
    let uvs = Free.univnames t |> BU.set_elements in
    { s with sigel = Sig_declare_typ (lid, uvs, Subst.close_univ_vars uvs t) }
  | Sig_let ((b, lbs), lids) ->
    let lb_univnames (lb:letbinding) :BU.set<univ_name> =
      BU.set_union (Free.univnames lb.lbtyp)
      (match lb.lbdef.n with
       | Tm_abs (bs, e, _) ->
         let uvs1 = bs_univnames bs in
         let uvs2 =
           match e.n with
           | Tm_ascribed (_, (Inl t, _), _) -> Free.univnames t
           | Tm_ascribed (_, (Inr c, _), _) -> Free.univnames_comp c
           | _ -> empty_set
         in
         BU.set_union uvs1 uvs2
       | Tm_ascribed (_, (Inl t, _), _) -> Free.univnames t
       | Tm_ascribed (_, (Inr c, _), _) -> Free.univnames_comp c
       | _ -> empty_set)
    in
    let all_lb_univs = lbs |> List.fold_left (fun uvs lb -> BU.set_union uvs (lb_univnames lb)) empty_set |> BU.set_elements in
    let usubst = Subst.univ_var_closing all_lb_univs in
    { s with sigel = Sig_let ((b, lbs |> List.map (fun lb -> { lb with lbunivs = all_lb_univs; lbdef = Subst.subst usubst lb.lbdef; lbtyp = Subst.subst usubst lb.lbtyp })), lids) }
  | Sig_assume (lid, _, fml) ->
    let uvs = Free.univnames fml |> BU.set_elements in
    { s with sigel = Sig_assume (lid, uvs, Subst.close_univ_vars uvs fml) }
  | Sig_effect_abbrev (lid, _, bs, c, flags) ->
    let uvs = BU.set_union (bs_univnames bs) (Free.univnames_comp c) |> BU.set_elements in
    let usubst = Subst.univ_var_closing uvs in
    { s with sigel = Sig_effect_abbrev (lid, uvs, Subst.subst_binders usubst bs, Subst.subst_comp usubst c, flags) }
  | _ -> s

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
  | "wp_ite"
  | "null_wp"
  | "wp_trivial"
  | "ctx"
  | "g_ctx"
  | "lift_from_pure"
  | "return_wp"
  | "return_elab"
  | "bind_wp"
  | "bind_elab"
  | "repr"
  | "post"
  | "pre"
  | "wp"
  | _ -> false

let rec sum_to_universe u n =
    if n = 0 then u else U_succ (sum_to_universe u (n-1))

let int_to_universe n = sum_to_universe U_zero n

let rec desugar_maybe_non_constant_universe t
  : either<int, Syntax.universe>  (* level of universe or desugared universe *)
=
  match (unparen t).tm with
      (* TODO : Check how this unification works *)
      (* The unification might introduce universe variables *)
  | Wild -> Inr (U_unif (Unionfind.univ_fresh ()))
  | Uvar u -> Inr (U_name u)

  | Const (Const_int (repr, _)) ->
      (* TODO : That might be a little dangerous... *)
      let n = int_of_string repr in
      if n < 0
      then raise_error (Errors.Fatal_NegativeUniverseConstFatal_NotSupported, "Negative universe constant  are not supported : "
                        ^ repr) t.range;
      Inl n
  | Op (op_plus, [t1 ; t2]) ->
      assert (Ident.text_of_id op_plus = "+") ;
      let u1 = desugar_maybe_non_constant_universe t1 in
      let u2 = desugar_maybe_non_constant_universe t2 in
      begin match u1, u2 with
          | Inl n1, Inl n2 -> Inl (n1+n2)
          | Inl n, Inr u
          | Inr u, Inl n -> Inr (sum_to_universe u n)
          | Inr u1, Inr u2 ->
              raise_error (Errors.Fatal_UniverseMightContainSumOfTwoUnivVars, "This universe might contain a sum of two universe variables "
                          ^ term_to_string t) t.range
      end
  | App _ ->
      let rec aux t univargs  =
        match (unparen t).tm with
        | App(t, targ, _) ->
            let uarg = desugar_maybe_non_constant_universe targ in
            aux t (uarg::univargs)
        | Var max_lid ->
            assert (Ident.text_of_lid max_lid = "max") ;
            if List.existsb (function Inr _ -> true | _ -> false) univargs
            then Inr (U_max (List.map (function Inl n -> int_to_universe n | Inr u -> u) univargs))
            else
              let nargs = List.map (function Inl n -> n | Inr _ -> failwith "impossible") univargs in
              Inl (List.fold_left (fun m n -> if m > n then m else n) 0 nargs)
        (* TODO : Might not be the best place to raise the error... *)
        | _ -> raise_error (Errors.Fatal_UnexpectedTermInUniverse, ("Unexpected term " ^ term_to_string t ^ " in universe context")) t.range
      in aux t []
  | _ -> raise_error (Errors.Fatal_UnexpectedTermInUniverse, ("Unexpected term " ^ term_to_string t ^ " in universe context")) t.range

let rec desugar_universe t : Syntax.universe =
    let u = desugar_maybe_non_constant_universe t in
    match u with
        | Inl n -> int_to_universe n
        | Inr u -> u

let check_no_aq (aq : antiquotations) : unit =
    match aq with
    | [] -> ()
    | (bv, { n = Tm_quoted (e, { qkind = Quote_dynamic })})::_ ->
        raise_error (Errors.Fatal_UnexpectedAntiquotation,
                      BU.format1 "Unexpected antiquotation: `@(%s)" (Print.term_to_string e)) e.pos
    | (bv, e)::_ ->
        raise_error (Errors.Fatal_UnexpectedAntiquotation,
                      BU.format1 "Unexpected antiquotation: `#(%s)" (Print.term_to_string e)) e.pos

(* issue 769: check that other fields are also of the same record. If
   so, then return the record found by field name resolution. *)
let check_fields env fields rg =
    let (f, _) = List.hd fields in
    let _ = Env.fail_if_qualified_by_curmodule env f in
    let record = fail_or env (try_lookup_record_by_field_name env) f in
    let check_field (f', _) =
        let _ = Env.fail_if_qualified_by_curmodule env f' in
        if Env.belongs_to_record env f' record
        then ()
        else let msg = BU.format3
                       "Field %s belongs to record type %s, whereas field %s does not"
                       f.str
                       record.typename.str
                       f'.str
             in
             raise_error (Errors.Fatal_FieldsNotBelongToSameRecordType, msg) rg
    in
    let () = List.iter check_field (List.tl fields)
    in
    record

(* TODO : Patterns should be checked that there are no incompatible type ascriptions *)
(* and these type ascriptions should not be dropped !!!                              *)
let rec desugar_data_pat env p is_mut : (env_t * bnd * list<Syntax.pat>) =
  let check_linear_pattern_variables pats r =
    // returns the set of pattern variables
    let rec pat_vars p = match p.v with
      | Pat_dot_term _
      | Pat_wild _
      | Pat_constant _ -> S.no_names
      | Pat_var x -> BU.set_add x S.no_names
      | Pat_cons(_, pats) ->
        let aux out (p, _) =
            let intersection = BU.set_intersect (pat_vars p) out in
            if BU.set_is_empty intersection
            then BU.set_union out (pat_vars p)
            else
              let duplicate_bv = List.hd (BU.set_elements intersection) in
              raise_error ( Errors.Fatal_NonLinearPatternNotPermitted,
                            BU.format1
                              "Non-linear patterns are not permitted. %s appears more than once in this pattern."
                               (duplicate_bv.ppname.idText) )

                          r
        in
        List.fold_left aux S.no_names pats
    in
    // check that the same variables are bound in each pattern
    match pats with
    | [] -> ()
    | [p] -> pat_vars p |> ignore
    | p::ps ->
      let pvars = pat_vars p in
      let aux p =
        if BU.set_eq pvars (pat_vars p) then () else
        let nonlinear_vars = BU.set_symmetric_difference pvars (pat_vars p) in
        let first_nonlinear_var = List.hd (BU.set_elements nonlinear_vars) in
        raise_error ( Errors.Fatal_IncoherentPatterns,
                      BU.format1
                        "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.ppname.idText) )
                    r
      in
      List.iter aux ps
  in

  begin match is_mut, p.pat with
      | false, _
      | true, PatVar _ ->
          ()
      | true, _ ->
          raise_error (Errors.Fatal_LetMutableForVariablesOnly, "let-mutable is for variables only") p.prange
  end;

  let resolvex (l:lenv_t) e x =
    match l |> BU.find_opt (fun y -> y.ppname.idText=x.idText) with
      | Some y -> l, e, y
      | _ ->
        let e, x = if is_mut then push_bv_mutable e x else push_bv e x in
        (x::l), e, x
  in
  let rec aux' (top:bool) (loc:lenv_t) env (p:pattern) =
    let pos q = Syntax.withinfo q p.prange in
    let pos_r r q = Syntax.withinfo q r in
    let orig = p in
    match p.pat with
      | PatOr _ -> failwith "impossible"

      | PatOp op ->
        aux loc env ({ pat = PatVar (mk_ident (compile_op 0 op.idText op.idRange, op.idRange), None); prange = p.prange })

      | PatAscribed(p, (t, tacopt)) ->
        let _ = match tacopt with
                | None -> ()
                | Some _ -> raise_error (Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly, "Type ascriptions within patterns cannot be associated with a tactic") orig.prange
        in
        let loc, env', binder, p, imp = aux loc env p in
        let annot_pat_var p t =
            match p.v with
            | Pat_var x -> {p with v=Pat_var({x with sort=t})}
            | Pat_wild x -> {p with v=Pat_wild({x with sort=t})}
            | _ when top -> p
            | _  -> raise_error (Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly, "Type ascriptions within patterns are only allowed on variables") orig.prange
        in
        let p, binder = match binder with
            | LetBinder _ -> failwith "impossible"
            | LocalBinder(x, aq) ->
              let t = desugar_term env (close_fun env t) in
              (* TODO : This should be a real check instead of just a warning *)
              if (match x.sort.n with | S.Tm_unknown -> false | _ -> true)
              then Errors.log_issue orig.prange (Errors.Warning_MultipleAscriptions, (BU.format3 "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                             (Print.bv_to_string x)
                                             (Print.term_to_string x.sort)
                                             (Print.term_to_string t))) ;
              annot_pat_var p t,
              LocalBinder({x with sort=t}, aq)
        in
        loc, env', binder, p, imp

      | PatWild ->
        let x = S.new_bv (Some p.prange) tun in
        loc, env, LocalBinder(x, None), pos <| Pat_wild x, false

      | PatConst c ->
        let x = S.new_bv (Some p.prange) tun in
        loc, env, LocalBinder(x, None), pos <| Pat_constant c, false

      | PatTvar(x, aq)
      | PatVar (x, aq) ->
        let imp = (aq=Some Implicit) in
        let aq = trans_aqual env aq in
        let loc, env, xbv = resolvex loc env x in
        loc, env, LocalBinder(xbv, aq), pos <| Pat_var xbv, imp

      | PatName l ->
        let l = fail_or env (try_lookup_datacon env) l in
        let x = S.new_bv (Some p.prange) tun in
        loc, env, LocalBinder(x,  None), pos <| Pat_cons(l, []), false

      | PatApp({pat=PatName l}, args) ->
        let loc, env, args = List.fold_right (fun arg (loc,env,args) ->
          let loc, env, _, arg, imp = aux loc env arg in
          (loc, env, (arg, imp)::args)) args (loc, env, []) in
        let l = fail_or env  (try_lookup_datacon env) l in
        let x = S.new_bv (Some p.prange) tun in
        loc, env, LocalBinder(x, None), pos <| Pat_cons(l, args), false

      | PatApp _ -> raise_error (Errors.Fatal_UnexpectedPattern, "Unexpected pattern") p.prange

      | PatList pats ->
        let loc, env, pats = List.fold_right (fun pat (loc, env, pats) ->
          let loc,env,_,pat, _ = aux loc env pat in
          loc, env, pat::pats) pats (loc, env, []) in
        let pat = List.fold_right (fun hd tl ->
            let r = Range.union_ranges hd.p tl.p in
            pos_r r <| Pat_cons(S.lid_as_fv C.cons_lid delta_constant (Some Data_ctor), [(hd, false);(tl, false)])) pats
                        (pos_r (Range.end_range p.prange) <| Pat_cons(S.lid_as_fv C.nil_lid delta_constant (Some Data_ctor), [])) in
        let x = S.new_bv (Some p.prange) tun in
        loc, env, LocalBinder(x, None), pat, false

      | PatTuple(args, dep) ->
        let loc, env, args = List.fold_left (fun (loc, env, pats) p ->
          let loc, env, _, pat, _ = aux loc env p in
          loc, env, (pat, false)::pats) (loc,env,[]) args in
        let args = List.rev args in
        let l = if dep then C.mk_dtuple_data_lid (List.length args) p.prange
                else C.mk_tuple_data_lid (List.length args) p.prange in
        let constr, _ = fail_or env  (Env.try_lookup_lid env) l in
        let l = match constr.n with
          | Tm_fvar fv -> fv
          | _ -> failwith "impossible" in
        let x = S.new_bv (Some p.prange) tun in
        loc, env, LocalBinder(x, None), pos <| Pat_cons(l, args), false

      | PatRecord ([]) ->
        raise_error (Errors.Fatal_UnexpectedPattern, "Unexpected pattern") p.prange

      | PatRecord (fields) ->
        let record = check_fields env fields p.prange in
        let fields = fields |> List.map (fun (f, p) -> (f.ident, p)) in
        let args = record.fields |> List.map (fun (f, _) ->
          match fields |> List.tryFind (fun (g, _) -> f.idText = g.idText) with
            | None -> mk_pattern PatWild p.prange
            | Some (_, p) -> p) in
        let app = mk_pattern (PatApp(mk_pattern (PatName (lid_of_ids (record.typename.ns @ [record.constrname]))) p.prange, args)) p.prange in
        let env, e, b, p, _ = aux loc env app in
        let p = match p.v with
            | Pat_cons(fv, args) -> pos <| Pat_cons(({fv with fv_qual=Some (Record_ctor (record.typename, record.fields |> List.map fst))}), args)
            | _ -> p in
        env, e, b, p, false
  and aux loc env p = aux' false loc env p
  in
  let aux_maybe_or env (p:pattern) =
    let loc = [] in
    match p.pat with
      | PatOr [] -> failwith "impossible"
      | PatOr (p::ps) ->
        let loc, env, var, p, _ = aux' true loc env p in
        let loc, env, ps = List.fold_left (fun (loc, env, ps) p ->
          let loc, env, _, p, _ = aux' true loc env p in
          loc, env, p::ps) (loc, env, []) ps in
        let pats = (p::List.rev ps) in
        env, var, pats
      | _ ->
        let loc, env, vars, pat, b = aux' true loc env p in
        env, vars, [pat]
  in
  let env, b, pats = aux_maybe_or env p in
  check_linear_pattern_variables pats p.prange;
  env, b, pats

and desugar_binding_pat_maybe_top top env p is_mut : (env_t * bnd * list<pat>) =
  let mklet x = env, LetBinder(qualify env x, (tun, None)), [] in
  if top
  then match p.pat with
    | PatOp x -> mklet (mk_ident (compile_op 0 x.idText x.idRange, x.idRange))
    | PatVar (x, _) -> mklet x
    | PatAscribed({pat=PatVar (x, _)}, (t, tacopt)) ->
      let tacopt = BU.map_opt tacopt (desugar_term env) in
      (env, LetBinder(qualify env x, (desugar_term env t, tacopt)), [])
    | _ -> raise_error (Errors.Fatal_UnexpectedPattern, "Unexpected pattern at the top-level") p.prange
  else
    let (env, binder, p) = desugar_data_pat env p is_mut in
    let p = match p with
      | [{v=Pat_var _}]
      | [{v=Pat_wild _}] -> []
      | _ -> p in
    (env, binder, p)

and desugar_binding_pat env p = desugar_binding_pat_maybe_top false env p false

and desugar_match_pat_maybe_top _ env pat =
  let (env, _, pat) = desugar_data_pat env pat false in
  (env, pat)

and desugar_match_pat env p = desugar_match_pat_maybe_top false env p

and desugar_term_aq env e : S.term * antiquotations =
    let env = Env.set_expect_typ env false in
    desugar_term_maybe_top false env e

and desugar_term env e : S.term =
    let t, aq = desugar_term_aq env e in
    check_no_aq aq;
    t

and desugar_typ_aq env e : S.term * antiquotations =
    let env = Env.set_expect_typ env true in
    desugar_term_maybe_top false env e

and desugar_typ env e : S.term =
    let t, aq = desugar_typ_aq env e in
    check_no_aq aq;
    t

and desugar_machine_integer env repr (signedness, width) range =
  let tnm = "FStar." ^
    (match signedness with | Unsigned -> "U" | Signed -> "") ^ "Int" ^
    (match width with | Int8 -> "8" | Int16 -> "16" | Int32 -> "32" | Int64 -> "64")
  in
  //we do a static check of integer constants
  //and coerce them to the appropriate type using the internal coercion
  // __uint_to_t or __int_to_t
  //Rather than relying on a verification condition to check this trivial property
  if not (within_bounds repr signedness width)
  then FStar.Errors.log_issue
                    range
                    (Errors.Error_OutOfRange,
                     BU.format2 "%s is not in the expected range for %s" repr tnm);
  let private_intro_nm = tnm ^
    ".__" ^ (match signedness with | Unsigned -> "u" | Signed -> "") ^ "int_to_t"
  in
  let intro_nm = tnm ^
    "." ^ (match signedness with | Unsigned -> "u" | Signed -> "") ^ "int_to_t"
  in
  let lid = lid_of_path (path_of_text intro_nm) range in
  let lid =
    match Env.try_lookup_lid env lid with
    | Some (intro_term, _) ->
      begin match intro_term.n with
        | Tm_fvar fv ->
          let private_lid = lid_of_path (path_of_text private_intro_nm) range in
          let private_fv = S.lid_as_fv private_lid (U.incr_delta_depth fv.fv_delta) fv.fv_qual in
          {intro_term with n=Tm_fvar private_fv}
        | _ ->
          failwith ("Unexpected non-fvar for " ^ intro_nm)
      end
    | None ->
      raise_error (Errors.Fatal_UnexpectedNumericLiteral, (BU.format1 "Unexpected numeric literal.  Restart F* to load %s." tnm)) range in
  let repr = S.mk (Tm_constant (Const_int (repr, None))) None range in
  S.mk (Tm_app (lid, [repr, as_implicit false])) None range

and desugar_name mk setpos (env: env_t) (resolve: bool) (l: lid) : S.term =
    let tm, mut, attrs = fail_or env ((if resolve then Env.try_lookup_lid_with_attributes else Env.try_lookup_lid_with_attributes_no_resolve) env) l in
    let warn_if_deprecated (attrs:list<attribute>) :unit =
      List.iter (fun a -> match a.n with
        | Tm_app ({ n = Tm_fvar fv }, args) when lid_equals fv.fv_name.v C.deprecated_attr ->
          let msg = (Print.term_to_string tm) ^ " is deprecated" in
          let msg =
            if List.length args > 0 then
              (match (fst (List.hd args)).n with
               | Tm_constant (Const_string (s, _)) when not (trim_string s = "") -> msg ^ ", use "  ^ s ^ " instead"
               | _ -> msg)
            else msg
          in
          log_issue (range_of_lid l) (Warning_DeprecatedDefinition, msg)
        | Tm_fvar fv when lid_equals fv.fv_name.v C.deprecated_attr ->
          let msg = (Print.term_to_string tm) ^ " is deprecated" in
          log_issue (range_of_lid l) (Warning_DeprecatedDefinition, msg)
        | _ -> ()) attrs
    in
    warn_if_deprecated attrs;
    let tm = setpos tm in
    if mut then mk <| Tm_meta (mk_ref_read tm, Meta_desugared Mutable_rval)
    else tm

and desugar_attributes (env:env_t) (cattributes:list<term>) : list<cflags> =
    let desugar_attribute t =
        match (unparen t).tm with
            | Var ({str="cps"}) -> CPS
            | _ -> raise_error (Errors.Fatal_UnknownAttribute, "Unknown attribute " ^ term_to_string t) t.range
    in List.map desugar_attribute cattributes

and desugar_term_maybe_top (top_level:bool) (env:env_t) (top:term) : S.term * antiquotations =
  let mk e = S.mk e None top.range in
  let noaqs = [] in
  let join_aqs aqs = List.flatten aqs in
  let setpos e = {e with pos=top.range} in
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

    | Op({idText = "=!="; idRange=r}, args) ->
      let e = mk_term (Op(Ident.mk_ident ("==", r), args)) top.range top.level in
      desugar_term_aq env (mk_term(Op(Ident.mk_ident ("~",r), [e])) top.range top.level)

    (* if op_Star has not been rebound, then it's reserved for tuples *)
    | Op(op_star, [_;_]) when
      Ident.text_of_id op_star = "*" &&
      (op_as_term env 2 top.range op_star |> Option.isNone) ->
      (* See the comment in parse.mly to understand why this implicitly relies
       * on the presence of a Paren node in the AST. *)
      let rec flatten t = match t.tm with
        // * is left-associative
        | Op({idText = "*"}, [t1;t2]) -> flatten t1 @ [ t2 ]
        | _ -> [t]
      in
      let targs, aqs = flatten (unparen top) |>
                            List.map (fun t -> let t', aq = desugar_typ_aq env t in as_arg t', aq) |>
                            List.unzip in
      let tup, _ = fail_or env (Env.try_lookup_lid env) (C.mk_tuple_lid (List.length targs) top.range) in
      mk (Tm_app(tup, targs)), join_aqs aqs

    | Tvar a ->
      setpos <| fst (fail_or2 (try_lookup_id env) a), noaqs

    | Uvar u ->
        raise_error (Errors.Fatal_UnexpectedUniverseVariable, "Unexpected universe variable " ^ text_of_id u ^ " in non-universe context") top.range

    | Op(s, args) ->
      begin match op_as_term env (List.length args) top.range s with
        | None -> raise_error (Errors.Fatal_UnepxectedOrUnboundOperator, "Unexpected or unbound operator: " ^ Ident.text_of_id s) top.range
        | Some op ->
            if List.length args > 0 then
              let args, aqs = args |> List.map (fun t -> let t', s = desugar_term_aq env t in
                                                         (t', None), s) |> List.unzip in
              mk (Tm_app(op, args)), join_aqs aqs
            else
              op, noaqs
      end

    | Construct (n, [(a, _)]) when n.str = "SMTPat" ->
        desugar_term_maybe_top top_level env ({top with tm = App ({top with tm = Var (lid_of_path ["Prims";"smt_pat"] top.range)}, a, Nothing)})

    | Construct (n, [(a, _)]) when n.str = "SMTPatT" ->
        Errors.log_issue top.range (Errors.Warning_SMTPatTDeprecated, "SMTPatT is deprecated; please just use SMTPat");
        desugar_term_maybe_top top_level env ({top with tm = App ({top with tm = Var (lid_of_path ["Prims";"smt_pat"] top.range)}, a, Nothing)})

    | Construct (n, [(a, _)]) when n.str = "SMTPatOr" ->
        desugar_term_maybe_top top_level env ({top with tm = App ({top with tm = Var (lid_of_path ["Prims";"smt_pat_or"] top.range)}, a, Nothing)})

    | Name {str="Type0"}  -> mk (Tm_type U_zero), noaqs
    | Name {str="Type"}   -> mk (Tm_type U_unknown), noaqs
    | Construct ({str="Type"}, [t, UnivApp]) -> mk (Tm_type (desugar_universe t)), noaqs
    | Name {str="Effect"} -> mk (Tm_constant Const_effect), noaqs
    | Name {str="True"}   -> S.fvar (Ident.set_lid_range Const.true_lid top.range) delta_constant None, noaqs
    | Name {str="False"}   -> S.fvar (Ident.set_lid_range Const.false_lid top.range) delta_constant None, noaqs
    | Projector (eff_name, {idText = txt})
      when is_special_effect_combinator txt && Env.is_effect_name env eff_name ->
      let _ = Env.fail_if_qualified_by_curmodule env eff_name in
      (* TODO : would it be possible to normalize the effect name at that point so that *)
      (* we get back the original effect definition instead of an effect abbreviation *)
      begin match try_lookup_effect_defn env eff_name with
        | Some ed ->
          let lid = U.dm4f_lid ed txt in
          S.fvar lid (Delta_constant_at_level 1) None, noaqs
        | None ->
          failwith (BU.format2 "Member %s of effect %s is not accessible \
                                (using an effect abbreviation instead of the original effect ?)"
                               (Ident.text_of_lid eff_name)
                               txt)
      end

    | Var l
    | Name l ->
      let _ = Env.fail_if_qualified_by_curmodule env l in
      desugar_name mk setpos env true l, noaqs

    | Projector (l, i) ->
      let _ = Env.fail_if_qualified_by_curmodule env l in
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
        raise_error (Errors.Fatal_EffectNotFound, (BU.format1 "Data constructor or effect %s not found" l.str)) top.range
      end

    | Discrim lid ->
      let _ = Env.fail_if_qualified_by_curmodule env lid in
      begin match Env.try_lookup_datacon env lid with
      | None ->
        raise_error (Errors.Fatal_DataContructorNotFound, (BU.format1 "Data constructor %s not found" lid.str)) top.range
      | _ ->
        let lid' = U.mk_discriminator lid in
        desugar_name mk setpos env true lid', noaqs
      end

    | Construct(l, args) ->
        let _ = Env.fail_if_qualified_by_curmodule env l in
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
                  arg_withimp_e imp te, aq) args |> List.unzip in
                let head = if universes = [] then head else mk (Tm_uinst(head, universes)) in
                mk (Tm_app (head, args)), join_aqs aqs
            end
        | None ->
            let err =
              match Env.try_lookup_effect_name env l with
              | None -> (Errors.Fatal_ConstructorNotFound, ("Constructor " ^ l.str ^ " not found"))
              | Some _ -> (Errors.Fatal_UnexpectedEffect, ("Effect " ^ l.str ^ " used at an unexpected position"))
            in
            raise_error err top.range
        end

    | Sum(binders, t) ->
      let env, _, targs = List.fold_left (fun (env, tparams, typs) b ->
                let xopt, t = desugar_binder env b in
                let env, x =
                    match xopt with
                    | None -> env, S.new_bv (Some top.range) tun
                    | Some x -> push_bv env x in
                (env, tparams@[{x with sort=t}, None], typs@[as_arg <| no_annot_abs tparams t]))
        (env, [], [])
        (binders@[mk_binder (NoName t) t.range Type_level None]) in
      let tup, _ = fail_or env  (try_lookup_lid env) (C.mk_dtuple_lid (List.length targs) top.range) in
      mk <| Tm_app(tup, targs), noaqs

    | Product(binders, t) ->
      let bs, t = uncurry binders t in
      let rec aux env bs = function
        | [] ->
          let cod = desugar_comp top.range env t in
          setpos <| U.arrow (List.rev bs) cod

        | hd::tl ->
          let bb = desugar_binder env hd in
          let b, env = as_binder env hd.aqual bb in
          aux env (b::bs) tl in
      aux env [] bs, noaqs

    | Refine(b, f) ->
      begin match desugar_binder env b with
        | (None, _) -> failwith "Missing binder in refinement"

        | b ->
          let (x, _), env = as_binder env None b in
          let f = desugar_formula env f in
          setpos <| U.refine x f, noaqs
      end

    | Abs(binders, body) ->
      let binders = binders |> List.map replace_unit_pattern in
      let _, ftv = List.fold_left (fun (env, ftvs) pat ->
        match pat.pat with
          | PatAscribed(_, (t, None)) -> env, free_type_vars env t@ftvs
          | PatAscribed(_, (t, Some tac)) -> env, free_type_vars env t@free_type_vars env tac@ftvs
          | _ -> env, ftvs) (env, []) binders in
      let ftv = sort_ftv ftv in
      let binders = (ftv |> List.map (fun a ->
                        mk_pattern (PatTvar(a, Some AST.Implicit)) top.range))
                    @binders in //close over the free type variables
      (*
         fun (P1 x1) (P2 x2) (P3 x3) -> e

            is desugared to

         fun y1 y2 y3 -> match (y1, y2, y3) with
                | (P1 x1, P2 x2, P3 x3) -> [[e]]
      *)
      let rec aux env bs sc_pat_opt =
        function
        | [] ->
            let body, aq = desugar_term_aq env body in
            let body = match sc_pat_opt with
            | Some (sc, pat) ->
                let body = Subst.close (S.pat_bvs pat |> List.map S.mk_binder) body in
                S.mk (Tm_match(sc, [(pat, None, body)])) None body.pos
            | None -> body in
            setpos (no_annot_abs (List.rev bs) body), aq

        | p::rest ->
            let env, b, pat = desugar_binding_pat env p in
            let pat =
                match pat with
                | [] -> None
                | [p] -> Some p
                | _ ->
                  raise_error (Errors.Fatal_UnsupportedDisjuctivePatterns, "Disjunctive patterns are not supported in abstractions") p.prange
            in
            let b, sc_pat_opt =
                match b with
                | LetBinder _ -> failwith "Impossible"
                | LocalBinder (x, aq) ->
                    let sc_pat_opt =
                        match pat, sc_pat_opt with
                        | None, _ -> sc_pat_opt
                        | Some p, None -> Some (S.bv_to_name x, p)
                        | Some p, Some (sc, p') -> begin
                          match sc.n, p'.v with
                          | Tm_name _, _ ->
                            let tup2 = S.lid_as_fv (C.mk_tuple_data_lid 2 top.range) delta_constant (Some Data_ctor) in
                            let sc = S.mk (Tm_app(mk (Tm_fvar tup2), [as_arg sc; as_arg <| S.bv_to_name x])) None top.range in
                            let p = withinfo (Pat_cons(tup2, [(p', false);(p, false)])) (Range.union_ranges p'.p p.p) in
                            Some(sc, p)
                          | Tm_app(_, args), Pat_cons(_, pats) ->
                            let tupn = S.lid_as_fv (C.mk_tuple_data_lid (1 + List.length args) top.range) delta_constant (Some Data_ctor) in
                            let sc = mk (Tm_app(mk (Tm_fvar tupn), args@[as_arg <| S.bv_to_name x])) in
                            let p = withinfo (Pat_cons(tupn, pats@[(p, false)])) (Range.union_ranges p'.p p.p) in
                            Some(sc, p)
                          | _ -> failwith "Impossible"
                          end
                    in
                    (x, aq), sc_pat_opt
            in
                aux env (b::bs) sc_pat_opt rest
       in
       aux env [] None binders

    | App (_, _, UnivApp) ->
       let rec aux universes e = match (unparen e).tm with
           | App(e, t, UnivApp) ->
               let univ_arg = desugar_universe t in
               aux (univ_arg::universes) e
            | _ ->
                let head, aq = desugar_term_aq env e in
                mk (Tm_uinst(head, universes)), aq
       in aux [] top

    | App _ ->
      let rec aux args aqs e = match (unparen e).tm with
        | App(e, t, imp) when imp <> UnivApp ->
          let t, aq = desugar_term_aq env t in
          let arg = arg_withimp_e imp t in
          aux (arg::args) (aq::aqs) e
        | _ ->
          let head, aq = desugar_term_aq env e in
          mk (Tm_app(head, args)), join_aqs (aq::aqs) in
      aux [] [] top

    | Bind(x, t1, t2) ->
      let xpat = AST.mk_pattern (AST.PatVar(x, None)) x.idRange in
      let k = AST.mk_term (Abs([xpat], t2)) t2.range t2.level in
      let bind_lid = Ident.lid_of_path ["bind"] x.idRange in
      let bind = AST.mk_term (AST.Var bind_lid) x.idRange AST.Expr in
      desugar_term_aq env (AST.mkExplicitApp bind [t1; k] top.range)

    | Seq(t1, t2) ->
      (* Convert it to a letbinding, desugar it, and then slap a Meta_desugared sequence on it to keep track of this *)
      (* TODO: GM: Maybe we don't really care about that *)
      let t = mk_term (Let(NoLetQualifier, [None, (mk_pattern PatWild t1.range,t1)], t2)) top.range Expr in
      let tm, s = desugar_term_aq env t in
      mk (Tm_meta(tm, Meta_desugared Sequence)), s

    | LetOpen (lid, e) ->
      let env = Env.push_namespace env lid in
      (if Env.expect_typ env then desugar_typ_aq else desugar_term_aq) env e

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
                        | PatAscribed({pat=PatVar(id,_)}, t) ->
                            if top_level
                            then attr_opt, (Inr (qualify env id), [], Some t), def
                            else attr_opt, (Inl id, [], Some t), def
                        | PatVar(id, _) ->
                            if top_level
                            then attr_opt, (Inr (qualify env id), [], None), def
                            else attr_opt, (Inl id, [], None), def
                        | _ -> raise_error (Errors.Fatal_UnexpectedLetBinding, "Unexpected let binding") p.prange
                      end)
        in

        //Generate fresh names and populate an env' with recursive bindings
        //below, we use env' instead of env, only if is_rec
        let env', fnames, rec_bindings =
          List.fold_left (fun (env, fnames, rec_bindings) (_attr_opt, (f, _, _), _) ->
            let env, lbname, rec_bindings = match f with
              | Inl x ->
                let env, xx = push_bv env x in
                env, Inl xx, S.mk_binder xx::rec_bindings
              | Inr l ->
                push_top_level_rec_binding env l.ident S.delta_equational, Inr l, rec_bindings in
            env, (lbname::fnames), rec_bindings) (env, [], []) funs
        in

        let fnames = List.rev fnames in
        let rec_bindings = List.rev rec_bindings in
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
        let desugar_one_def env lbname (attrs_opt, (_, args, result_t), def) =
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
                              raise_error (Errors.Fatal_ComputationTypeNotAllowed, "Computation type annotations are only permitted on let-bindings \
                                             without inlined patterns; \
                                             replace this pattern with a variable") p.prange in
                         t
                    else if Options.ml_ish () //we're type-checking the compiler itself, e.g.
                    && Option.isSome (Env.try_lookup_effect_name env C.effect_ML_lid) //ML is in scope (not still in prims, e.g)
                    && (not is_rec || List.length args <> 0) //and we don't have something like `let rec f : t -> t' = fun x -> e`
                    then AST.ml_comp t
                    else AST.tot_comp t
                in
                mk_term (Ascribed(def, t, tacopt)) def.range Expr
            in
            let def = match args with
                 | [] -> def
                 | _ -> mk_term (un_curry_abs args def) top.range top.level in
            let body = desugar_term env def in
            let lbname = match lbname with
                | Inl x -> Inl x
                | Inr l -> Inr (S.lid_as_fv l (incr_delta_qualifier body) None) in
            let body = if is_rec then Subst.close rec_bindings body else body in
            let attrs = match attrs_opt with
              | None -> []
              | Some l -> List.map (desugar_term env) l
            in
            mk_lb (attrs, lbname, tun, body, pos)
        in
        let lbs = List.map2 (desugar_one_def (if is_rec then env' else env)) fnames funs in
        let body, aq = desugar_term_aq env' body in
        mk <| (Tm_let((is_rec, lbs), Subst.close rec_bindings body)), aq
      in
      //end ds_let_rec_or_app

      let ds_non_rec attrs_opt pat t1 t2 =
        let attrs =
            match attrs_opt with
            | None -> []
            | Some l -> List.map (desugar_term env) l
        in
        let t1 = desugar_term env t1 in
        let is_mutable = qual = Mutable in
        // a let-mutable is a hidden ref allocation
        let t1 = if is_mutable
                 then mk_ref_alloc t1
                 else t1
        in
        let env, binder, pat = desugar_binding_pat_maybe_top top_level env pat is_mutable in
        let tm, aq =
            match binder with
            | LetBinder(l, (t, _tacopt)) -> //_tacopt must be None here
              let body, aq = desugar_term_aq env t2 in
              let fv = S.lid_as_fv l (incr_delta_qualifier t1) None in
              mk <| Tm_let((false, [mk_lb (attrs, Inr fv, t, t1, t1.pos)]), body), aq

            | LocalBinder (x,_) ->
              let body, aq = desugar_term_aq env t2 in
              let body = match pat with
                | []
                | [{v=Pat_wild _}] -> body
                | _ ->
                  S.mk (Tm_match(S.bv_to_name x, desugar_disjunctive_pattern pat None body)) None top.range in
              mk <| Tm_let((false, [mk_lb (attrs, Inl x, x.sort, t1, t1.pos)]), Subst.close [S.mk_binder x] body), aq
        in
        if is_mutable
        then mk <| Tm_meta (tm, Meta_desugared Mutable_alloc), aq
        else tm, aq
      in

      let attrs, (head_pat, defn) = List.hd lbs in
      if is_rec
      || is_app_pattern head_pat
      then ds_let_rec_or_app()
      else ds_non_rec attrs head_pat defn body

    | If(t1, t2, t3) ->
      let x = Syntax.new_bv (Some t3.range) S.tun in
      let t_bool = mk (Tm_fvar(S.lid_as_fv C.bool_lid delta_constant None)) in
      let t1', aq1 = desugar_term_aq env t1 in
      let t2', aq2 = desugar_term_aq env t2 in
      let t3', aq3 = desugar_term_aq env t3 in
      mk (Tm_match(t1',
                    [(withinfo (Pat_constant (Const_bool true)) t2.range, None, t2');
                     (withinfo (Pat_wild x) t3.range, None, t3')])), join_aqs [aq1;aq2;aq3]

    | TryWith(e, branches) ->
      let r = top.range in
      let handler = mk_function branches r r in
      let body = mk_function [(mk_pattern (PatConst Const_unit) r, None, e)] r r in
      let a1 = mk_term (App(mk_term (Var C.try_with_lid) r top.level, body, Nothing)) r  top.level in
      let a2 = mk_term (App(a1, handler, Nothing)) r top.level in
      desugar_term_aq env a2

    | Match(e, branches) ->
      let desugar_branch (pat, wopt, b) =
        let env, pat = desugar_match_pat env pat in
        let wopt = match wopt with
          | None -> None
          | Some e -> Some (desugar_term env e) in
        let b, aq = desugar_term_aq env b in
        desugar_disjunctive_pattern pat wopt b, aq
      in
      let e, aq = desugar_term_aq env e in
      let brs, aqs = List.map desugar_branch branches |> List.unzip |> (fun (x, y) -> (List.flatten x, y)) in
      mk <| Tm_match(e, brs), join_aqs (aq::aqs)

    | Ascribed(e, t, tac_opt) ->
      let annot = if is_comp_type env t
                  then Inr (desugar_comp t.range env t)
                  else Inl (desugar_term env t) in
      let tac_opt = BU.map_opt tac_opt (desugar_term env) in
      let e, aq = desugar_term_aq env e in
      mk <| Tm_ascribed(e, (annot, tac_opt), None), aq

    | Record(_, []) ->
      raise_error (Errors.Fatal_UnexpectedEmptyRecord, "Unexpected empty record") top.range

    | Record(eopt, fields) ->
      let record = check_fields env fields top.range in
      (* Namespace qualifier given by the user, needed to requalify fields in 'recterm' (MUST NOT be already resolved, since it will be re-resolved afterwards and thus may undergo rewriting e.g. by module abbrev *)
      let user_ns = let (f, _) = List.hd fields in f.ns in
      let get_field xopt f =
        let found = fields |> BU.find_opt (fun (g, _) -> f.idText = g.ident.idText) in
        let fn = lid_of_ids (user_ns @ [f]) in
        match found with
          | Some (_, e) -> (fn, e)
          | None ->
            match xopt with
              | None ->
                raise_error (Errors.Fatal_MissingFieldInRecord, (BU.format2 "Field %s of record type %s is missing" f.idText record.typename.str)) top.range
              | Some x ->
                (fn, mk_term (Project(x, fn)) x.range x.level) in

      let user_constrname = lid_of_ids (user_ns @ [record.constrname]) in
      let recterm = match eopt with
        | None ->
          Construct(user_constrname,
                    record.fields |> List.map (fun (f, _) ->
                    snd <| get_field None f, Nothing))

        | Some e ->
          let x = FStar.Ident.gen e.range in
          let xterm = mk_term (Var (lid_of_ids [x])) x.idRange Expr in
          let record = Record(None, record.fields |> List.map (fun (f, _) -> get_field (Some xterm) f)) in
          Let(NoLetQualifier, [None, (mk_pattern (PatVar (x, None)) x.idRange, e)], mk_term record top.range top.level) in

      let recterm = mk_term recterm top.range top.level in
      let e, s = desugar_term_aq env recterm in
      begin match e.n with
        | Tm_app ({n=Tm_fvar fv}, args) ->
          mk <| Tm_app(S.fvar (Ident.set_lid_range fv.fv_name.v e.pos) delta_constant
                             (Some (Record_ctor(record.typename, record.fields |> List.map fst))),
                      args), s
        | _ -> e, s
      end

    | Project(e, f) ->
      let _ = Env.fail_if_qualified_by_curmodule env f in
      let constrname, is_rec = fail_or env  (try_lookup_dc_by_field_name env) f in
      let e, s = desugar_term_aq env e in
      let projname = mk_field_projector_name_from_ident constrname f.ident in
      let qual = if is_rec then Some (Record_projector (constrname, f.ident)) else None in
      mk <| Tm_app(S.fvar (Ident.set_lid_range projname (range_of_lid f)) (Delta_equational_at_level 1) qual, [as_arg e]), s

    | NamedTyp(_, e) ->
        desugar_term_aq env e

    | Paren e -> failwith "impossible"

    | VQuote e ->
      (* Just get the lid and replace the VQuote for a string of it *)
      let tm = desugar_term env e in
      begin match (Subst.compress tm).n with
      | Tm_fvar fv -> { U.exp_string (string_of_lid (lid_of_fv fv)) with pos = e.range }, noaqs
      | _ ->
        raise_error (Fatal_UnexpectedTermVQuote, ("VQuote, expected an fvar, got: " ^ P.term_to_string tm)) top.range
      end

    | Quote (e, Static) ->
      let tm, vts = desugar_term_aq env e in
      let qi = { qkind = Quote_static
               ; antiquotes = vts
               } in
      mk <| Tm_quoted (tm, qi), noaqs

    | Antiquote e ->
        let bv = S.new_bv (Some e.range) S.tun in
        (* We use desugar_term, so the there can be double antiquotations *)
        S.bv_to_name bv, [(bv, desugar_term env e)]

    | Quote (e, Dynamic) ->
      let qi = { qkind = Quote_dynamic
               ; antiquotes = []
               } in
      mk <| Tm_quoted (desugar_term env e, qi), noaqs

    | _ when (top.level=Formula) -> desugar_formula env top, noaqs

    | _ ->
      raise_error (Fatal_UnexpectedTerm, ("Unexpected term: " ^ term_to_string top)) top.range
  end

and not_ascribed t =
    match t.tm with
    | Ascribed _ -> false
    | _ ->  true

and desugar_args env args =
    args |> List.map (fun (a, imp) -> arg_withimp_e imp (desugar_term env a))

and desugar_comp r env t =
    let fail : (Errors.raw_error * string) -> 'a = fun err -> raise_error err r in
    let is_requires (t, _) = match (unparen t).tm with
      | Requires _ -> true
      | _ -> false
    in
    let is_ensures (t, _) = match (unparen t).tm with
      | Ensures _ -> true
      | _ -> false
    in
    let is_app head (t, _) = match (unparen t).tm with
      | App({tm=Var d}, _, _) -> d.ident.idText = head
      | _ -> false
    in
    let is_smt_pat (t,_) =
      match (unparen t).tm with
      // TODO: remove this first match once we fully migrate
      | Construct (cons, [{tm=Construct (smtpat, _)}, _; _]) ->
        Ident.lid_equals cons C.cons_lid &&
        BU.for_some (fun s -> smtpat.str = s)
          (* the smt pattern does not seem to be disambiguated yet at this point *)
          ["SMTPat"; "SMTPatT"; "SMTPatOr"]
          (* [C.smtpat_lid ; C.smtpatT_lid ; C.smtpatOr_lid] *)

      | Construct (cons, [{tm=Var smtpat}, _; _]) ->
        Ident.lid_equals cons C.cons_lid &&
        BU.for_some (fun s -> smtpat.str = s)
          (* the smt pattern does not seem to be disambiguated yet at this point *)
          ["smt_pat" ; "smt_pat_or"]
          (* [C.smtpat_lid ; C.smtpatT_lid ; C.smtpatOr_lid] *)
      | _ -> false
    in
    let is_decreases = is_app "decreases" in
    let pre_process_comp_typ (t:AST.term) =
      let head, args = head_and_args t in
      match head.tm with
      | Name lemma when (lemma.ident.idText = "Lemma") ->
        (* need to add the unit result type and the empty smt_pat list, if n *)
        let unit_tm = mk_term (Name C.unit_lid) t.range Type_level, Nothing in
        let nil_pat = mk_term (Name C.nil_lid) t.range Expr, Nothing in
        let req_true =
          let req = Requires (mk_term (Name C.true_lid) t.range Formula, None) in
          mk_term req t.range Type_level, Nothing
        in
        (* The postcondition for Lemma is thunked, to allow to assume the precondition
         * (c.f. #57), so add the thunking here *)
        let thunk_ens_ (ens : AST.term) : AST.term =
            let wildpat = mk_pattern PatWild ens.range in
            mk_term (Abs ([wildpat], ens)) ens.range Expr
        in
        let thunk_ens (e, i) = (thunk_ens_ e, i) in
        let fail_lemma () =
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
             let msg = String.concat "\n\t" expected_one_of in
             raise_error (Errors.Fatal_InvalidLemmaArgument, "Invalid arguments to 'Lemma'; expected one of the following:\n\t" ^ msg) t.range
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
        let head_and_attributes = fail_or env (Env.try_lookup_effect_name_and_attributes env) lemma in
        head_and_attributes, args

      | Name l when Env.is_effect_name env l ->
        (* we have an explicit effect annotation ... no need to add anything *)
        fail_or env (Env.try_lookup_effect_name_and_attributes env) l, args


      (* we're right at the beginning of Prims, when Tot isn't yet fully defined *)
      | Name l when (lid_equals (Env.current_module env) C.prims_lid
                          && l.ident.idText = "Tot") ->
        (* we have an explicit effect annotation ... no need to add anything *)
        (Ident.set_lid_range Const.effect_Tot_lid head.range,  []), args

      (* we're right at the beginning of Prims, when GTot isn't yet fully defined *)
      | Name l when (lid_equals (Env.current_module env) C.prims_lid
                          && l.ident.idText = "GTot") ->
        (* we have an explicit effect annotation ... no need to add anything *)
        (Ident.set_lid_range Const.effect_GTot_lid head.range, []), args

      | Name l when (l.ident.idText="Type"
                      || l.ident.idText="Type0"
                      || l.ident.idText="Effect") ->
        (* the default effect for Type is always Tot *)
        (Ident.set_lid_range Const.effect_Tot_lid head.range, []), [t, Nothing]

      | _ ->
        let default_effect =
          if Options.ml_ish ()
          then Const.effect_ML_lid
          else (if Options.warn_default_effects()
                then FStar.Errors.log_issue head.range (Errors.Warning_UseDefaultEffect, "Using default effect Tot");
                Const.effect_Tot_lid) in
        (Ident.set_lid_range default_effect head.range, []), [t, Nothing]
    in
    let (eff, cattributes), args = pre_process_comp_typ t in
    if List.length args = 0
    then fail (Errors.Fatal_NotEnoughArgsToEffect, (BU.format1 "Not enough args to effect %s" (Print.lid_to_string eff)));
    let is_universe (_, imp) = imp = UnivApp in
    let universes, args = BU.take is_universe args in
    let universes = List.map (fun (u, imp) -> desugar_universe u) universes in
    let result_arg, rest = List.hd args, List.tl args in
    let result_typ = desugar_typ env (fst result_arg) in
    let rest = desugar_args env rest in
    let dec, rest =
      let is_decrease (t, _) = match t.n with
        | Tm_app({n=Tm_fvar fv}, [_]) -> S.fv_eq_lid fv C.decreases_lid
        | _ -> false
      in
      rest |> List.partition is_decrease
    in

    let decreases_clause =
      dec |> List.map (fun (t, _) ->
        match t.n with
        | Tm_app(_, [(arg, _)]) -> DECREASES arg
        | _ -> failwith "impos")
    in
    let no_additional_args =
        (* F# complains about not being able to use = on some types.. *)
        let is_empty (l:list<'a>) = match l with | [] -> true | _ -> false in
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
        else if lid_equals eff C.effect_ML_lid    then [MLEFFECT]
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
                  S.fvar (Ident.set_lid_range Const.pattern_lid pat.pos) delta_constant None
                in
                S.mk_Tm_app nil [(pattern, Some S.imp_tag)] None pat.pos
              | _ -> pat
            in
            [req; ens; (S.mk (Tm_meta(pat, Meta_desugared Meta_smt_pat)) None pat.pos, aq)]
          | _ -> rest
        else rest
      in
      mk_Comp ({comp_univs=universes;
                effect_name=eff;
                result_typ=result_typ;
                effect_args=rest;
                flags=flags@decreases_clause})

and desugar_formula env (f:term) : S.term =
  let connective s = match s with
    | "/\\"  -> Some C.and_lid
    | "\\/"  -> Some C.or_lid
    | "==>"  -> Some C.imp_lid
    | "<==>" -> Some C.iff_lid
    | "~"    -> Some C.not_lid
    | _ -> None in
  let mk t = S.mk t None f.range in
  let setpos t = {t with pos=f.range} in
  let desugar_quant (q:lident) b pats body =
    let tk = desugar_binder env ({b with blevel=Formula}) in
    let desugar_pats env pats = List.map (fun es -> es |> List.map (fun e -> arg_withimp_t Nothing <| desugar_term env e)) pats in
    match tk with
      | Some a, k ->
        let env, a = push_bv env a in
        let a = {a with sort=k} in
        let pats = desugar_pats env pats in
        let body = desugar_formula env body in
        let body = match pats with
          | [] -> body
          | _ -> mk (Tm_meta (body, Meta_pattern pats)) in
        let body = setpos <| no_annot_abs [S.mk_binder a] body in
        mk <| Tm_app (S.fvar (set_lid_range q b.brange) (Delta_constant_at_level 1) None, [as_arg body])

      | _ -> failwith "impossible" in

 let push_quant (q:(list<AST.binder> * list<(list<AST.term>)> * AST.term) -> AST.term') (binders:list<AST.binder>) pats (body:term) =
    match binders with
    | b::(b'::_rest) ->
      let rest = b'::_rest in
      let body = mk_term (q(rest, pats, body)) (Range.union_ranges b'.brange body.range) Formula in
      mk_term (q([b], [], body)) f.range Formula
    | _ -> failwith "impossible" in

  match (unparen f).tm with
    | Labeled(f, l, p) ->
      let f = desugar_formula env f in
      mk <| Tm_meta(f, Meta_labeled(l, f.pos, p))

    | QForall([], _, _)
    | QExists([], _, _) -> failwith "Impossible: Quantifier without binders"

    | QForall((_1::_2::_3), pats, body) ->
      let binders = _1::_2::_3 in
      desugar_formula env (push_quant (fun x -> QForall x) binders pats body)

    | QExists((_1::_2::_3), pats, body) ->
      let binders = _1::_2::_3 in
      desugar_formula env (push_quant (fun x -> QExists x) binders pats body)

    | QForall([b], pats, body) ->
      desugar_quant C.forall_lid b pats body

    | QExists([b], pats, body) ->
      desugar_quant C.exists_lid b pats body

    | Paren f -> failwith "impossible"

    | _ -> desugar_term env f

and typars_of_binders env bs =
    let env, tpars = List.fold_left (fun (env, out) b ->
        let tk = desugar_binder env ({b with blevel=Formula}) in  (* typars follow the same binding conventions as formulas *)
        match tk with
            | Some a, k ->
                let env, a = push_bv env a in
                let a = {a with sort=k} in
                (env, (a, trans_aqual env b.aqual)::out)
            | _ -> raise_error (Errors.Fatal_UnexpectedBinder, "Unexpected binder") b.brange) (env, []) bs in
    env, List.rev tpars

and desugar_binder env b : option<ident> * S.term = match b.b with
  | TAnnotated(x, t)
  | Annotated(x, t) -> Some x, desugar_typ env t
  | TVariable x     -> Some x, mk (Tm_type U_unknown) None x.idRange
  | NoName t        -> None, desugar_typ env t
  | Variable x      -> Some x, tun

and as_binder env imp = function
  | (None, k) -> null_binder k, env
  | (Some a, k) ->
    let env, a = Env.push_bv env a in
    ({a with sort=k}, trans_aqual env imp), env

and trans_aqual env = function
  | Some AST.Implicit -> Some S.imp_tag
  | Some AST.Equality -> Some S.Equality
  | Some (AST.Meta t) -> Some (S.Meta (desugar_term env t))
  | None -> None

// FIXME: Would be nice to add auto-generated docs to these
let mk_data_discriminators quals env datas =
    let quals = quals |> List.filter (function
        | S.NoExtract
        | S.Abstract
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
        { sigel = Sig_declare_typ(disc_name, [], Syntax.tun);
          sigrng = range_of_lid disc_name;// FIXME: Isn't that range wrong? // FIXME: Doc?
          sigquals =  quals [(* S.Logic ; *) S.OnlyName ; S.Discriminator d];
          sigmeta = default_sigmeta;
          sigattrs = []
        })

let mk_indexed_projector_names iquals fvq env lid (fields:list<S.binder>) =
    let p = range_of_lid lid in

    fields |> List.mapi (fun i (x, _) ->
        let field_name, _ = U.mk_field_projector_name lid x i in
        let only_decl =
            lid_equals C.prims_lid  (Env.current_module env)
            || fvq<>Data_ctor
            || Options.dont_gen_projectors (Env.current_module env).str
        in
        let no_decl = Syntax.is_type x.sort in
        let quals q =
            if only_decl
            then S.Assumption::List.filter (function S.Abstract -> false | _ -> true) q
            else q
        in
        let quals =
            let iquals = iquals |> List.filter (function
                | S.NoExtract
                | S.Abstract
                | S.Private -> true
                | _ -> false)
            in
            quals (OnlyName :: S.Projector(lid, x.ppname) :: iquals)
        in
        let decl = { sigel = Sig_declare_typ(field_name, [], Syntax.tun);
                     sigquals = quals;
                     sigrng = range_of_lid field_name;
                     sigmeta = default_sigmeta ;
                     sigattrs = [] } in // FIXME: Doc?
        if only_decl
        then [decl] //only the signature
        else
            let dd =
                if quals |> List.contains S.Abstract
                then Delta_abstract (Delta_equational_at_level 1)
                else (Delta_equational_at_level 1)
            in
            let lb = {
                lbname=Inr (S.lid_as_fv field_name dd None);
                lbunivs=[];
                lbtyp=tun;
                lbeff=C.effect_Tot_lid;
                lbdef=tun;
                lbattrs=[];
                lbpos=Range.dummyRange;
            } in
            let impl = { sigel = Sig_let((false, [lb]), [lb.lbname |> right |> (fun fv -> fv.fv_name.v)]);
                         sigquals = quals;
                         sigrng = p;
                         sigmeta = default_sigmeta;
                         sigattrs = [] } in // FIXME: Doc?
            if no_decl then [impl] else [decl;impl]) |> List.flatten

// FIXME: Would be nice to add auto-generated docs to these
let mk_data_projector_names iquals env se =
  match se.sigel with
  | Sig_datacon(lid, _, t, _, n, _) when (//(not env.iface || env.admitted_iface) &&
                                                not (lid_equals lid C.lexcons_lid)) ->
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
            let iquals =
                if List.contains S.Abstract iquals && not (List.contains S.Private iquals)
                then S.Private::iquals
                else iquals
            in
            let _, rest = BU.first_N n formals in
            mk_indexed_projector_names iquals fv_qual env lid rest
    end

  | _ -> []

let mk_typ_abbrev lid uvs typars kopt t lids quals rng =
    let dd = if quals |> List.contains S.Abstract
             then Delta_abstract (incr_delta_qualifier t)
             else incr_delta_qualifier t in
    let lb = {
        lbname=Inr (S.lid_as_fv lid dd None);
        lbunivs=uvs;
        lbdef=no_annot_abs typars t;
        lbtyp=if is_some kopt then U.arrow typars (S.mk_Total (kopt |> must)) else tun;
        lbeff=C.effect_Tot_lid;
        lbattrs=[];
        lbpos=rng;
    } in
    { sigel = Sig_let((false, [lb]), lids);
      sigquals = quals;
      sigrng = rng;
      sigmeta = default_sigmeta ;
      sigattrs = [] }

let rec desugar_tycon env (d: AST.decl) quals tcs : (env_t * sigelts) =
  let rng = d.drange in
  let tycon_id = function
    | TyconAbstract(id, _, _)
    | TyconAbbrev(id, _, _, _)
    | TyconRecord(id, _, _, _)
    | TyconVariant(id, _, _, _) -> id in
  let binder_to_term b = match b.b with
    | Annotated (x, _)
    | Variable x -> mk_term (Var (lid_of_ids [x])) x.idRange Expr
    | TAnnotated(a, _)
    | TVariable a -> mk_term (Tvar a) a.idRange Type_level
    | NoName t -> t in
  let tot = mk_term (Name (C.effect_Tot_lid)) rng Expr in
  let with_constructor_effect t = mk_term (App(tot, t, Nothing)) t.range t.level in
  let apply_binders t binders =
    let imp_of_aqual (b:AST.binder) = match b.aqual with
        | Some Implicit -> Hash
        | _ -> Nothing in
    List.fold_left (fun out b -> mk_term (App(out, binder_to_term b, imp_of_aqual b)) out.range out.level)
      t binders in
  let tycon_record_as_variant = function
    | TyconRecord(id, parms, kopt, fields) ->
      let constrName = mk_ident("Mk" ^ id.idText, id.idRange) in
      (* it is necessary to mangle field names to avoid capture as they are turned into the formal parameters of the data constructor *)
      let mfields = List.map (fun (x,t,_) -> mk_binder (Annotated(mangle_field_name x,t)) x.idRange Expr None) fields in
      let result = apply_binders (mk_term (Var (lid_of_ids [id])) id.idRange Type_level) parms in
      let constrTyp = mk_term (Product(mfields, with_constructor_effect result)) id.idRange Type_level in
      //let _ = BU.print_string (BU.format2 "Translated record %s to constructor %s\n" (id.idText) (term_to_string constrTyp)) in
      // FIXME: docs of individual fields are dropped
      TyconVariant(id, parms, kopt, [(constrName, Some constrTyp, None, false)]), fields |> List.map (fun (x, _, _) -> unmangle_field_name x)
    | _ -> failwith "impossible" in
  let desugar_abstract_tc quals _env mutuals = function
    | TyconAbstract(id, binders, kopt) ->
      let _env', typars = typars_of_binders _env binders in
      let k = match kopt with
        | None -> U.ktype
        | Some k -> desugar_term _env' k in
      let tconstr = apply_binders (mk_term (Var (lid_of_ids [id])) id.idRange Type_level) binders in
      let qlid = qualify _env id in
      let typars = Subst.close_binders typars in
      let k = Subst.close typars k in
      let se = { sigel = Sig_inductive_typ(qlid, [], typars, k, mutuals, []);
                 sigquals = quals;
                 sigrng = rng;
                 sigmeta = default_sigmeta  ;
                 sigattrs = [] } in
      let _env = Env.push_top_level_rec_binding _env id S.delta_constant in
      let _env2 = Env.push_top_level_rec_binding _env' id S.delta_constant in
      _env, _env2, se, tconstr
    | _ -> failwith "Unexpected tycon" in
  let push_tparams env bs =
    let env, bs = List.fold_left (fun (env, tps) (x, imp) ->
        let env, y = Env.push_bv env x.ppname in
        env, (y, imp)::tps) (env, []) bs in
    env, List.rev bs in
  match tcs with
    | [TyconAbstract(id, bs, kopt)] ->
        let kopt = match kopt with
            | None -> Some (tm_type_z id.idRange)
            | _ -> kopt in
        let tc = TyconAbstract(id, bs, kopt) in
        let _, _, se, _ = desugar_abstract_tc quals env [] tc in
        let se = match se.sigel with
           | Sig_inductive_typ(l, _, typars, k, [], []) ->
             let quals = se.sigquals in
             let quals = if List.contains S.Assumption quals
                         then quals
                         else (if not (Options.ml_ish ()) then
                                 FStar.Errors.log_issue se.sigrng
                                   (Errors.Warning_AddImplicitAssumeNewQualifier, (BU.format1 "Adding an implicit 'assume new' qualifier on %s"
                                               (Print.lid_to_string l)));
                                 S.Assumption :: S.New :: quals) in
             let t = match typars with
                | [] -> k
                | _ -> mk (Tm_arrow(typars, mk_Total k)) None se.sigrng in
             { se with sigel = Sig_declare_typ(l, [], t);
                       sigquals = quals }
           | _ -> failwith "Impossible" in
        let env = push_sigelt env se in
        let env = Env.push_doc env (qualify env id) d.doc in
        (* let _ = pr "Pushed %s\n" (text_of_lid (qualify env (tycon_id tc))) in *)
        env, [se]

    | [TyconAbbrev(id, binders, kopt, t)] ->
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
                 let c = desugar_comp t.range env' t in
                 let typars = Subst.close_binders typars in
                 let c = Subst.close_comp typars c in
                 let quals = quals |> List.filter (function S.Effect -> false | _ -> true) in
                 { sigel = Sig_effect_abbrev(qlid, [], typars, c, cattributes @ comp_flags c);
                   sigquals = quals;
                   sigrng = rng;
                   sigmeta = default_sigmeta  ;
                   sigattrs = [] }
            else let t = desugar_typ env' t in
                 mk_typ_abbrev qlid [] typars kopt t [qlid] quals rng in

        let env = push_sigelt env se in
        let env = push_doc env qlid d.doc in
        env, [se]

    | [TyconRecord _] ->
      let trec = List.hd tcs in
      let t, fs = tycon_record_as_variant trec in
      desugar_tycon env d (RecordType (ids_of_lid (current_module env), fs)::quals) [t]

    |  _::_ ->
      let env0 = env in
      let mutuals = List.map (fun x -> qualify env <| tycon_id x) tcs in
      let rec collect_tcs quals et tc =
        let (env, tcs) = et in
        match tc with
          | TyconRecord _ ->
            let trec = tc in
            let t, fs = tycon_record_as_variant trec in
            collect_tcs (RecordType (ids_of_lid (current_module env), fs)::quals) (env, tcs) t
          | TyconVariant(id, binders, kopt, constructors) ->
            let env, _, se, tconstr = desugar_abstract_tc quals env mutuals (TyconAbstract(id, binders, kopt)) in
            env, Inl(se, constructors, tconstr, quals)::tcs
          | TyconAbbrev(id, binders, kopt, t) ->
            let env, _, se, tconstr = desugar_abstract_tc quals env mutuals (TyconAbstract(id, binders, kopt)) in
            env, Inr(se, binders, t, quals)::tcs
          | _ -> failwith "Unrecognized mutual type definition" in
      let env, tcs = List.fold_left (collect_tcs quals) (env, []) tcs in
      let tcs = List.rev tcs in
      let docs_tps_sigelts = tcs |> List.collect (function
        | Inr ({ sigel = Sig_inductive_typ(id, uvs, tpars, k, _, _) }, binders, t, quals) -> //type abbrevs in mutual type definitions
              let t =
                  let env, tpars = typars_of_binders env binders in
                  let env_tps, tpars = push_tparams env tpars in
                  let t = desugar_typ env_tps t in
                  let tpars = Subst.close_binders tpars in
                  Subst.close tpars t
          in
          [((id, d.doc), [], mk_typ_abbrev id uvs tpars (Some k) t [id] quals rng)]

        | Inl ({ sigel = Sig_inductive_typ(tname, univs, tpars, k, mutuals, _); sigquals = tname_quals }, constrs, tconstr, quals) ->
          let mk_tot t =
            let tot = mk_term (Name C.effect_Tot_lid) t.range t.level in
            mk_term (App(tot, t, Nothing)) t.range t.level in
          let tycon = (tname, tpars, k) in
          let env_tps, tps = push_tparams env tpars in
          let data_tpars = List.map (fun (x, _) -> (x, Some (S.Implicit true))) tps in
          let tot_tconstr = mk_tot tconstr in
          let constrNames, constrs = List.split <|
              (constrs |> List.map (fun (id, topt, doc, of_notation) ->
                let t =
                  if of_notation
                  then match topt with
                    | Some t -> mk_term (Product([mk_binder (NoName t) t.range t.level None], tot_tconstr)) t.range t.level
                    | None -> tconstr
                  else match topt with
                    | None -> failwith "Impossible"
                    | Some t -> t in
                let t = desugar_term env_tps (close env_tps t) in
                let name = qualify env id in
                let quals = tname_quals |> List.collect (function
                    | RecordType fns -> [RecordConstructor fns]
                    | _ -> []) in
                let ntps = List.length data_tpars in
                (name, ((name, doc), tps, { sigel = Sig_datacon(name, univs, U.arrow data_tpars (mk_Total (t |> U.name_function_binders)),
                                                                tname, ntps, mutuals);
                                            sigquals = quals;
                                            sigrng = rng;
                                            sigmeta = default_sigmeta  ;
                                            sigattrs = [] }))))
          in
          ((tname, d.doc), [], { sigel = Sig_inductive_typ(tname, univs, tpars, k, mutuals, constrNames);
                                 sigquals = tname_quals;
                                 sigrng = rng;
                                 sigmeta = default_sigmeta  ;
                                 sigattrs = [] })::constrs
        | _ -> failwith "impossible")
      in
      let name_docs = docs_tps_sigelts |> List.map (fun (name_doc, _, _) -> name_doc) in
      let sigelts = docs_tps_sigelts |> List.map (fun (_, _, se) -> se) in
      let bundle, abbrevs = FStar.Syntax.MutRecTy.disentangle_abbrevs_from_bundle sigelts quals (List.collect U.lids_of_sigelt sigelts) rng in
      let env = push_sigelt env0 bundle in
      let env = List.fold_left push_sigelt env abbrevs in
      (* NOTE: derived operators such as projectors and discriminators are using the type names before unfolding. *)
      let data_ops = docs_tps_sigelts |> List.collect (fun (_, tps, se) -> mk_data_projector_names quals env se) in
      let discs = sigelts |> List.collect (fun se -> match se.sigel with
        | Sig_inductive_typ(tname, _, tps, k, _, constrs) when (List.length constrs > 1)->
          let quals = se.sigquals in
          let quals = if List.contains S.Abstract quals && not (List.contains S.Private quals)
                      then S.Private::quals
                      else quals in
          mk_data_discriminators quals env constrs
        | _ -> []) in
      let ops = discs@data_ops in
      let env = List.fold_left push_sigelt env ops in
      let env = List.fold_left (fun acc (lid, doc) -> push_doc env lid doc) env name_docs in
      env, [bundle]@abbrevs@ops

    | [] -> failwith "impossible"

let desugar_binders env binders =
    let env, binders = List.fold_left (fun (env,binders) b ->
    match desugar_binder env b with
      | (Some a, k) ->
        let binder, env = as_binder env b.aqual (Some a, k) in
        env, binder::binders

      | _ -> raise_error (Errors.Fatal_MissingNameInBinder, "Missing name in binder") b.brange) (env, []) binders in
    env, List.rev binders

let push_reflect_effect env quals (effect_name:Ident.lid) range =
    if quals |> BU.for_some (function S.Reflectable _ -> true | _ -> false)
    then let monad_env = Env.enter_monad_scope env effect_name.ident in
         let reflect_lid = Ident.id_of_text "reflect" |> Env.qualify monad_env in
         let quals = [S.Assumption; S.Reflectable effect_name] in
         let refl_decl = { sigel = S.Sig_declare_typ(reflect_lid, [], S.tun);
                           sigrng = range;
                           sigquals = quals;
                           sigmeta = default_sigmeta  ;
                           sigattrs = [] } in
         Env.push_sigelt env refl_decl // FIXME: Add docs to refl_decl?
    else env

// If this is a fail attribute, return the listed errors and whether it's a fail_lax or not
let get_fail_attr warn (at : S.term) : option<(list<int> * bool)> =
    let hd, args = U.head_and_args at in
    match (SS.compress hd).n, args with
    | Tm_fvar fv, [(a1, _)] when S.fv_eq_lid fv C.fail_attr
                              || S.fv_eq_lid fv C.fail_lax_attr ->
        begin match EMB.unembed (EMB.e_list EMB.e_int) a1 true EMB.id_norm_cb with
        | Some es when List.length es > 0->
            (* Is this an expect_lax_failure? *)
            let b = S.fv_eq_lid fv C.fail_lax_attr in
            Some (List.map FStar.BigInt.to_int_fs es, b)

        | _ ->
            if warn then
                Errors.log_issue at.pos (Errors.Warning_UnappliedFail, "Found ill-applied 'expect_failure', argument should be a non-empty list of integer literals");
            None
        end

    | Tm_fvar fv, [] when S.fv_eq_lid fv C.fail_attr
                       || S.fv_eq_lid fv C.fail_lax_attr ->
        (* Is this an expect_lax_failure? *)
        let b = S.fv_eq_lid fv C.fail_lax_attr in
        Some ([], b)

    | Tm_fvar fv, _ when S.fv_eq_lid fv C.fail_attr
                      || S.fv_eq_lid fv C.fail_lax_attr ->
        if warn then
            Errors.log_issue at.pos (Errors.Warning_UnappliedFail, "Found ill-applied 'expect_failure', argument should be a non-empty list of integer literals");
        None

    | _ ->
        None

let rec desugar_effect env d (quals: qualifiers) eff_name eff_binders eff_typ eff_decls attrs =
    let env0 = env in
    // qualified with effect name
    let monad_env = Env.enter_monad_scope env eff_name in
    let env, binders = desugar_binders monad_env eff_binders in
    let eff_t = desugar_term env eff_typ in

    (* An effect for free has a type of the shape "a:Type -> Effect" *)
    let for_free = List.length (fst (U.arrow_formals eff_t)) = 1 in

    let mandatory_members =
      let rr_members = ["repr" ; "return" ; "bind"] in
      if for_free then rr_members
      else
        (* the first 3 are optional but must not be counted as actions *)
        rr_members @ [
          "return_wp";
          "bind_wp";
          "if_then_else";
          "ite_wp";
          "stronger";
          "close_wp";
          "assert_p";
          "assume_p";
          "null_wp";
          "trivial"
        ]
    in

    let name_of_eff_decl decl =
      match decl.d with
      | Tycon(_, _, [TyconAbbrev(name, _, _, _), _]) -> Ident.text_of_id name
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
    let actions_docs = actions |> List.map (fun d ->
        match d.d with
        | Tycon(_, _,[TyconAbbrev(name, action_params, _, { tm = Construct (_, [ def, _; cps_type, _ ])}), doc]) when not for_free ->
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
            }, doc
        | Tycon(_, _, [TyconAbbrev(name, action_params, _, defn), doc]) when for_free ->
            // When for free, the user just provides the definition and the rest
            // is elaborated
            let env, action_params = desugar_binders env action_params in
            let action_params = Subst.close_binders action_params in
            {
              action_name=Env.qualify env name;
              action_unqualified_name = name;
              action_univs=[];
              action_params = action_params;
              action_defn=Subst.close (binders@action_params) (desugar_term env defn);
              action_typ=S.tun
            }, doc
        | _ ->
            raise_error (Errors.Fatal_MalformedActionDeclaration, ("Malformed action declaration; if this is an \"effect \
              for free\", just provide the direct-style declaration. If this is \
              not an \"effect for free\", please provide a pair of the definition \
              and its cps-type with arrows inserted in the right place (see \
              examples).")) d.drange
    ) in
    let actions = List.map fst actions_docs in
    let eff_t = Subst.close binders eff_t in
    let lookup s =
        let l = Env.qualify env (mk_ident(s, d.drange)) in
        [], Subst.close binders <| fail_or env (try_lookup_definition env) l in
    let mname       =qualify env0 eff_name in
    let qualifiers  =List.map (trans_qual d.drange (Some mname)) quals in
    let se =
      if for_free then
        let dummy_tscheme = [], mk Tm_unknown None Range.dummyRange in
        { sigel =
          (Sig_new_effect_for_free ({
             mname       = mname;
             cattributes  = [];
             univs       = [];
             binders     = binders;
             signature   = eff_t;
             ret_wp      = dummy_tscheme;
             bind_wp     = dummy_tscheme;
             if_then_else= dummy_tscheme;
             ite_wp      = dummy_tscheme;
             stronger    = dummy_tscheme;
             close_wp    = dummy_tscheme;
             assert_p    = dummy_tscheme;
             assume_p    = dummy_tscheme;
             null_wp     = dummy_tscheme;
             trivial     = dummy_tscheme;
             repr        = snd (lookup "repr");
             bind_repr   = lookup "bind";
             return_repr = lookup "return";
             actions     = actions;
             eff_attrs   = List.map (desugar_term env) attrs;
           }));
           sigquals = qualifiers;
           sigrng = d.drange;
           sigmeta = default_sigmeta  ;
           sigattrs = [] }
      else
        let rr = BU.for_some (function S.Reifiable | S.Reflectable _ -> true | _ -> false) qualifiers in
        let un_ts = [], Syntax.tun in
        { sigel =
          (Sig_new_effect({
             mname       = mname;
             cattributes  = [];
             univs       = [];
             binders     = binders;
             signature   = eff_t;
             ret_wp      = lookup "return_wp";
             bind_wp     = lookup "bind_wp";
             if_then_else= lookup "if_then_else";
             ite_wp      = lookup "ite_wp";
             stronger    = lookup "stronger";
             close_wp    = lookup "close_wp";
             assert_p    = lookup "assert_p";
             assume_p    = lookup "assume_p";
             null_wp     = lookup "null_wp";
             trivial     = lookup "trivial";
             repr        = (if rr then snd <| lookup "repr" else S.tun);
             bind_repr   = (if rr then lookup "bind" else un_ts);
             return_repr = (if rr then lookup "return" else un_ts);
             actions     = actions;
             eff_attrs   = List.map (desugar_term env) attrs;
           }));
           sigquals = qualifiers;
           sigrng = d.drange;
           sigmeta = default_sigmeta  ;
           sigattrs = [] }
    in
    let env = push_sigelt env0 se in
    let env = push_doc env mname d.doc in
    let env = actions_docs |> List.fold_left (fun env (a, doc) ->
        //printfn "Pushing action %s\n" a.action_name.str;
        let env = push_sigelt env (U.action_as_lb mname a a.action_defn.pos) in
        push_doc env a.action_name doc) env
    in
    let env = push_reflect_effect env qualifiers mname d.drange in
    let env = push_doc env mname d.doc in
    env, [se]

and desugar_redefine_effect env d trans_qual quals eff_name eff_binders defn =
    let env0 = env in
    let env = Env.enter_monad_scope env eff_name in
    let env, binders = desugar_binders env eff_binders in
    let ed_lid, ed, args, cattributes =
        let head, args = head_and_args defn in
        let lid = match head.tm with
          | Name l -> l
          | _ -> raise_error (Errors.Fatal_EffectNotFound, "Effect " ^AST.term_to_string head^ " not found") d.drange
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
    then raise_error (Errors.Fatal_ArgumentLengthMismatch, "Unexpected number of arguments to effect constructor") defn.range;
    let ed_binders, _, ed_binders_opening = Subst.open_term' ed.binders S.t_unit in
    let sub (us, x) =
        let x = Subst.subst (Subst.shift_subst (List.length us) ed_binders_opening) x in
        let s = U.subst_of_list ed_binders args in
        Subst.close_tscheme binders (us, (Subst.subst s x))
    in
    let mname=qualify env0 eff_name in
    let ed = {
            mname       =mname;
            cattributes =cattributes;
            univs       =ed.univs;
            binders     =binders;
            signature   =snd (sub ([], ed.signature));
            ret_wp      =sub ed.ret_wp;
            bind_wp     =sub ed.bind_wp;
            if_then_else=sub ed.if_then_else;
            ite_wp      =sub ed.ite_wp;
            stronger    =sub ed.stronger;
            close_wp    =sub ed.close_wp;
            assert_p    =sub ed.assert_p;
            assume_p    =sub ed.assume_p;
            null_wp     =sub ed.null_wp;
            trivial     =sub ed.trivial;

            repr        =snd (sub ([], ed.repr));
            bind_repr   =sub ed.bind_repr;
            return_repr =sub ed.return_repr;
            actions     = List.map (fun action ->
                {
                    // Since we called enter_monad_env before, this is going to generate
                    // a name of the form FStar.ST.uu___proj__STATE__item__get
                    action_name = Env.qualify env (action.action_unqualified_name);
                    action_unqualified_name = action.action_unqualified_name;
                    action_univs = action.action_univs ;
                    action_params = action.action_params ;
                    action_defn =snd (sub ([], action.action_defn)) ;
                    action_typ =snd (sub ([], action.action_typ))
                })
                ed.actions;
            eff_attrs   = ed.eff_attrs;
    } in
    let se =
      (* An effect for free has a type of the shape "a:Type -> Effect" *)
      let for_free = List.length (fst (U.arrow_formals ed.signature)) = 1 in
      { sigel = if for_free then Sig_new_effect_for_free (ed) else Sig_new_effect (ed);
        sigquals = List.map (trans_qual (Some mname)) quals;
        sigrng = d.drange;
        sigmeta = default_sigmeta  ;
        sigattrs = [] }
    in
    let monad_env = env in
    let env = push_sigelt env0 se in
    let env = push_doc env ed_lid d.doc in // FIXME: Docs of actions?
    let env = ed.actions |> List.fold_left (fun env a ->
        let doc = Env.try_lookup_doc env a.action_name in
        let env = push_sigelt env (U.action_as_lb mname a a.action_defn.pos) in
        push_doc env a.action_name doc
    ) env in
    let env =
        if quals |> List.contains Reflectable
        then let reflect_lid = Ident.id_of_text "reflect" |> Env.qualify monad_env in
             let quals = [S.Assumption; S.Reflectable mname] in
             let refl_decl = { sigel = S.Sig_declare_typ(reflect_lid, [], S.tun);
                               sigquals = quals;
                               sigrng = d.drange;
                               sigmeta = default_sigmeta  ;
                               sigattrs = [] } in
             push_sigelt env refl_decl // FIXME: Add docs to refl_decl?
        else env in
    let env = push_doc env mname d.doc in
    env, [se]

// JP: crappy formatting, use PPrint
and mk_comment_attr (d: decl) =
  let text, kv = match d.doc with | None -> "", [] | Some fsdoc -> fsdoc in
  let summary = match List.assoc "summary" kv with | None -> "" | Some s -> "  " ^ s ^ "\n" in
  let pp =
    match List.assoc "type" kv with
    | Some _ ->
        "\n  " ^ FStar.Pprint.pretty_string 0.95 80 (FStar.Parser.ToDocument.signature_to_document d)
    | _ ->
        ""
  in
  let other = List.filter_map (fun (k, v) ->
    if k <> "summary" && k <> "type" then
      Some (k ^ ": " ^ v)
    else
      None
  ) kv
  in
  let other = if other <> [] then String.concat "\n" other ^ "\n" else "" in
  let str = summary ^ pp ^ other ^ text in
  (* Building a fake term *)
  let fv = S.fvar (lid_of_str "FStar.Pervasives.Comment") delta_constant None in
  let arg = U.exp_string str in
  U.mk_app fv [ S.as_arg arg ]

and desugar_decl_aux env (d: decl): (env_t * sigelts) =
  // Rather than carrying the attributes down the maze of recursive calls, we
  // let each desugar_foo function provide an empty list, then override it here.
  // Not for the `fail` attribute though! We only keep that one on the first
  // new decl.
  let env, sigelts = desugar_decl_noattrs env d in
  let attrs = d.attrs in
  let attrs = List.map (desugar_term env) attrs in
  let attrs = mk_comment_attr d :: attrs in
  env, List.mapi (fun i sigelt -> if i = 0
                                  then { sigelt with sigattrs = attrs }
                                  else { sigelt with sigattrs = List.filter (fun at -> Option.isNone (get_fail_attr false at)) attrs })
                 sigelts

and desugar_decl env (d:decl) :(env_t * sigelts) =
  let env, ses = desugar_decl_aux env d in
  env, ses |> List.map generalize_annotated_univs

and desugar_decl_noattrs env (d:decl) : (env_t * sigelts) =
  let trans_qual = trans_qual d.drange in
  match d.d with
  | Pragma p ->
    let p = trans_pragma p in
    U.process_pragma p d.drange;
    let se = { sigel = Sig_pragma p;
               sigquals = [];
               sigrng = d.drange;
               sigmeta = default_sigmeta  ;
               sigattrs = [] } in
    env, [se]

  | Fsdoc _ -> env, []

  | TopLevelModule id -> env, []

  | Open lid ->
    let env = Env.push_namespace env lid in
    env, []

  | Include lid ->
    let env = Env.push_include env lid in
    env, []

  | ModuleAbbrev(x, l) ->
    Env.push_module_abbrev env x l, []

  | Tycon(is_effect, typeclass, tcs) ->
    let quals = d.quals in
    let quals = if is_effect then Effect_qual :: quals else quals in
    let quals = if typeclass then Noeq        :: quals else quals in
    let tcs = List.map (fun (x,_) -> x) tcs in
    let env, ses = desugar_tycon env d (List.map (trans_qual None) quals) tcs in

    (* Handling typeclasses: we typecheck the tcs as usual, and then need to add
     * %splice[new_meth_lids] (mk_class type_lid)
     * where the tricky bit is getting the new_meth_lids. To do so,
     * we traverse the new declarations marked with "Projector", and get
     * the field names. This is pretty ugly. *)
    let mkclass lid =
        U.abs [S.mk_binder (S.new_bv None S.tun)]
              (U.mk_app (S.tabbrev C.mk_class_lid)
                        [S.as_arg (U.exp_string (string_of_lid lid))])
              None
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
            let id = U.unmangle_field_name id in
            [qualify env id]
    in
    let rec splice_decl meths se =
        match se.sigel with
        | Sig_bundle (ses, _) -> List.concatMap (splice_decl meths) ses
        | Sig_inductive_typ (lid, _, _, _, _, _) ->
           [{ sigel = Sig_splice(meths , mkclass lid);
              sigquals = [];
              sigrng = d.drange;
              sigmeta = default_sigmeta;
              sigattrs = [] }]
        | _ -> []
    in
    let extra =
        if typeclass
        then let meths = List.concatMap get_meths ses in
             List.concatMap (splice_decl meths) ses
        else []
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
        | [ { pat = PatAscribed ({ pat = PatVar _}, _) }, _ ] -> false
        | [ p, _ ] -> not (is_app_pattern p)
        | _ -> false
      end
    in
    if not expand_toplevel_pattern
    then begin
      let lets = List.map (fun x -> None, x) lets in
      let as_inner_let =
        mk_term (Let(isrec, lets, mk_term (Const Const_unit) d.drange Expr)) d.drange Expr
      in
      let ds_lets, aq = desugar_term_maybe_top true env as_inner_let in
      check_no_aq aq;
      match (Subst.compress <| ds_lets).n with
        | Tm_let(lbs, _) ->
          let fvs = snd lbs |> List.map (fun lb -> right lb.lbname) in
          let quals = match quals with
            | _::_ -> List.map (trans_qual None) quals
            | _ -> snd lbs |> List.collect
            (function | {lbname=Inl _} -> []
                      | {lbname=Inr fv} -> Env.lookup_letbinding_quals env fv.fv_name.v) in
          let quals =
            if lets |> BU.for_some (fun (_, (_, t)) -> t.level=Formula)
            then S.Logic::quals
            else quals in
          let lbs = if quals |> List.contains S.Abstract
                    then fst lbs, snd lbs |> List.map (fun lb ->
                            let fv = right lb.lbname in
                            {lb with lbname=Inr ({fv with fv_delta=Delta_abstract fv.fv_delta})})
                    else lbs in
          let names = fvs |> List.map (fun fv -> fv.fv_name.v) in
          (*
           * AR: we first deguar the term with no attributes and then add attributes in the end, see desugar_decl above
           *     this used to be fine, because subsequent typechecker then works on terms that have attributes
           *     however this doesn't work if we want access to the attributes during desugaring, e.g. when warning about deprecated defns.
           *     for now, adding attrs to Sig_let to make progress on the deprecated warning, but perhaps we should add attrs to all terms
           *)
          let attrs = List.map (desugar_term env) d.attrs in
          let s = { sigel = Sig_let(lbs, names);
                    sigquals = quals;
                    sigrng = d.drange;
                    sigmeta = default_sigmeta  ;
                    sigattrs = attrs } in
          let env = push_sigelt env s in
          // FIXME all bindings in let get the same docs?
          let env = List.fold_left (fun env id -> push_doc env id d.doc) env names in
          env, [s]
        | _ -> failwith "Desugaring a let did not produce a let"
    end
    else
      (* If there is a top-level pattern we first bind the result of the body *)
      (* to some private anonymous name then we gather each idents bounded in *)
      (* the pattern and introduce one toplevel binding for each of them      *)
      let (pat, body) = match lets with
        | [pat, body] -> pat, body
        | _ -> failwith "expand_toplevel_pattern should only allow single definition lets"
      in
      let fresh_toplevel_name = Ident.gen Range.dummyRange in
      let fresh_pat =
        let var_pat = mk_pattern (PatVar (fresh_toplevel_name, None)) Range.dummyRange in
        (* TODO : What about inner type ascriptions ? Is there any way to retrieve those ? *)
        match pat.pat with
          | PatAscribed (pat, ty) -> { pat with pat = PatAscribed (var_pat, ty) }
          | _ -> var_pat
      in
      (* TODO : We should ensure that the result of body always matches pat (add a type annotation ?) *)
      let main_let =
        desugar_decl env ({ d with
          d = TopLevelLet (isrec, [fresh_pat, body]) ;
          quals = Private :: d.quals })
      in

      let build_projection (env, ses) id =
        (* We build a new toplevel definition as follow and then desugar it *)
        (* let id = match fresh_toplevel_name with | pat -> id              *)
        let main = mk_term (Var (lid_of_ids [fresh_toplevel_name])) Range.dummyRange Expr in
        let lid = lid_of_ids [id] in
        let projectee = mk_term (Var lid) Range.dummyRange Expr in
        let body = mk_term (Match (main, [pat, None, projectee])) Range.dummyRange Expr in
        let bv_pat = mk_pattern (PatVar (id, None)) Range.dummyRange in
        (* TODO : do we need to put some attributes for this declaration ? *)
        let id_decl = mk_decl (TopLevelLet(NoLetQualifier, [bv_pat, body])) Range.dummyRange [] in
        let env, ses' = desugar_decl env id_decl in
        env, ses @ ses'
      in
      let bvs = gather_pattern_bound_vars pat |> set_elements in
      List.fold_left build_projection main_let bvs

  | Main t ->
    let e = desugar_term env t in
    let se = { sigel = Sig_main(e);
               sigquals = [];
               sigrng = d.drange;
               sigmeta = default_sigmeta  ;
               sigattrs = [] } in
    env, [se]

  | Assume(id, t) ->
    let f = desugar_formula env t in
    let lid = qualify env id in
    let env = push_doc env lid d.doc in
    env, [{ sigel = Sig_assume(lid, [], f);
            sigquals = [S.Assumption];
            sigrng = d.drange;
            sigmeta = default_sigmeta  ;
            sigattrs = [] }]

  | Val(id, t) ->
    let quals = d.quals in
    let t = desugar_term env (close_fun env t) in
    let quals =
        if Env.iface env
        && Env.admitted_iface env
        then Assumption::quals
        else quals in
    let lid = qualify env id in
    let se = { sigel = Sig_declare_typ(lid, [], t);
               sigquals = List.map (trans_qual None) quals;
               sigrng = d.drange;
               sigmeta = default_sigmeta  ;
               sigattrs = [] } in
    let env = push_sigelt env se in
    let env = push_doc env lid d.doc in
    env, [se]

  | Exception(id, None) ->
    let t, _ = fail_or env (try_lookup_lid env) C.exn_lid in
    let l = qualify env id in
    let qual = [ExceptionConstructor] in
    let se = { sigel = Sig_datacon(l, [], t, C.exn_lid, 0, [C.exn_lid]);
               sigquals = qual;
               sigrng = d.drange;
               sigmeta = default_sigmeta  ;
               sigattrs = [] } in
    let se' = { sigel = Sig_bundle([se], [l]);
                sigquals = qual;
                sigrng = d.drange;
                sigmeta = default_sigmeta  ;
                sigattrs = [] } in
    let env = push_sigelt env se' in
    let env = push_doc env l d.doc in
    let data_ops = mk_data_projector_names [] env se in
    let discs = mk_data_discriminators [] env [l] in
    let env = List.fold_left push_sigelt env (discs@data_ops) in
    env, se'::discs@data_ops

  | Exception(id, Some term) ->
    let t = desugar_term env term in
    let t = U.arrow ([null_binder t]) (mk_Total <| fst (fail_or env (try_lookup_lid env) C.exn_lid)) in
    let l = qualify env id in
    let qual = [ExceptionConstructor] in
    let se = { sigel = Sig_datacon(l, [], t, C.exn_lid, 0, [C.exn_lid]);
               sigquals = qual;
               sigrng = d.drange;
               sigmeta = default_sigmeta  ;
               sigattrs = [] } in
    let se' = { sigel = Sig_bundle([se], [l]);
                sigquals = qual;
                sigrng = d.drange;
                sigmeta = default_sigmeta  ;
                sigattrs = [] } in
    let env = push_sigelt env se' in
    let env = push_doc env l d.doc in
    let data_ops = mk_data_projector_names [] env se in
    let discs = mk_data_discriminators [] env [l] in
    let env = List.fold_left push_sigelt env (discs@data_ops) in
    env, se'::discs@data_ops

  | NewEffect (RedefineEffect(eff_name, eff_binders, defn)) ->
    let quals = d.quals in
    desugar_redefine_effect env d trans_qual quals eff_name eff_binders defn

  | NewEffect (DefineEffect(eff_name, eff_binders, eff_typ, eff_decls)) ->
    let quals = d.quals in
    let attrs = d.attrs in
    desugar_effect env d quals eff_name eff_binders eff_typ eff_decls attrs

  | SubEffect l ->
    let lookup l = match Env.try_lookup_effect_name env l with
        | None -> raise_error (Errors.Fatal_EffectNotFound, ("Effect name " ^Print.lid_to_string l^ " not found")) d.drange
        | Some l -> l in
    let src = lookup l.msource in
    let dst = lookup l.mdest in
    let lift_wp, lift = match l.lift_op with
        | NonReifiableLift t -> Some ([],desugar_term env t), None
        | ReifiableLift (wp, t) -> Some ([],desugar_term env wp), Some([], desugar_term env t)
        | LiftForFree t -> None, Some ([],desugar_term env t)
    in
    let se = { sigel = Sig_sub_effect({source=src; target=dst; lift_wp=lift_wp; lift=lift});
               sigquals = [];
               sigrng = d.drange;
               sigmeta = default_sigmeta  ;
               sigattrs = [] } in
    env, [se]

  | Splice (ids, t) ->
    let t = desugar_term env t in
    let se = { sigel = Sig_splice(List.map (qualify env) ids, t);
               sigquals = [];
               sigrng = d.drange;
               sigmeta = default_sigmeta;
               sigattrs = [] } in
    let env = push_sigelt env se in
    env, [se]

let desugar_decls env decls =
  let env, sigelts =
    List.fold_left (fun (env, sigelts) d ->
      let env, se = desugar_decl env d in
      env, sigelts@se) (env, []) decls
  in
  (* Propagate the doc from a val to a let. *)
  let rec forward acc = function
    | se1 :: se2 :: sigelts ->
        begin match se1.sigel, se2.sigel with
        | Sig_declare_typ _, Sig_let _ ->
            forward ({ se2 with sigattrs =
              List.filter (function
                | { n = Tm_app ({ n = Tm_fvar fv }, _) }
                  when string_of_lid (lid_of_fv fv) = "FStar.Pervasives.Comment" ->
                    true
                | _ -> false
              ) se1.sigattrs @ se2.sigattrs
            } :: se1 :: acc) sigelts
        | _ ->
            forward (se1 :: acc) (se2 :: sigelts)
        end
    | sigelts ->
        List.rev_append acc sigelts
  in
  env, forward [] sigelts


let open_prims_all =
    [AST.mk_decl (AST.Open C.prims_lid) Range.dummyRange;
     AST.mk_decl (AST.Open C.all_lid) Range.dummyRange]

(* Top-level functionality: from AST to a module
   Keeps track of the name of variables and so on (in the context)
 *)
let desugar_modul_common (curmod: option<S.modul>) env (m:AST.modul) : env_t * Syntax.modul * bool =
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
    exports=[];
    is_interface=intf
  } in
  env, modul, pop_when_done

let as_interface (m:AST.modul) : AST.modul =
    match m with
    | AST.Module(mname, decls) -> AST.Interface(mname, decls, true)
    | i -> i

let desugar_partial_modul curmod (env:env_t) (m:AST.modul) : env_t * Syntax.modul =
  let m =
    if Options.interactive () &&
      List.mem (get_file_extension (List.hd (Options.file_list ()))) ["fsti"; "fsi"]
    then as_interface m
    else m
  in
  let env, modul, pop_when_done = desugar_modul_common curmod env m in
  if pop_when_done then Env.pop (), modul
  else env, modul

let desugar_modul env (m:AST.modul) : env_t * Syntax.modul =
  let env, modul, pop_when_done = desugar_modul_common None env m in
  let env, modul = Env.finish_module_or_interface env modul in
  if Options.dump_module modul.name.str
  then BU.print1 "Module after desugaring:\n%s\n" (Print.modul_to_string modul);
  (if pop_when_done then export_interface modul.name env else env), modul


/////////////////////////////////////////////////////////////////////////////////////////
//External API for modules
/////////////////////////////////////////////////////////////////////////////////////////
let with_options (f:unit -> 'a) : 'a =
    FStar.Options.push();
    let res = f () in
    let light = FStar.Options.ml_ish() in
    FStar.Options.pop();
    if light then FStar.Options.set_ml_ish();
    res

let ast_modul_to_modul modul : withenv<S.modul> =
    fun env ->
        with_options (fun () ->
        let e, m = desugar_modul env modul in
        m, e)

let decls_to_sigelts decls : withenv<S.sigelts> =
    fun env ->
        with_options (fun () ->
        let env, sigelts = desugar_decls env decls in
        sigelts, env)

let partial_ast_modul_to_modul modul a_modul : withenv<S.modul> =
    fun env ->
        with_options (fun () ->
        let env, modul = desugar_partial_modul modul env a_modul in
        modul, env)

let add_modul_to_env (m:Syntax.modul)
                     (mii:module_inclusion_info)
                     (erase_univs:S.term -> S.term) : withenv<unit> =
  fun en ->
      let erase_univs_ed ed =
          let erase_binders bs =
              match bs with
              | [] -> []
              | _ ->
                let t = erase_univs (S.mk (Tm_abs(bs, S.t_unit, None)) None Range.dummyRange) in
                match (Subst.compress t).n with
                | Tm_abs(bs, _, _) -> bs
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
                    let t = S.mk (Tm_abs(bs, S.t_unit, None)) None Range.dummyRange in
                    match (Subst.compress (Subst.close binders t)).n with
                    | Tm_abs(bs, _, _) -> bs
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
               univs = [];
               binders   = Subst.close_binders binders;
               signature = erase_term ed.signature;
               ret_wp    = erase_tscheme ed.ret_wp;
               bind_wp   = erase_tscheme ed.bind_wp;
               if_then_else= erase_tscheme ed.if_then_else;
               ite_wp      = erase_tscheme ed.ite_wp;
               stronger    = erase_tscheme ed.stronger;
               close_wp    = erase_tscheme ed.close_wp;
               assert_p    = erase_tscheme ed.assert_p;
               assume_p    = erase_tscheme ed.assume_p;
               null_wp     = erase_tscheme ed.null_wp;
               trivial     = erase_tscheme ed.trivial;
               repr        = erase_term ed.repr;
               return_repr = erase_tscheme ed.return_repr;
               bind_repr   = erase_tscheme ed.bind_repr;
               actions     = List.map erase_action ed.actions
          }
      in
      let push_sigelt env se =
          match se.sigel with
          | Sig_new_effect ed ->
            let se' = {se with sigel=Sig_new_effect (erase_univs_ed ed)} in
            let env = Env.push_sigelt env se' in
            push_reflect_effect env se.sigquals ed.mname se.sigrng
          | Sig_new_effect_for_free ed ->
            let se' = {se with sigel=Sig_new_effect_for_free (erase_univs_ed ed)} in
            let env = Env.push_sigelt env se' in
            push_reflect_effect env se.sigquals ed.mname se.sigrng
          | _ -> Env.push_sigelt env se
      in
      let en, pop_when_done = Env.prepare_module_or_interface false false en m.name mii in
      let en = List.fold_left
                    push_sigelt
                    (Env.set_current_module en m.name)
                    m.exports in
      let env = Env.finish en m in
      (), (if pop_when_done then export_interface m.name env else env)
