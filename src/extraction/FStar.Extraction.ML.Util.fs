(*
   Copyright 2008-2015 Abhishek Anand, Nikhil Swamy and Microsoft Research

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
module FStar.Extraction.ML.Util
open FStar.ST
open FStar.All
open FStar
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Extraction.ML
open FStar.Extraction.ML.Syntax
open FStar.Const
open FStar.Ident
open FStar.Errors
module BU = FStar.Util
module U = FStar.Syntax.Util
module UEnv = FStar.Extraction.ML.UEnv
module PC = FStar.Parser.Const
module Range = FStar.Range
module S = FStar.Syntax.Syntax

let codegen_fsharp () = Options.codegen () = Some Options.FSharp

let pruneNones (l : list<option<'a>>) : list<'a> =
    List.fold_right (fun  x ll -> match x with
                          | Some xs -> xs::ll
                          | None -> ll) l []


let mk_range_mle = with_ty MLTY_Top <| MLE_Name (["Prims"], "mk_range")

(* private *)
let mlconst_of_const' (sctt : sconst) =
  match sctt with
  | Const_effect       -> failwith "Unsupported constant"

  | Const_range _
  | Const_unit         -> MLC_Unit
  | Const_char   c     -> MLC_Char  c
  | Const_int    (s, i)-> MLC_Int   (s, i)
  | Const_bool   b     -> MLC_Bool  b
  | Const_float  d     -> MLC_Float d

  | Const_bytearray (bytes, _) ->
      MLC_Bytes bytes

  | Const_string (s, _) -> MLC_String (s)

  | Const_range_of
  | Const_set_range_of ->
    failwith "Unhandled constant: range_of/set_range_of"

  | Const_reify
  | Const_reflect _ ->
    failwith "Unhandled constant: reify/reflect"

let mlconst_of_const (p:Range.range) (c:sconst) =
    try mlconst_of_const' c
    with _ -> failwith (BU.format2 "(%s) Failed to translate constant %s " (Range.string_of_range p) (Print.const_to_string c))

let mlexpr_of_range (r:Range.range) : mlexpr' =
    let cint (i : int) : mlexpr =
        MLC_Int (string_of_int i, None) |> MLE_Const |> with_ty ml_int_ty
    in
    let cstr (s : string) : mlexpr =
        MLC_String s |> MLE_Const |> with_ty ml_string_ty
    in
    // This is not being fully faithful since it disregards
    // the use_range, but I assume that's not too bad.
    MLE_App (mk_range_mle, [Range.file_of_range r |> cstr;
                            Range.start_of_range r |> Range.line_of_pos |> cint;
                            Range.start_of_range r |> Range.col_of_pos  |> cint;
                            Range.end_of_range r   |> Range.line_of_pos |> cint;
                            Range.end_of_range r   |> Range.col_of_pos  |> cint;
                            ])

let mlexpr_of_const (p:Range.range) (c:sconst) : mlexpr' =
    (* Special case ranges, which can be extracted but not as constants.
     * Maybe a sign that there shouldn't really be a Const_range *)
    match c with
    | Const_range r ->
        mlexpr_of_range r

    | _ ->
        MLE_Const (mlconst_of_const p c)

let rec subst_aux (subst:list<(mlident * mlty)>) (t:mlty)  : mlty =
    match t with
    | MLTY_Var  x -> (match BU.find_opt (fun (y, _) -> y=x) subst with
                     | Some ts -> snd ts
                     | None -> t) // TODO : previously, this case would abort. why? this case was encountered while extracting st3.fst
    | MLTY_Fun (t1, f, t2) -> MLTY_Fun(subst_aux subst t1, f, subst_aux subst t2)
    | MLTY_Named(args, path) -> MLTY_Named(List.map (subst_aux subst) args, path)
    | MLTY_Tuple ts -> MLTY_Tuple(List.map (subst_aux subst) ts)
    | MLTY_Top -> MLTY_Top

let try_subst ((formals, t):mltyscheme) (args:list<mlty>) : option<mlty> =
    if List.length formals <> List.length args
    then None
    else Some (subst_aux (List.zip formals args) t)

let subst ts args =
    match try_subst ts args with
    | None ->
      failwith "Substitution must be fully applied (see GitHub issue #490)"
    | Some t ->
      t

let udelta_unfold (g:UEnv.env) = function
    | MLTY_Named(args, n) ->
      begin match UEnv.lookup_ty_const g n with
        | Some ts ->
          begin
            match try_subst ts args with
            | None ->
              failwith (BU.format3 "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                                                 (string_of_mlpath n)
                                                 (BU.string_of_int (List.length args))
                                                 (BU.string_of_int (List.length (fst ts))))
            | Some r -> Some r
          end
        | _ -> None
      end
    | _ -> None

let eff_leq f f' = match f, f' with
    | E_PURE, _          -> true
    | E_GHOST, E_GHOST   -> true
    | E_IMPURE, E_IMPURE -> true
    | _ -> false

let eff_to_string = function
    | E_PURE -> "Pure"
    | E_GHOST -> "Ghost"
    | E_IMPURE -> "Impure"

let join r f f' = match f, f' with
    | E_IMPURE, E_PURE
    | E_PURE  , E_IMPURE
    | E_IMPURE, E_IMPURE -> E_IMPURE
    | E_GHOST , E_GHOST  -> E_GHOST
    | E_PURE  , E_GHOST  -> E_GHOST
    | E_GHOST , E_PURE   -> E_GHOST
    | E_PURE  , E_PURE   -> E_PURE
    | _ -> failwith (BU.format3 "Impossible (%s): Inconsistent effects %s and %s"
                            (Range.string_of_range r)
                            (eff_to_string f) (eff_to_string f'))

let join_l r fs = List.fold_left (join r) E_PURE fs

let mk_ty_fun = List.fold_right (fun (_, t0) t -> MLTY_Fun(t0, E_PURE, t))

type unfold_t = mlty -> option<mlty>

(* type_leq is essentially the lifting of the sub-effect relation, eff_leq, into function types.
   type_leq_c is a coercive variant of type_leq, which implements an optimization to erase the bodies of ghost functions.
   Specifically, a function (f : t -> Pure t') can be subsumed to (t -> Ghost t')
   In the case where f is a function literal, \x. e, subsuming it to (t -> Ghost t') means that we can simply
   erase e to unit right away.
*)
let rec type_leq_c (unfold_ty:unfold_t) (e:option<mlexpr>) (t:mlty) (t':mlty) : (bool * option<mlexpr>) =
    match t, t' with
        | MLTY_Var x, MLTY_Var y ->
          if x = y
          then true, e
          else false, None

        | MLTY_Fun (t1, f, t2), MLTY_Fun (t1', f', t2') ->
          let mk_fun xs body = match xs with
            | [] -> body
            | _ ->
              let e = match body.expr with
                | MLE_Fun(ys, body) -> MLE_Fun(xs@ys, body)
                | _ -> MLE_Fun(xs, body) in
              with_ty (mk_ty_fun xs body.mlty) e in
          begin match e with
            | Some ({expr=MLE_Fun(x::xs, body)}) ->
              if type_leq unfold_ty t1' t1
              && eff_leq f f'
              then if f=E_PURE
                   && f'=E_GHOST
                   then if type_leq unfold_ty t2 t2'
                        then let body = if type_leq unfold_ty t2 ml_unit_ty
                                        then ml_unit
                                        else with_ty t2' <| MLE_Coerce(ml_unit, ml_unit_ty, t2') in
                             true, Some (with_ty (mk_ty_fun [x] body.mlty) <| MLE_Fun([x], body))
                        else false, None
                   else let ok, body = type_leq_c unfold_ty (Some <| mk_fun xs body) t2 t2' in
                        let res = match body with
                            | Some body -> Some (mk_fun [x] body)
                            | _ ->  None in
                        ok, res
              else false, None

            | _ ->
              if type_leq unfold_ty t1' t1
              && eff_leq f f'
              && type_leq unfold_ty t2 t2'
              then true, e
              else false, None
          end

        | MLTY_Named(args, path), MLTY_Named(args', path') ->
          if path=path'
          then if List.forall2 (type_leq unfold_ty) args args'
               then true, e
               else false, None
          else begin match unfold_ty t with
                        | Some t -> type_leq_c unfold_ty e t t'
                        | None -> (match unfold_ty t' with
                                     | None -> false, None
                                     | Some t' -> type_leq_c unfold_ty e t t')
               end

        | MLTY_Tuple ts, MLTY_Tuple ts' ->
          if List.forall2 (type_leq unfold_ty) ts ts'
          then true, e
          else false, None

        | MLTY_Top, MLTY_Top -> true, e

        | MLTY_Named _, _ ->
          begin match unfold_ty t with
            | Some t -> type_leq_c unfold_ty e t t'
            | _ ->  false, None
          end

        | _, MLTY_Named _ ->
          begin match unfold_ty t' with
            | Some t' -> type_leq_c unfold_ty e t t'
            | _ -> false, None
          end

        | _ -> false, None

and type_leq g t1 t2 : bool = type_leq_c g None t1 t2 |> fst

let is_type_abstraction = function
    | (Inl _, _)::_ -> true
    | _ -> false

let is_xtuple (ns, n) =
  if FStar.Parser.Const.is_tuple_datacon_string (BU.concat_l "." (ns@[n]))
  (* Returns the integer k in "Mktuplek" *)
  then Some (BU.int_of_char (BU.char_at n 7))
  else None

let resugar_exp e = match e.expr with
    | MLE_CTor(mlp, args) ->
        (match is_xtuple mlp with
        | Some n -> with_ty e.mlty <| MLE_Tuple args
        | _ -> e)
    | _ -> e

let record_field_path = function
    | f::_ ->
        let ns, _ = BU.prefix f.ns in
        ns |> List.map (fun id -> id.idText)
    | _ -> failwith "impos"

let record_fields fs vs = List.map2 (fun (f:lident) e -> f.ident.idText, e) fs vs
//
//let resugar_pat q p = match p with
//    | MLP_CTor(d, pats) ->
//      begin match is_xtuple d with
//        | Some n -> MLP_Tuple(pats)
//        | _ ->
//          match q with
//            | Some (Record_ctor (_, fns)) ->
//              let p = record_field_path fns in
//              let fs = record_fields fns pats in
//              MLP_Record(p, fs)
//            | _ -> p
//      end
//    | _ -> p


let is_xtuple_ty (ns, n) =
  if FStar.Parser.Const.is_tuple_constructor_string (BU.concat_l "." (ns@[n]))
  (* Returns the integer k in "tuplek" *)
  then Some (BU.int_of_char (BU.char_at n 5))
  else None

let resugar_mlty t = match t with
    | MLTY_Named (args, mlp) ->
      begin match is_xtuple_ty mlp with
        | Some n -> MLTY_Tuple args
        | _ -> t
      end
    | _ -> t

let flatten_ns ns =
    if codegen_fsharp()
    then String.concat "." ns
    else String.concat "_" ns
let flatten_mlpath (ns, n) =
    if codegen_fsharp()
    then String.concat "." (ns@[n])
    else String.concat "_" (ns@[n])
let mlpath_of_lid (l:lident) = (l.ns |> List.map (fun i -> i.idText),  l.ident.idText)

let rec erasableType (unfold_ty:unfold_t) (t:mlty) :bool =
    //printfn "(* erasability of %A is %A *)\n" t (g.erasableTypes t);
   if UEnv.erasableTypeNoDelta t
   then true
   else match unfold_ty t with
     | Some t -> (erasableType unfold_ty t)
     | None  -> false

let rec eraseTypeDeep unfold_ty (t:mlty) : mlty =
    match t with
    | MLTY_Fun (tyd, etag, tycd) -> if etag=E_PURE then MLTY_Fun (eraseTypeDeep unfold_ty tyd, etag, eraseTypeDeep unfold_ty tycd) else t
    | MLTY_Named (lty, mlp) -> if erasableType unfold_ty t then UEnv.erasedContent else MLTY_Named (List.map (eraseTypeDeep unfold_ty) lty, mlp)  // only some named constants are erased to unit.
    | MLTY_Tuple lty ->  MLTY_Tuple (List.map (eraseTypeDeep unfold_ty) lty)
    | _ ->  t

let prims_op_equality = with_ty MLTY_Top <| MLE_Name (["Prims"], "op_Equality")
let prims_op_amp_amp  = with_ty (mk_ty_fun [("x", ml_bool_ty); ("y", ml_bool_ty)] ml_bool_ty) <| MLE_Name (["Prims"], "op_AmpAmp")
let conjoin e1 e2 = with_ty ml_bool_ty <| MLE_App(prims_op_amp_amp, [e1;e2])
let conjoin_opt e1 e2 = match e1, e2 with
    | None, None -> None
    | Some x, None
    | None, Some x -> Some x
    | Some x, Some y -> Some (conjoin x y)

let mlloc_of_range (r: Range.range) =
    let pos = Range.start_of_range r in
    let line = Range.line_of_pos pos in
    line, Range.file_of_range r

let rec doms_and_cod (t:mlty) : list<mlty> * mlty =
    match t with
      | MLTY_Fun (a,_,b) ->
        let ds, c = doms_and_cod b in
        a::ds, c
      | _ ->
          [], t

let argTypes  (t: mlty) : list<mlty> =
    fst (doms_and_cod t)

let rec uncurry_mlty_fun t =
    match t with
    | MLTY_Fun (a,_,b) ->
        let args, res = uncurry_mlty_fun b in
        a::args, res
    | _ -> [], t

(* helper functions used to extract, alongside a tactic, its corresponding call
   to FStar.Tactics.Native.register_tactic *)
module RD = FStar.Reflection.Data

let not_implemented_warning r t msg =
    Errors.log_issue r (Errors.Warning_CallNotImplementedAsWarning, BU.format2 ". Tactic %s will not run natively because %s.\n" t msg)

type emb_decl =
    | Embed
    | Unembed

type embedding = {
    embed  :mlexpr;
    unembed:mlexpr;
    type_repr:mlexpr;
}

type variance =
  | Covariant
  | Contravariant
  | Invariant

module N = FStar.TypeChecker.Normalize
let interpret_plugin_as_term_fun tcenv (fv:lident) (t:typ) (ml_fv:mlexpr') =
    let t = N.normalize [N.Beta; N.EraseUniverses; N.AllowUnboundUniverses] tcenv t in
    let w = with_ty MLTY_Top in
    let lid_to_name l     = with_ty MLTY_Top <| MLE_Name (mlpath_of_lident l) in
    let lid_to_top_name l = with_ty MLTY_Top <| MLE_Name (mlpath_of_lident l) in
    let str_to_name s     = lid_to_name (lid_of_str s) in
    let str_to_top_name s = lid_to_top_name (lid_of_str s) in
    let fstar_syn_syn_prefix s = str_to_name ("FStar_Syntax_Syntax." ^ s) in
    let fstar_tc_common_prefix s = str_to_name ("FStar_TypeChecker_Common." ^ s) in
    let fstar_refl_basic_prefix s = str_to_name ("FStar_Reflection_Basic." ^ s) in
    let fstar_refl_data_prefix s = str_to_name ("FStar_Reflection_Data." ^ s) in
    let fstar_emb_basic_prefix s = str_to_name ("FStar_Syntax_Embeddings." ^ s) in
    let mk_basic_embedding (m: emb_decl) (s: string) =
        match m with
        | Embed -> fstar_emb_basic_prefix ("embed_" ^ s)
        | Unembed -> fstar_emb_basic_prefix ("unembed_" ^ s) in
    let mk_lam nm e =
        w <| MLE_Fun ([(nm, MLTY_Top)], e)
    in
    let id_embedding nm =
        let id = mk_lam "x" (str_to_name "x") in
        { embed = id; unembed = id; type_repr = str_to_name nm}
    in
    let known_type_constructors =
        [ (PC.int_lid,  [], fstar_syn_syn_prefix "t_int");
          (PC.bool_lid, [], fstar_syn_syn_prefix "t_bool");
          (PC.unit_lid, [], fstar_syn_syn_prefix "t_unit");
          (PC.string_lid, [], fstar_syn_syn_prefix "t_string");
          (RD.fstar_refl_types_lid "term", [], fstar_refl_data_prefix "t_term");
          (RD.fstar_refl_types_lid "fv", [], fstar_refl_data_prefix "t_fv");
          (RD.fstar_refl_types_lid "binder", [], fstar_refl_data_prefix "t_binder");
          (RD.fstar_refl_syntax_lid "binders", [], fstar_refl_data_prefix "t_binders");
          (RD.fstar_refl_syntax_lid "norm_step", [], fstar_refl_data_prefix "t_norm_step");
          (PC.list_lid,   [Covariant], fstar_tc_common_prefix "t_list_of"); //one covariant argument
          (PC.option_lid, [Covariant], fstar_tc_common_prefix "t_option_of");
          (PC.mk_tuple_lid 2 Range.dummyRange, [Covariant; Covariant], fstar_tc_common_prefix "t_tuple2_of") //two covariant arguments
        ]
    in
    let is_known_type_constructor fv n =
        BU.for_some
            (fun (x, args, _) -> fv_eq_lid fv x && n = List.length args)
            known_type_constructors
    in
    let embed_type_app (fv:S.fv) (arg_embeddings:list<embedding>) =
        let nm = fv.fv_name.v.ident.idText in
        let _, variances, trepr_head =
            BU.find_opt
                (fun (x, _, _) -> fv_eq_lid fv x)
                known_type_constructors
            |> BU.must
        in
        let choose e_or_u variance embedding =
            let term_embedding =
                 match variance with
                 | Covariant ->
                    (match e_or_u with
                     | Embed   -> [embedding.embed]
                     | Unembed -> [embedding.unembed])
                 | Contravariant ->
                    (match e_or_u with
                     | Embed   -> [embedding.unembed]
                     | Unembed -> [embedding.embed])
                 | Invariant ->
                    [embedding.embed;
                     embedding.unembed]
            in
            term_embedding@[embedding.type_repr]
        in
        let mk embed_or_unembed =
            let head = mk_basic_embedding embed_or_unembed nm in
            match variances with
            | [] -> head
            | _ ->
              let args =
                List.map2 (choose embed_or_unembed) variances arg_embeddings
              in
              w <| MLE_App(head, List.flatten args)
        in
        let type_repr =
            match variances with
            | [] ->
              trepr_head
            | _ ->
              w <| MLE_App (trepr_head,
                            List.map (fun x -> x.type_repr) arg_embeddings)
        in
        { embed   = mk Embed;
          unembed = mk Unembed;
          type_repr = type_repr}
    in
    let find_env_entry bv (bv', _) = S.bv_eq bv bv' in
    let rec mk_embedding (env:list<(bv * embedding)>) t =
        match (FStar.Syntax.Subst.compress t).n with
        | Tm_name bv
             when BU.for_some (find_env_entry bv) env ->
          snd (BU.must (BU.find_opt (find_env_entry bv) env))

        | _ ->
          let t = FStar.TypeChecker.Normalize.unfold_whnf tcenv t in
          let head, args = U.head_and_args t in
          let n_args = List.length args in
          begin
          match (U.un_uinst head).n with
          | Tm_refine(b, _) ->
            mk_embedding env b.sort

          | Tm_fvar fv
              when is_known_type_constructor fv n_args ->
            let arg_embeddings = List.map (fun (t, _) -> mk_embedding env t) args in
            embed_type_app fv arg_embeddings

          | _ ->
            raise_err (Fatal_CallNotImplemented, ("Embedding not defined for type " ^ (Print.term_to_string t)))
          end
    in
    let bs, c = U.arrow_formals_comp t in
    let arity = List.length bs in
    let result_typ = U.comp_result c in
    let type_vars, bs =
        match
            BU.prefix_until
                (fun (b, _) ->
                    match (Subst.compress b.sort).n with
                    | Tm_type _ -> false
                    | _ -> true)
               bs
        with
        | None ->
          bs, []
        | Some (tvars, x, rest) ->
          tvars, x::rest
    in
    let tvar_names = List.mapi (fun i tv -> ("tv_" ^ string_of_int i)) type_vars in
    let tvar_context = List.map2 (fun b nm -> fst b, id_embedding nm) type_vars tvar_names in
    let rec aux accum_embeddings (env:list<(bv * embedding)>) bs =
        match bs with
        | [] ->
          let arg_unembeddings = List.rev accum_embeddings |> List.map (fun x -> x.unembed) in
          let res_embedding = mk_embedding env result_typ in
          if U.is_pure_comp c
          then begin
            let embed_fun_N = mk_basic_embedding Embed ("arrow_" ^ string_of_int arity) in
            let args = arg_unembeddings @ [res_embedding.embed; lid_to_top_name fv] in
            let fun_embedding = w <| MLE_App(embed_fun_N, args) in
            let tabs = List.fold_right mk_lam tvar_names fun_embedding in
            Some (mk_lam "_psc" tabs,
                  arity,
                  true)
          end
          else if Ident.lid_equals (FStar.TypeChecker.Env.norm_eff_name tcenv (U.comp_effect_name c))
                                 PC.tac_effect_lid
          then begin
            let h = str_to_top_name ("FStar_Tactics_Interpreter.mk_tactic_interpretation_" ^ string_of_int arity) in
            let tac_fun = w <| MLE_App (str_to_top_name ("FStar_Tactics_Native.from_tactic_" ^ string_of_int arity), [lid_to_top_name fv]) in
            let tac_lid_app = w <| MLE_App (str_to_top_name "FStar_Ident.lid_of_str", [w ml_fv]) in
            let psc = str_to_name "psc" in
            let args = str_to_name "args" in
            let args =
                [w <| MLE_Const (MLC_Bool true); //trigger a TAC?.reflect
                 tac_fun] @
                arg_unembeddings @
                [res_embedding.embed;
                 res_embedding.type_repr;
                 tac_lid_app;
                 psc;
                 args] in
            Some (mk_lam "psc" <| (mk_lam "args" (w <| MLE_App (h, args))),
                  arity,
                  false)
          end
          else raise_err (Fatal_CallNotImplemented, ("Plugins not defined for type " ^ Print.term_to_string t))

        | (b, _)::bs ->
          aux (mk_embedding env b.sort::accum_embeddings) env bs
    in
    aux [] tvar_context bs

//
//(*
//  Given:
//      fv: a source top-level lident at type fv_t
//      whose name as a string is ml_fv
//
//  builds the ML term:
//      fun psc args ->
//        mk_tactic_interpretation_N
//                true //to insert a TAC?.reflect
//                (from_tactic_N tac_lid)
//                (unembed_b1 ... unembed_bN)
//                (embed_t)
//                (t:FStar.Syntax.Syntax.typ)
//                args
//
// *)
//let interpret_plugin_as_term_fun tcenv (fv:lident) (fv_t:typ) (ml_fv:mlexpr') =
//    let w = with_ty MLTY_Top in
//    let mk_lam nm e =
//        MLE_Fun ([(nm, MLTY_Top)], w e)
//    in
//    try
//        let bs, c = U.arrow_formals_comp fv_t in
//        let arg_types = List.map (fun x -> (fst x).sort) bs in
//        let arity = List.length bs in
//        let result_typ = U.comp_result c in
//        if U.is_pure_comp c
//        then begin
//            let embed_fun_N = with_ty MLTY_Top <| mk_basic_embedding Embed ("arrow_" ^ string_of_int arity) in
//            let un_embeddings = List.map (fun x -> w (must_mk_embedding_path tcenv Unembed x)) arg_types in
//            let embed_res = must_mk_embedding_path tcenv Embed result_typ in
//            let args = un_embeddings @ [w embed_res; lid_to_top_name fv] in
//            Some (mk_lam "_" <| MLE_App(embed_fun_N, args),
//                  arity,
//                  true)
//        end
//        else if Ident.lid_equals (FStar.TypeChecker.Env.norm_eff_name tcenv (U.comp_effect_name c))
//                                 PC.tac_effect_lid
//        then begin
//            let h = str_to_top_name ("FStar_Tactics_Interpreter.mk_tactic_interpretation_" ^ string_of_int arity) in
//            let tac_fun = MLE_App (str_to_top_name ("FStar_Tactics_Native.from_tactic_" ^ string_of_int arity), [lid_to_top_name fv]) in
//            let tac_lid_app = MLE_App (str_to_top_name "FStar_Ident.lid_of_str", [w ml_fv]) in
//            let psc = str_to_name "psc" in
//            let args =
//                [MLE_Const (MLC_Bool true); //trigger a TAC?.reflect
//                 tac_fun] @
//                (List.map (mk_tac_embedding_path tcenv Unembed) arg_types) @
//                [mk_tac_embedding_path tcenv Embed result_typ;
//                 mk_tac_param_type tcenv result_typ;
//                 tac_lid_app;
//                 psc;
//                 str_to_name "args"] in
//            Some (mk_lam "psc" <| (mk_lam "args" <| MLE_App (h, List.map w args)),
//                  arity,
//                  false)
//          end
//          else raise_err (Fatal_CallNotImplemented, ("Plugins not defined for type " ^ Print.term_to_string fv_t))
//    with Errors.Error(Fatal_CallNotImplemented, msg, _)->
//        not_implemented_warning fv_t.pos (string_of_lid fv) msg;
//        None