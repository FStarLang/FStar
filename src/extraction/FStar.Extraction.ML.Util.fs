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
open Prims
open FStar.ST
open FStar.All
open FStar
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
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
module N = FStar.TypeChecker.Normalize
module Env = FStar.TypeChecker.Env


let codegen_fsharp () = Options.codegen () = Some Options.FSharp

let pruneNones (l : list<option<'a>>) : list<'a> =
    List.fold_right (fun  x ll -> match x with
                          | Some xs -> xs::ll
                          | None -> ll) l []


let mk_range_mle = with_ty MLTY_Top <| MLE_Name (["Prims"], "mk_range")
let dummy_range_mle = with_ty MLTY_Top <| MLE_Name (["FStar"; "Range"], "dummyRange")

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
    | MLTY_Top
    | MLTY_Erased -> t

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
        let mk_fun xs body =
            match xs with
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

    | MLTY_Erased, MLTY_Erased ->
      true, e

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
module SEmb = FStar.Syntax.Embeddings
module REmb = FStar.Reflection.Embeddings

exception NoTacticEmbedding of string

let not_implemented_warning r t msg =
    Errors.log_issue r
        (Errors.Warning_CallNotImplementedAsWarning,
         BU.format2 "Plugin %s will not run natively because %s.\n" t msg)

type emb_loc =
    | S (* FStar.Syntax.Embeddings *)
    | R (* FStar.Reflection.Embeddings *)

let interpret_plugin_as_term_fun tcenv (fv:fv) (t:typ) (arity_opt:option<int>) (ml_fv:mlexpr') =
    let fv_lid = fv.fv_name.v in
    let t = N.normalize [
      Env.EraseUniverses;
      Env.AllowUnboundUniverses;
      Env.UnfoldUntil S.delta_constant // unfold abbreviations such as nat
    ] tcenv t in
    let w = with_ty MLTY_Top in
    let lid_to_name l     = with_ty MLTY_Top <| MLE_Name (mlpath_of_lident l) in
    let lid_to_top_name l = with_ty MLTY_Top <| MLE_Name (mlpath_of_lident l) in
    let str_to_name s     = lid_to_name (lid_of_str s) in
    let str_to_top_name s = lid_to_top_name (lid_of_str s) in
    let fstar_syn_emb_prefix s = str_to_name ("FStar_Syntax_Embeddings." ^ s) in
    let fstar_refl_emb_prefix s = str_to_name ("FStar_Reflection_Embeddings." ^ s) in
    let fv_lid_embedded =
        with_ty MLTY_Top <|
            MLE_App (str_to_name "FStar_Ident.lid_of_str",
                     [with_ty MLTY_Top <| MLE_Const (MLC_String (Ident.string_of_lid fv_lid))])
    in
    let mk_basic_embedding (l:emb_loc) (s: string): mlexpr =
        let emb_prefix = match l with
            | S -> fstar_syn_emb_prefix
            | R -> fstar_refl_emb_prefix
        in
        emb_prefix ("e_" ^ s)
    in
    let mk_arrow_as_prim_step (arity: int): mlexpr =
        fstar_syn_emb_prefix ("arrow_as_prim_step_" ^ string_of_int arity)
    in
    let mk_any_embedding (s: string): mlexpr =
        w <| MLE_App(fstar_syn_emb_prefix "mk_any_emb", [str_to_name s])
    in
    let mk_lam nm e =
        w <| MLE_Fun ([(nm, MLTY_Top)], e)
    in
    let emb_arrow e1 e2 =
        w <| MLE_App(fstar_syn_emb_prefix "e_arrow", [e1; e2])
    in
    let known_type_constructors =
        [ (PC.int_lid, 0, "int", S);
          (PC.bool_lid, 0, "bool", S);
          (PC.unit_lid, 0, "unit", S);
          (PC.string_lid, 0, "string", S);
          (RD.fstar_refl_types_lid "term", 0, "term", R);
          (RD.fstar_refl_types_lid "fv", 0, "fv", R);
          (RD.fstar_refl_types_lid "binder", 0, "binder", R);
          (RD.fstar_refl_syntax_lid "binders", 0, "binders", R);
          (PC.norm_step_lid, 0, "norm_step", S);
          (PC.list_lid, 1, "list", S);
          (PC.option_lid, 1, "option", S);
          (PC.mk_tuple_lid 2 Range.dummyRange, 2, "tuple2", S);
          (RD.fstar_refl_data_lid "exp", 0, "exp", R)
        ]
    in

    let is_known_type_constructor fv n =
        BU.for_some
            (fun (x, args, _, _) -> fv_eq_lid fv x && n = args)
            known_type_constructors
    in
    let find_env_entry bv (bv', _) = S.bv_eq bv bv' in
    (*  Generates the ML syntax of a term of type
           `FStar.Syntax.Embeddings.embedding [[t]]`
        where [[t]] is the ML denotation of the F* type t
    *)
    let rec mk_embedding (env:list<(bv * string)>) (t: term): mlexpr =
        let t = FStar.TypeChecker.Normalize.unfold_whnf tcenv t in
        match (FStar.Syntax.Subst.compress t).n with
        | Tm_name bv
             when BU.for_some (find_env_entry bv) env ->
          mk_any_embedding <| snd (BU.must (BU.find_opt (find_env_entry bv) env))

        | Tm_refine (x, _) ->
          (* Refinements are irrelevant to generate embeddings. *)
          mk_embedding env x.sort

        | Tm_ascribed (t, _, _) ->
          mk_embedding env t

        | Tm_arrow ([b], c) when U.is_pure_comp c ->
          let bs, c = FStar.Syntax.Subst.open_comp [b] c in
          let t0 = (fst (List.hd bs)).sort in
          let t1 = U.comp_result c in
          emb_arrow (mk_embedding env t0) (mk_embedding env t1)

        | Tm_arrow(b::more::bs, c) ->
          let tail = S.mk (Tm_arrow(more::bs, c)) None t.pos in
          let t = S.mk (Tm_arrow([b], S.mk_Total tail)) None t.pos in
          mk_embedding env t

        | Tm_fvar _
        | Tm_uinst _
        | Tm_app _ ->
          let head, args = U.head_and_args t in
          let n_args = List.length args in
          begin
          match (U.un_uinst head).n with
          | Tm_fvar fv
              when is_known_type_constructor fv n_args ->
            begin
            let arg_embeddings = List.map (fun (t, _) -> mk_embedding env t) args in
            let nm = fv.fv_name.v.ident.idText in
            let _, t_arity, _trepr_head, loc_embedding =
                BU.find_opt
                    (fun (x, _, _, _) -> fv_eq_lid fv x)
                    known_type_constructors
                |> BU.must
            in
            let head = mk_basic_embedding loc_embedding nm in
            match t_arity with
            | 0 ->
                head
            | n ->
                w <| MLE_App (head, arg_embeddings)
            // embed_type_app fv arg_embeddings
            end

          | _ ->
            raise (NoTacticEmbedding("Embedding not defined for type " ^ (Print.term_to_string t)))
          end

        | _ ->
          raise (NoTacticEmbedding("Embedding not defined for type " ^ (Print.term_to_string t)))
    in
    (* abstract_tvars:
         body is an implicitly polymorphic function over tvar_names
        whose type is of the form `args -> term`

       returns an mlexpr that explicitly abstracts over FStar.Syntax.term
               representations of those type arguments
               peeling away a prefix of args corresponding to the type arguments
     *)
    let abstract_tvars tvar_names (body:mlexpr) : mlexpr =
        match tvar_names with
        | [] ->
          let body =
              w <| MLE_App(str_to_name "FStar_Syntax_Embeddings.debug_wrap",
                            [with_ty MLTY_Top <| MLE_Const (MLC_String (Ident.string_of_lid fv_lid));
                             mk_lam "_" (w <| MLE_App(body, [str_to_name "args"]))])
          in
          mk_lam "args" body
        | _ ->
          let args_tail = MLP_Var "args_tail" in
          let mk_cons hd_pat tail_pat =
              MLP_CTor ((["Prims"], "Cons"), [hd_pat; tail_pat])
          in
          let fst_pat v =
              MLP_Tuple [MLP_Var v; MLP_Wild]
          in
          let pattern =
              List.fold_right
                (fun hd_var -> mk_cons (fst_pat hd_var))
                tvar_names
                args_tail
          in
          let branch =
             pattern,
             None,
             w <| MLE_App(body, [str_to_name "args"])
          in
          let default_branch =
              MLP_Wild,
              None,
              w <| MLE_App(str_to_name "failwith",
                            [w <| mlexpr_of_const
                                   Range.dummyRange
                                   (FStar.Const.Const_string("arity mismatch", Range.dummyRange))])
          in
          let body =
              w <| MLE_Match(str_to_name "args", [branch; default_branch])
          in
          let body =
              w <| MLE_App(str_to_name "FStar_Syntax_Embeddings.debug_wrap",
                            [with_ty MLTY_Top <| MLE_Const (MLC_String (Ident.string_of_lid fv_lid));
                             mk_lam "_" body])
          in
          mk_lam "args" body
    in
    (* We're trying to register a plugin or tactic
       ml_fv which has source F* type t *)
    let bs, c = U.arrow_formals_comp t in
    let bs, c =
        match arity_opt with
        | None -> bs, c
        | Some n ->
          let n_bs = List.length bs in
          if n = n_bs then bs, c
          else if n < n_bs
          then let bs, rest = BU.first_N n bs in
               BU.print2 "Restricting arity of %s to %s\n"
                (Ident.string_of_lid fv_lid)
                (BU.string_of_int n);
               let c = S.mk_Total <| U.arrow rest c in
               bs, c
          else // n > bs
               let msg =
                BU.format3
                    "Embedding not defined for %s; expected arity at least %s; got %s"
                    (Ident.string_of_lid fv_lid)
                    (BU.string_of_int n)
                    (BU.string_of_int n_bs) in
               raise (NoTacticEmbedding msg)
    in
    let result_typ = U.comp_result c in
    let arity = List.length bs in
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
    (* Explicit polymorphism in the source type `t`
       is turned into implicit polymorphism in ML.

           `t` is really `forall type_vars. bs -> result_typ`
    *)
    let tvar_arity = List.length type_vars in
    let non_tvar_arity = List.length bs in
    let tvar_names = List.mapi (fun i tv -> ("tv_" ^ string_of_int i)) type_vars in
    let tvar_context : list<(bv * string)> = List.map2 (fun b nm -> fst b, nm) type_vars tvar_names in
    // The tvar_context records all the ML type variables in scope
    // All their embeddings will be just identity embeddings

    (* aux: The main function that builds the registration code

        accum_embeddings: all the embeddings of the arguments (in reverse order)
        bs: the remaining arguments

        returns (mlexpr, //the registration code
                 int,    //the arity of the compiled code (+1 for tactics)
                 bool)   //true if this is a tactic
    *)
    let rec aux accum_embeddings bs : (mlexpr * int * bool) =
        match bs with
        | [] ->
          let arg_unembeddings = List.rev accum_embeddings in
          let res_embedding = mk_embedding tvar_context result_typ in
          let fv_lid = fv.fv_name.v in
          if U.is_pure_comp c
          then begin
            let ncb = str_to_name "ncb" in
            let embed_fun_N = mk_arrow_as_prim_step non_tvar_arity in
            let args = arg_unembeddings
                    @ [res_embedding;
                       lid_to_top_name fv_lid;
                       with_ty MLTY_Top <| MLE_Const (MLC_Int(string_of_int tvar_arity, None));
                       fv_lid_embedded;
                       ncb]
            in
            let fun_embedding = w <| MLE_App(embed_fun_N, args) in
            let tabs = abstract_tvars tvar_names fun_embedding in
            (mk_lam "_psc" (mk_lam "ncb" tabs),
             arity,
             true)
          end
          else if Ident.lid_equals (FStar.TypeChecker.Env.norm_eff_name tcenv (U.comp_effect_name c))
                                    PC.effect_TAC_lid
          then begin
            let h = str_to_top_name ("FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
                                     ^ string_of_int non_tvar_arity)
            in
            let tac_fun = w <| MLE_App (str_to_top_name ("FStar_Tactics_Native.from_tactic_"
                                                         ^ string_of_int non_tvar_arity),
                          [lid_to_top_name fv_lid])
            in
            let tac_lid_app = w <| MLE_App (str_to_top_name "FStar_Ident.lid_of_str", [w ml_fv]) in
            let psc = str_to_name "psc" in
            let ncb = str_to_name "ncb" in
            let all_args = str_to_name "args" in
            let args =
                [tac_fun] @
                arg_unembeddings @
                [res_embedding;
                 tac_lid_app;
                 psc;
                 ncb] in
            let tabs =
              match tvar_names with
              | [] -> mk_lam "args" (w <| MLE_App (h, args@[all_args]))
              | _ -> abstract_tvars tvar_names (w <| MLE_App (h, args))
            in
            (mk_lam "psc" (mk_lam "ncb" tabs),
             arity + 1,
             false)
          end
          else raise (NoTacticEmbedding("Plugins not defined for type " ^ Print.term_to_string t))

        | (b, _)::bs ->
          aux (mk_embedding tvar_context b.sort::accum_embeddings) bs
    in
    try
        Some (aux [] bs)
    with
    | NoTacticEmbedding msg ->
      not_implemented_warning t.pos (FStar.Syntax.Print.fv_to_string fv) msg;
      None
