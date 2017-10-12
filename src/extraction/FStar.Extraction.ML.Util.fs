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
module BU = FStar.Util
module U = FStar.Syntax.Util
module UEnv = FStar.Extraction.ML.UEnv
module PC = FStar.Parser.Const

let pruneNones (l : list<option<'a>>) : list<'a> =
    List.fold_right (fun  x ll -> match x with
                          | Some xs -> xs::ll
                          | None -> ll) l []


let mlconst_of_const (sctt : sconst) =
  match sctt with
  | Const_range _
  | Const_effect       -> failwith "Unsupported constant"
  | Const_unit         -> MLC_Unit
  | Const_char   c     -> MLC_Char  c
  | Const_int    (s, i)-> MLC_Int   (s, i)
  | Const_bool   b     -> MLC_Bool  b
  | Const_float  d     -> MLC_Float d

  | Const_bytearray (bytes, _) ->
      MLC_Bytes bytes

  | Const_string (s, _) -> MLC_String (s)

  | Const_reify
  | Const_reflect _ ->
    failwith "Unhandled constant: reify/reflect"

let mlconst_of_const' (p:Range.range) (c:sconst) =
    try mlconst_of_const c
    with _ -> failwith (BU.format2 "(%s) Failed to translate constant %s " (Range.string_of_range p) (Print.const_to_string c))

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
    if Options.codegen_fsharp()
    then String.concat "." ns
    else String.concat "_" ns
let flatten_mlpath (ns, n) =
    if Options.codegen_fsharp()
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

exception CallNotImplemented
let not_implemented_warning t = BU.print1_warning ". Tactic %s will not run natively.\n" t

type emb_decl =
    | Embed
    | Unembed

let lid_to_name l = MLE_Name (mlpath_of_lident l)
let lid_to_top_name l = with_ty MLTY_Top <| MLE_Name (mlpath_of_lident l)
let str_to_name s = lid_to_name (lid_of_str s)
let str_to_top_name s = lid_to_top_name (lid_of_str s)

let fstar_syn_syn_prefix s = str_to_name ("FStar_Syntax_Syntax." ^ s)
let fstar_tc_common_prefix s = str_to_name ("FStar_TypeChecker_Common." ^ s)
let fstar_refl_basic_prefix s = str_to_name ("FStar_Reflection_Basic." ^ s)
let fstar_refl_data_prefix s = str_to_name ("FStar_Reflection_Data." ^ s)
let fstar_emb_basic_prefix s = str_to_name ("FStar_Syntax_Embeddings." ^ s)

let mk_basic_embedding (m: emb_decl) (s: string) =
    match m with
    | Embed -> fstar_emb_basic_prefix ("embed_" ^ s)
    | Unembed -> fstar_emb_basic_prefix ("unembed_" ^ s)
let mk_embedding (m: emb_decl) (s: string) =
    match m with
    | Embed -> fstar_refl_basic_prefix ("embed_" ^ s)
    | Unembed -> fstar_refl_basic_prefix ("unembed_" ^ s)

let mk_tactic_unembedding (args: list<mlexpr'>) =
    let tac_arg = "t" in
    let reify_tactic = with_ty MLTY_Top  <| MLE_App (str_to_top_name "FStar_Tactics_Interpreter.reify_tactic", [str_to_top_name tac_arg]) in
    let from_tac = str_to_top_name ("FStar_Tactics_Builtins.from_tac_" ^ BU.string_of_int (List.length args-1)) in
    let unembed_tactic = str_to_top_name ("FStar_Tactics_Interpreter.unembed_tactic_" ^ BU.string_of_int (List.length args-1)) in
    let app = match (List.length args) with
    | 1 -> MLE_App (from_tac, [with_ty MLTY_Top (MLE_App (unembed_tactic, List.map (with_ty MLTY_Top) args@[reify_tactic]))])
    | n ->
        BU.print1_warning "Unembedding not defined for tactics of %s arguments\n" (BU.string_of_int n);
        raise CallNotImplemented in
    MLE_Fun ([(tac_arg, MLTY_Top); ("()", MLTY_Top)], with_ty MLTY_Top app)

let rec mk_tac_param_type (t: term): mlexpr' =
    match (FStar.Syntax.Subst.compress t).n with
    | Tm_fvar fv when fv_eq_lid fv PC.int_lid -> fstar_syn_syn_prefix "t_int"
    | Tm_fvar fv when fv_eq_lid fv PC.bool_lid -> fstar_syn_syn_prefix "t_bool"
    | Tm_fvar fv when fv_eq_lid fv PC.unit_lid -> fstar_syn_syn_prefix "t_unit"
    | Tm_fvar fv when fv_eq_lid fv PC.string_lid -> fstar_syn_syn_prefix "t_string"
    | Tm_fvar fv when fv_eq_lid fv (RD.fstar_refl_types_lid "binder") -> fstar_refl_data_prefix "t_binder"
    | Tm_fvar fv when fv_eq_lid fv (RD.fstar_refl_types_lid "term") -> fstar_refl_data_prefix "t_term"
    | Tm_fvar fv when fv_eq_lid fv (RD.fstar_refl_types_lid "fv") -> fstar_refl_data_prefix "t_fv"
    | Tm_fvar fv when fv_eq_lid fv (RD.fstar_refl_syntax_lid "binder") -> fstar_refl_data_prefix "t_binders"
    | Tm_fvar fv when fv_eq_lid fv (RD.fstar_refl_syntax_lid "norm_step") -> fstar_refl_data_prefix "t_norm_step"
    | Tm_app (h, args) ->
       (match (FStar.Syntax.Subst.compress h).n with
        | Tm_uinst (h', _) ->
           (match (FStar.Syntax.Subst.compress h').n with
            | Tm_fvar fv when fv_eq_lid fv PC.list_lid ->
                let arg_term = fst (List.hd args) in
                MLE_App (with_ty MLTY_Top (fstar_tc_common_prefix "t_list_of"), List.map (with_ty MLTY_Top) [mk_tac_param_type arg_term])
            | Tm_fvar fv when fv_eq_lid fv PC.option_lid ->
                let arg_term = fst (List.hd args) in
                MLE_App (with_ty MLTY_Top (fstar_tc_common_prefix "t_option_of"), List.map (with_ty MLTY_Top) [mk_tac_param_type arg_term] )
            | _ ->
                BU.print_warning ("Type term not defined for higher-order type " ^ (Print.term_to_string (FStar.Syntax.Subst.compress h')));
                raise CallNotImplemented)
        | _ ->
            BU.print_warning "Impossible\n";
            raise CallNotImplemented)
     | _ ->
         BU.print_warning ("Type term not defined for " ^ (Print.term_to_string (FStar.Syntax.Subst.compress t)));
         raise CallNotImplemented

(* Except for the `tactic` type, which is handled specially, this assumes that functions for embedding/unembedding a type
   live in the same place and are named embed_x, unembed_x *)
let rec mk_tac_embedding_path (m: emb_decl) (t: term): mlexpr' =
    match (FStar.Syntax.Subst.compress t).n with
    | Tm_fvar fv when fv_eq_lid fv PC.int_lid -> mk_basic_embedding m "int"
    | Tm_fvar fv when fv_eq_lid fv PC.bool_lid -> mk_basic_embedding m "bool"
    | Tm_fvar fv when fv_eq_lid fv PC.unit_lid -> mk_basic_embedding m "unit"
    | Tm_fvar fv when fv_eq_lid fv PC.string_lid -> mk_basic_embedding m "string"
    | Tm_fvar fv when fv_eq_lid fv (RD.fstar_refl_types_lid "binder") -> mk_embedding m "binder"
    | Tm_fvar fv when fv_eq_lid fv (RD.fstar_refl_types_lid "term") -> mk_embedding m "term"
    | Tm_fvar fv when fv_eq_lid fv (RD.fstar_refl_types_lid "fv") -> mk_embedding m "fvar"
    | Tm_fvar fv when fv_eq_lid fv (RD.fstar_refl_syntax_lid "binders") -> mk_embedding m "binders"
    | Tm_fvar fv when fv_eq_lid fv (RD.fstar_refl_syntax_lid "norm_step") -> mk_embedding m "norm_step"
    | Tm_app (h, args) ->
        (match (FStar.Syntax.Subst.compress h).n with
         | Tm_uinst (h', _) ->
            let ht, hargs, type_arg, is_tactic =
                (match (FStar.Syntax.Subst.compress h').n with
                 | Tm_fvar fv when fv_eq_lid fv PC.list_lid ->
                     let arg_term = fst (List.hd args) in
                     "list", [mk_tac_embedding_path m arg_term], mk_tac_param_type arg_term, false
                 | Tm_fvar fv when fv_eq_lid fv PC.option_lid ->
                     let arg_term = fst (List.hd args) in
                     "option", [mk_tac_embedding_path m arg_term], mk_tac_param_type arg_term, false
                 | Tm_fvar fv when fv_eq_lid fv PC.tactic_lid ->
                     let arg_term = fst (List.hd args) in
                     "list", [mk_tac_embedding_path m arg_term], mk_tac_param_type arg_term, true
                 | _ ->
                     BU.print_warning ("Embedding not defined for higher-order type " ^ (Print.term_to_string (FStar.Syntax.Subst.compress h')));
                     raise CallNotImplemented) in
            let hargs =
                match m with
                | Embed -> hargs @ [type_arg]
                | Unembed -> hargs in
            if is_tactic then
                match m with
                | Embed ->
                    BU.print_warning "Embedding not defined for tactic type\n";
                    raise CallNotImplemented
                | Unembed -> mk_tactic_unembedding hargs
            else
                MLE_App (with_ty MLTY_Top (mk_basic_embedding m ht), List.map (with_ty MLTY_Top) hargs)
         | _ ->
             BU.print_warning "Impossible\n";
             raise CallNotImplemented)
    | _ ->
        BU.print_warning ("Embedding not defined for type " ^ (Print.term_to_string (FStar.Syntax.Subst.compress t)));
        raise CallNotImplemented

let mk_interpretation_fun tac_lid assm_lid t bs =
    try
        let arg_types = List.map (fun x -> (fst x).sort) bs in
        let arity = List.length bs in
        let h = str_to_top_name ("FStar_Tactics_Interpreter.mk_tactic_interpretation_" ^ string_of_int arity) in
        let tac_fun = MLE_App (str_to_top_name ("FStar_Tactics_Native.from_tactic_" ^ string_of_int arity), [lid_to_top_name tac_lid]) in
        let tac_lid_app = MLE_App (str_to_top_name "FStar_Ident.lid_of_str", [with_ty MLTY_Top assm_lid]) in
        let args =
            [tac_fun] @
            (List.map (mk_tac_embedding_path Unembed) arg_types) @
            [mk_tac_embedding_path Embed t; mk_tac_param_type t; tac_lid_app; str_to_name "args"] in
        let app = with_ty MLTY_Top <| MLE_App (h, List.map (with_ty MLTY_Top) args) in
        Some (MLE_Fun ([("args", MLTY_Top)], app))
    with CallNotImplemented ->
        not_implemented_warning (string_of_lid tac_lid);
        None
