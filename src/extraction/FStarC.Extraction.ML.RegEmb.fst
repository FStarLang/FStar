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
module FStarC.Extraction.ML.RegEmb

(* This module handles registering plugins and generating
embeddings for their types. *)

open FStar open FStarC
open FStarC.Compiler
open FStarC.Compiler.Effect
open FStarC.Compiler.List
open FStarC.Const
open FStarC.Extraction.ML.Syntax
open FStarC.Extraction.ML.UEnv
open FStarC.Syntax.Syntax

module BU    = FStarC.Compiler.Util
module Code  = FStarC.Extraction.ML.Code
module EMB   = FStarC.Syntax.Embeddings
module Env   = FStarC.TypeChecker.Env
module N     = FStarC.TypeChecker.Normalize
module NBET  = FStarC.TypeChecker.NBETerm
module PC    = FStarC.Parser.Const
module Print = FStarC.Syntax.Print
module RC    = FStarC.Reflection.V2.Constants
module S     = FStarC.Syntax.Syntax
module SS    = FStarC.Syntax.Subst
module Term  = FStarC.Extraction.ML.Term
module U     = FStarC.Syntax.Util
module Util  = FStarC.Extraction.ML.Util

open FStarC.Class.Show
open FStarC.Class.Tagged

exception NoEmbedding of string
exception Unsupported of string

(*** ML syntax helpers ***)
let splitlast s = let x::xs = List.rev s in (List.rev xs, x)

let mk e = with_ty MLTY_Top e

let ml_name : Ident.lid -> mlexpr =
  fun l ->
    let s = Ident.path_of_lid l in
    let ns, id = splitlast s in
    mk (MLE_Name (ns, id))

let ml_name' : string -> mlexpr =
  fun s ->
    ml_name (Ident.lid_of_str s)

let ml_ctor : Ident.lid -> list mlexpr -> mlexpr =
  fun l args ->
    let s = Ident.path_of_lid l in
    let ns, id = splitlast s in
    mk (MLE_CTor ((ns, id), args))

let ml_record : Ident.lid -> list (string & mlexpr) -> mlexpr =
  fun l args ->
    let s = Ident.path_of_lid l in
    // [] -> assuming same module
    mk (MLE_Record ([], l |> Ident.ident_of_lid |> Ident.string_of_id, args))

let mk_binder x t = {mlbinder_name=x; mlbinder_ty=t; mlbinder_attrs=[]}

let ml_lam nm e =
    mk <| MLE_Fun ([mk_binder nm MLTY_Top ], e)

let ml_none : mlexpr = mk (MLE_Name (["FStar"; "Pervasives"; "Native"], "None"))
let ml_some : mlexpr = mk (MLE_Name (["FStar"; "Pervasives"; "Native"], "Some"))

let s_tdataconstr =
  mk (MLE_Name (splitlast ["Fstar_guts.FStarC"; "Syntax"; "Syntax"; "tdataconstr"]))
let mk_app =
  mk (MLE_Name (splitlast ["Fstar_guts.FStarC"; "Syntax"; "Util"; "mk_app"]))

let tm_fvar =
  mk (MLE_Name (splitlast ["Fstar_guts.FStarC"; "Syntax"; "Syntax"; "Tm_fvar"]))
let fv_eq_lid =
  mk (MLE_Name (splitlast ["Fstar_guts.FStarC"; "Syntax"; "Syntax"; "fv_eq_lid"]))
let lid_of_str =
  mk (MLE_Name (splitlast ["Fstar_guts.FStarC"; "Ident"; "lid_of_str"]))

let nil_lid        = Ident.lid_of_str "Prims.Nil"
let cons_lid       = Ident.lid_of_str "Prims.Cons"

let embed      = mk (MLE_Name (splitlast ["Fstar_guts.FStarC"; "Syntax"; "Embeddings"; "Base"; "extracted_embed"]))
let unembed    = mk (MLE_Name (splitlast ["Fstar_guts.FStarC"; "Syntax"; "Embeddings"; "Base"; "extracted_unembed"]))
let bind_opt   = mk (MLE_Name (splitlast ["Fstar_guts.FStarC"; "Compiler"; "Util"; "bind_opt"]))

let ml_nbe_unsupported : mlexpr =
  (* extraction thunks this definition *)
  let hd = mk (MLE_Name (["Fstar_guts.FStarC"; "TypeChecker"; "NBETerm"], "e_unsupported")) in
  mk (MLE_App (hd, [ml_unit]))

let ml_magic : mlexpr =
  mk (MLE_Coerce (ml_unit, MLTY_Top, MLTY_Top))

let as_name mlp = with_ty MLTY_Top <| MLE_Name mlp

let ml_failwith (s:string) : mlexpr =
  mk <| MLE_App(as_name ([], "failwith"), [mk <| MLE_Const (MLC_String s)])

let rec as_ml_list (ts : list mlexpr) : mlexpr =
  match ts with
  | [] -> ml_ctor nil_lid []
  | t::ts -> ml_ctor cons_lid [t; as_ml_list ts]

let rec pats_to_list_pat (vs : list mlpattern) : mlpattern =
  match vs with
  | [] -> MLP_CTor ((["Prims"], "Nil"), [])
  | p::ps -> MLP_CTor ((["Prims"], "Cons"), [p; pats_to_list_pat ps])
(*** / ML syntax helpers ***)

let fresh : string -> string =
  let r = BU.mk_ref 0 in
  fun s ->
    let v = !r in
    r := v+1;
    s^"_"^(string_of_int v)

let not_implemented_warning (r: Range.range) (t: string) (msg: string) =
  let open FStarC.Pprint in
  let open FStarC.Errors.Msg in
  let open FStarC.Class.PP in
  Errors.log_issue r Errors.Warning_PluginNotImplemented [
    prefix 2 1 (text (BU.format1 "Plugin `%s' can not run natively because:" t))
      (text msg);
    text "Use --warn_error -"
      ^^ pp (Errors.error_number (Errors.lookup Errors.Warning_PluginNotImplemented))
      ^/^ text "to carry on."
  ]

type embedding_data = {
  arity : int;
  syn_emb : Ident.lid; (* lid for regular embedding *)
  nbe_emb : option Ident.lid; (* nbe embedding, optional! will abort _at runtime_ if None and called *)
}

(*** List of registered embeddings ***)
let builtin_embeddings : list (Ident.lident & embedding_data) =
  let syn_emb_lid s      = Ident.lid_of_path ["Fstar_guts.FStarC"; "Syntax"; "Embeddings"; s] Range.dummyRange in
  let nbe_emb_lid s      = Ident.lid_of_path ["Fstar_guts.FStarC"; "TypeChecker"; "NBETerm"; s] Range.dummyRange in
  let refl_emb_lid s     = Ident.lid_of_path ["Fstar_guts.FStarC"; "Reflection"; "V2"; "Embeddings"; s] Range.dummyRange in
  let nbe_refl_emb_lid s = Ident.lid_of_path ["Fstar_guts.FStarC"; "Reflection"; "V2"; "NBEEmbeddings"; s] Range.dummyRange in
  [
    (PC.int_lid,                          {arity=0; syn_emb=syn_emb_lid  "e_int";        nbe_emb=Some(nbe_emb_lid "e_int")});
    (PC.bool_lid,                         {arity=0; syn_emb=syn_emb_lid  "e_bool";       nbe_emb=Some(nbe_emb_lid "e_bool")});
    (PC.unit_lid,                         {arity=0; syn_emb=syn_emb_lid  "e_unit";       nbe_emb=Some(nbe_emb_lid "e_unit")});
    (PC.string_lid,                       {arity=0; syn_emb=syn_emb_lid  "e_string";     nbe_emb=Some(nbe_emb_lid "e_string")});
    (PC.norm_step_lid,                    {arity=0; syn_emb=syn_emb_lid  "e_norm_step";  nbe_emb=Some(nbe_emb_lid "e_norm_step")});
    (PC.__range_lid,                      {arity=0; syn_emb=syn_emb_lid  "e___range";    nbe_emb=Some(nbe_emb_lid "e___range")});

    (PC.vconfig_lid,                      {arity=0; syn_emb=syn_emb_lid  "e_vconfig";    nbe_emb=Some(nbe_emb_lid "e_vconfig")});

    (PC.list_lid,                         {arity=1; syn_emb=syn_emb_lid  "e_list";       nbe_emb=Some(nbe_emb_lid "e_list")});
    (PC.option_lid,                       {arity=1; syn_emb=syn_emb_lid  "e_option";     nbe_emb=Some(nbe_emb_lid "e_option")});
    (PC.sealed_lid,                       {arity=1; syn_emb=syn_emb_lid  "e_sealed";     nbe_emb=Some(nbe_emb_lid "e_sealed")});

    (PC.mk_tuple_lid 2 Range.dummyRange,  {arity=2; syn_emb=syn_emb_lid  "e_tuple2";     nbe_emb=Some(nbe_emb_lid "e_tuple2")});
    (PC.mk_tuple_lid 3 Range.dummyRange,  {arity=3; syn_emb=syn_emb_lid  "e_tuple3";     nbe_emb=Some(nbe_emb_lid "e_tuple3")});
    (PC.either_lid,                       {arity=2; syn_emb=syn_emb_lid  "e_either";     nbe_emb=Some(nbe_emb_lid "e_either")});

    (* Reflection base types *)
    (RC.fstar_refl_types_lid "namedv",    {arity=0; syn_emb=refl_emb_lid "e_namedv";    nbe_emb=Some(nbe_refl_emb_lid "e_namedv")});
    (RC.fstar_refl_types_lid "bv",        {arity=0; syn_emb=refl_emb_lid "e_bv";        nbe_emb=Some(nbe_refl_emb_lid "e_bv")});
    (RC.fstar_refl_types_lid "binder",    {arity=0; syn_emb=refl_emb_lid "e_binder";    nbe_emb=Some(nbe_refl_emb_lid "e_binder")});
    (RC.fstar_refl_types_lid "term",      {arity=0; syn_emb=refl_emb_lid "e_term";      nbe_emb=Some(nbe_refl_emb_lid "e_term")});
    (RC.fstar_refl_types_lid "env",       {arity=0; syn_emb=refl_emb_lid "e_env";       nbe_emb=Some(nbe_refl_emb_lid "e_env")});
    (RC.fstar_refl_types_lid "fv",        {arity=0; syn_emb=refl_emb_lid "e_fv";        nbe_emb=Some(nbe_refl_emb_lid "e_fv")});
    (RC.fstar_refl_types_lid "comp",      {arity=0; syn_emb=refl_emb_lid "e_comp";      nbe_emb=Some(nbe_refl_emb_lid "e_comp")});
    (RC.fstar_refl_types_lid "sigelt",    {arity=0; syn_emb=refl_emb_lid "e_sigelt";    nbe_emb=Some(nbe_refl_emb_lid "e_sigelt")});
    (RC.fstar_refl_types_lid "ctx_uvar_and_subst", {arity=0; syn_emb=refl_emb_lid "e_ctx_uvar_and_subst"; nbe_emb=Some(nbe_refl_emb_lid "e_ctx_uvar_and_subst")});
    (RC.fstar_refl_types_lid "letbinding",{arity=0; syn_emb=refl_emb_lid "e_letbinding";nbe_emb=Some(nbe_refl_emb_lid "e_letbinding")});
    (RC.fstar_refl_types_lid "ident",     {arity=0; syn_emb=refl_emb_lid "e_ident";     nbe_emb=Some(nbe_refl_emb_lid "e_ident")});
    (RC.fstar_refl_types_lid "universe_uvar", {arity=0; syn_emb=refl_emb_lid "e_universe_uvar"; nbe_emb=Some(nbe_refl_emb_lid "e_universe_uvar")});
    (RC.fstar_refl_types_lid "universe",  {arity=0; syn_emb=refl_emb_lid "e_universe";  nbe_emb=Some(nbe_refl_emb_lid "e_universe")});

    (* Views and datatypes *)
    (RC.fstar_refl_data_lid  "vconst",         {arity=0; syn_emb=refl_emb_lid "e_vconst";         nbe_emb=Some(nbe_refl_emb_lid "e_vconst")});
    (RC.fstar_refl_data_lid  "aqualv",         {arity=0; syn_emb=refl_emb_lid "e_aqualv";         nbe_emb=Some(nbe_refl_emb_lid "e_aqualv")});
    (RC.fstar_refl_data_lid  "pattern",        {arity=0; syn_emb=refl_emb_lid "e_pattern";        nbe_emb=Some(nbe_refl_emb_lid "e_pattern")});
    (RC.fstar_refl_data_lid  "namedv_view",    {arity=0; syn_emb=refl_emb_lid "e_namedv_view";    nbe_emb=Some(nbe_refl_emb_lid "e_namedv_view")});
    (RC.fstar_refl_data_lid  "bv_view",        {arity=0; syn_emb=refl_emb_lid "e_bv_view";        nbe_emb=Some(nbe_refl_emb_lid "e_bv_view")});
    (RC.fstar_refl_data_lid  "binder_view",    {arity=0; syn_emb=refl_emb_lid "e_binder_view";    nbe_emb=Some(nbe_refl_emb_lid "e_binder_view")});
    (RC.fstar_refl_data_lid  "binding",        {arity=0; syn_emb=refl_emb_lid "e_binding";        nbe_emb=Some(nbe_refl_emb_lid "e_binding")});
    (RC.fstar_refl_data_lid  "universe_view",  {arity=0; syn_emb=refl_emb_lid "e_universe_view";  nbe_emb=Some(nbe_refl_emb_lid "e_universe_view")});
    (RC.fstar_refl_data_lid  "term_view",      {arity=0; syn_emb=refl_emb_lid "e_term_view";      nbe_emb=Some(nbe_refl_emb_lid "e_term_view")});
    (RC.fstar_refl_data_lid  "comp_view",      {arity=0; syn_emb=refl_emb_lid "e_comp_view";      nbe_emb=Some(nbe_refl_emb_lid "e_comp_view")});
    (RC.fstar_refl_data_lid  "lb_view",        {arity=0; syn_emb=refl_emb_lid "e_lb_view";        nbe_emb=Some(nbe_refl_emb_lid "e_lb_view")});
    (RC.fstar_refl_data_lid  "sigelt_view",    {arity=0; syn_emb=refl_emb_lid "e_sigelt_view";    nbe_emb=Some(nbe_refl_emb_lid "e_sigelt_view")});
    (RC.fstar_refl_data_lid  "qualifier",      {arity=0; syn_emb=refl_emb_lid "e_qualifier";      nbe_emb=Some(nbe_refl_emb_lid "e_qualifier")});
  ]

let dbg_plugin = Debug.get_toggle "Plugins"

let local_fv_embeddings : ref (list (Ident.lident & embedding_data)) = BU.mk_ref []
let register_embedding (l: Ident.lident) (d: embedding_data) : unit =
  if !dbg_plugin then
    BU.print1 "Registering local embedding for %s\n" (Ident.string_of_lid l);
  local_fv_embeddings := (l,d) :: !local_fv_embeddings

let list_local () = !local_fv_embeddings

let find_fv_embedding' (l: Ident.lident) : option embedding_data =
  match List.find (fun (l', _) -> Ident.lid_equals l l')
        (!local_fv_embeddings @ builtin_embeddings)
  with
  | Some (_, data) -> Some data
  | None -> None

let find_fv_embedding (l: Ident.lident) : embedding_data =
  match find_fv_embedding' l with
  | Some data -> data
  | None ->
    raise (NoEmbedding ("Embedding not defined for type " ^ Ident.string_of_lid l))

(*** /List of registered embeddings ***)

type embedding_kind =
  | SyntaxTerm
  | NBETerm

(*** Make an embedding for a composite type (arrows, tuples, list, etc). The environment
is a mapping from variable names into their embeddings. *)
let rec embedding_for
    (tcenv:Env.env)
    (mutuals: list Ident.lid)
    (k: embedding_kind)
    (env:list (bv & string))
    (t: term)
: mlexpr
= let str_to_name s     = as_name ([], s) in
  let emb_arrow e1 e2 =
    let comb =
      match k with
      | SyntaxTerm -> mk <| MLE_Name (["Fstar_guts.FStarC"; "Syntax"; "Embeddings"], "e_arrow")
      | NBETerm    -> mk <| MLE_Name (["Fstar_guts.FStarC"; "TypeChecker"; "NBETerm"], "e_arrow")
    in
    mk (MLE_App (comb, [e1; e2]))
  in
  let find_env_entry bv (bv', _) = S.bv_eq bv bv' in
  (*
   * We need the whnf to reduce things like
   *   ppname_t ~> Inhabited.sealed_ string "" ~> Sealed.sealed string
   * If we just unfold variable, we will hit lambdas.
   *)
  let t = N.unfold_whnf tcenv t in
  let t = U.un_uinst t in
  let t = SS.compress t in
  match t.n with
  (* A name, explain (why e_any?) *)
  | Tm_name bv when BU.for_some (find_env_entry bv) env ->
    let comb =
      match k with
      | SyntaxTerm -> mk <| MLE_Name (["Fstar_guts.FStarC"; "Syntax"; "Embeddings"], "mk_any_emb")
      | NBETerm    -> mk <| MLE_Name (["Fstar_guts.FStarC"; "TypeChecker"; "NBETerm"], "mk_any_emb")
    in
    let s = snd (BU.must (BU.find_opt (find_env_entry bv) env)) in
    mk <| MLE_App(comb, [str_to_name s])

  (* Refinements are irrelevant for embeddings. *)
  | Tm_refine {b=x} ->
    embedding_for tcenv mutuals k env x.sort

  (* Ascriptions are irrelevant for embeddings. *)
  | Tm_ascribed {tm=t} ->
    embedding_for tcenv mutuals k env t

  (* Pure arrow *)
  | Tm_arrow {bs=[b]; comp=c} when U.is_pure_comp c ->
    let [b], c = FStarC.Syntax.Subst.open_comp [b] c in
    let t0 = b.binder_bv.sort in
    let t1 = U.comp_result c in
    emb_arrow (embedding_for tcenv mutuals k env t0) (embedding_for tcenv mutuals k env t1)

  (* More than 1 binder, curry and retry *)
  | Tm_arrow {bs=b::more::bs; comp=c} ->
    let tail = S.mk (Tm_arrow {bs=more::bs; comp=c}) t.pos in
    let t = S.mk (Tm_arrow {bs=[b]; comp=S.mk_Total tail}) t.pos in
    embedding_for tcenv mutuals k env t

  | Tm_app _ ->
    let head, args = U.head_and_args t in
    let e_head = embedding_for tcenv mutuals k env head in
    let e_args = List.map (fun (t, _) -> embedding_for tcenv mutuals k env t) args in
    mk <| MLE_App (e_head, e_args)

  (* An fv part of the mutual set of inductives that we are making
  an embedding for, just point to the recursive binding. There is a catch
  though: we want to generate something like:

    let rec e_t1 = mk_emb ...
    and e_t2 = mk_emb ...
    ...

  but this does not satisfy OCamls's let-rec restrictions. Hence, we thunk
  all of them, using a name prefix __knot_e, and later define the e_X at the
  top-level by unthunking.
  *)
  | Tm_fvar fv when List.existsb (Ident.lid_equals fv.fv_name.v) mutuals ->
    let head = mk <| MLE_Var ("__knot_e_" ^ Ident.string_of_id (Ident.ident_of_lid fv.fv_name.v)) in
    mk (MLE_App (head, [ml_unit]))

  (* An fv for which we have an embedding already registered. *)
  | Tm_fvar fv when Some? (find_fv_embedding' fv.fv_name.v) ->
    let emb_data = find_fv_embedding fv.fv_name.v in
    begin match k with
    | SyntaxTerm -> ml_name emb_data.syn_emb
    | NBETerm ->
      begin match emb_data.nbe_emb with
      | Some lid -> ml_name lid
      | None ->
        ml_nbe_unsupported
      end
    end

  (*
   * An fv which we do not have registered, but has the plugin
   * attribute. We assume it must have had an embedding generated
   * right next to it in its same module.
   *)
  | Tm_fvar fv when Env.fv_has_attr tcenv fv PC.plugin_attr ->
    begin match k with
    | SyntaxTerm ->
      let lid = fv.fv_name.v in
      as_name (List.map Ident.string_of_id (Ident.ns_of_lid lid),
               "e_" ^ Ident.string_of_id (Ident.ident_of_lid lid))
    | NBETerm ->
      ml_nbe_unsupported
    end

  (* An fv which we do not have registered, and did not unfold *)
  | Tm_fvar fv ->
    raise (NoEmbedding (BU.format1 "Embedding not defined for name `%s'" (show t)))

  | _ ->
    raise (NoEmbedding (BU.format2 "Cannot embed type `%s' (%s)" (show t) (tag_of t)))

type wrapped_term = mlexpr & mlexpr & int & bool

let interpret_plugin_as_term_fun (env:UEnv.uenv) (fv:fv) (t:typ) (arity_opt:option int) (ml_fv:mlexpr')
    : option wrapped_term =
    let fv_lid = fv.fv_name.v in
    let tcenv = UEnv.tcenv_of_uenv env in
    let t = N.normalize [
      Env.EraseUniverses;
      Env.AllowUnboundUniverses;
      Env.UnfoldUntil S.delta_constant; // unfold abbreviations such as nat
      Env.ForExtraction
    ] tcenv t in
    let as_name mlp       = with_ty MLTY_Top <| MLE_Name mlp in
    let lid_to_name l     = with_ty MLTY_Top <| MLE_Name (UEnv.mlpath_of_lident env l) in
    let str_to_name s     = as_name ([], s) in
    let fv_lid_embedded =
        with_ty MLTY_Top <|
            MLE_App (as_name (["Fstar_guts.FStarC_Ident"],"lid_of_str"),
                     [with_ty MLTY_Top <| MLE_Const (MLC_String (Ident.string_of_lid fv_lid))])
    in
    let mk_tactic_interpretation l arity =
      if arity > FStarC.Tactics.InterpFuns.max_tac_arity then
        raise (NoEmbedding("tactic plugins can only take up to 20 arguments"))
      else
      let idroot =
        match l with
        | SyntaxTerm -> "mk_tactic_interpretation_"
        | NBETerm    -> "mk_nbe_tactic_interpretation_"
      in
      as_name (["Fstar_guts.FStarC_Tactics_InterpFuns"], idroot^string_of_int arity)
    in
    let mk_from_tactic l arity =
      let idroot =
        match l with
        | SyntaxTerm -> "from_tactic_"
        | NBETerm    -> "from_nbe_tactic_"
      in
      as_name (["Fstar_guts.FStarC_Tactics_Native"], idroot^string_of_int arity)
    in
    let mk_arrow_as_prim_step k (arity: int) : mlexpr =
      let modul =
        match k with
        | SyntaxTerm -> ["Fstar_guts.FStarC"; "Syntax"; "Embeddings"]
        | NBETerm    -> ["Fstar_guts.FStarC"; "TypeChecker"; "NBETerm"]
      in
      as_name (modul, "arrow_as_prim_step_" ^ string_of_int arity)
    in
    (*  Generates the ML syntax of a term of type
           `FStarC.Syntax.Embeddings.embedding [[t]]`
        where [[t]] is the ML denotation of the F* type t
    *)
    (* abstract_tvars:
         body is an implicitly polymorphic function over tvar_names
        whose type is of the form `args -> term`

       returns an mlexpr that explicitly abstracts over FStarC.Syntax.term
               representations of those type arguments
               peeling away a prefix of args corresponding to the type arguments
     *)
    let abstract_tvars tvar_names (body:mlexpr) : mlexpr =
        match tvar_names with
        | [] ->
          let body =
              mk <| MLE_App(as_name (["Fstar_guts.FStarC_Syntax_Embeddings"], "debug_wrap"),
                            [with_ty MLTY_Top <| MLE_Const (MLC_String (Ident.string_of_lid fv_lid));
                             ml_lam "_" (mk <| MLE_App(body, [str_to_name "args"]))])
          in
          ml_lam "args" body
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
             mk <| MLE_App(body, [as_name ([], "args_tail")])
          in
          let default_branch =
              MLP_Wild,
              None,
              mk <| MLE_App(str_to_name "failwith",
                            [mk <| MLE_Const (MLC_String "arity mismatch")])
          in
          let body =
              mk <| MLE_Match(as_name ([], "args"), [branch; default_branch])
          in
          let body =
              mk <| MLE_App(as_name (["Fstar_guts.FStarC_Syntax_Embeddings"], "debug_wrap"),
                            [with_ty MLTY_Top <| MLE_Const (MLC_String (Ident.string_of_lid fv_lid));
                             ml_lam "_" body])
          in
          ml_lam "args" body
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
               let c = S.mk_Total <| U.arrow rest c in
               bs, c
          else // n > bs
               let msg =
                BU.format3
                    "Embedding not defined for %s; expected arity at least %s; got %s"
                    (Ident.string_of_lid fv_lid)
                    (BU.string_of_int n)
                    (BU.string_of_int n_bs) in
               raise (NoEmbedding msg)
    in
    let result_typ = U.comp_result c in
    let arity = List.length bs in
    let type_vars, bs =
        match
            BU.prefix_until
                (fun ({binder_bv=b}) ->
                    match (SS.compress b.sort).n with
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
    let tvar_context : list (bv & string) = List.map2 (fun b nm -> b.binder_bv, nm) type_vars tvar_names in
    // The tvar_context records all the ML type variables in scope
    // All their embeddings will be just identity embeddings

    (* aux: The main function that builds the registration code

        accum_embeddings: all the embeddings of the arguments (in reverse order)
        bs: the remaining arguments

        returns (mlexpr, //the registration code
                 int,    //the arity of the compiled code (+1 for tactics)
                 bool)   //true if this is a tactic
    *)
    let rec aux loc (accum_embeddings:list mlexpr) bs : (mlexpr & int & bool) =
        match bs with
        | [] ->
          let arg_unembeddings = List.rev accum_embeddings in
          let res_embedding = embedding_for tcenv [] loc tvar_context result_typ in
          let fv_lid = fv.fv_name.v in
          if U.is_pure_comp c
          then begin
            let cb = str_to_name "cb" in
            let us = str_to_name "us" in
            let embed_fun_N = mk_arrow_as_prim_step loc non_tvar_arity in
            let args = arg_unembeddings
                    @ [res_embedding;
                       lid_to_name fv_lid;
                       fv_lid_embedded;
                       cb;
                       us]
            in
            let fun_embedding = mk <| MLE_App(embed_fun_N, args) in
            let tabs = abstract_tvars tvar_names fun_embedding in
            let cb_tabs = ml_lam "cb" (ml_lam "us" tabs) in
            ((if loc = NBETerm then cb_tabs else ml_lam "_psc" cb_tabs),
             arity,
             true)
          end
          else if Ident.lid_equals (FStarC.TypeChecker.Env.norm_eff_name tcenv (U.comp_effect_name c))
                                    PC.effect_TAC_lid
          then begin
            let h = mk_tactic_interpretation loc non_tvar_arity in
            let tac_fun = mk <| MLE_App (mk_from_tactic loc non_tvar_arity,
                                      [lid_to_name fv_lid])
            in
            let psc = str_to_name "psc" in
            let ncb = str_to_name "ncb" in
            let us = str_to_name "us" in
            let all_args = str_to_name "args" in
            let args =
                [mk <| MLE_Const (MLC_String (Ident.string_of_lid fv_lid ^ " (plugin)"))] @
                [tac_fun] @
                arg_unembeddings @
                [res_embedding;
                 psc;
                 ncb;
                 us] in
            let tabs =
              match tvar_names with
              | [] -> ml_lam "args" (mk <| MLE_App (h, args@[all_args]))
              | _ -> abstract_tvars tvar_names (mk <| MLE_App (h, args))
            in
            (ml_lam "psc" (ml_lam "ncb" (ml_lam "us" tabs)),
             arity + 1,
             false)
          end
          else raise (NoEmbedding("Plugins not defined for type " ^ show t))

        | ({binder_bv=b})::bs ->
          aux loc (embedding_for tcenv [] loc tvar_context b.sort::accum_embeddings) bs
    in
    try
        let w, a, b = aux SyntaxTerm [] bs in
        let w', _, _ = aux NBETerm [] bs in
        Some (w, w', a, b)
    with
    | NoEmbedding msg ->
      not_implemented_warning (Ident.range_of_lid fv.fv_name.v)
                              (show fv)
                              msg;
      None

(* Creates an unembedding function for the type *)
let mk_unembed
    (tcenv:Env.env)                           // tc environment mostly used to lookup fvs
    (mutuals : list Ident.lid)                // mutual inductives we are defining embedding for
    (record_fields : option (list mlpath))    // if this type is a record, these are the (extracted) field names
    (ctors: list sigelt)                      // constructors of the inductive
: mlexpr
= let e_branches : ref (list mlbranch) = BU.mk_ref [] in
  let arg_v = fresh "tm" in
  ctors |> List.iter (fun ctor ->
    match ctor.sigel with
    | Sig_datacon {lid; us; t; ty_lid; num_ty_params; mutuals=_} ->
      let fv = fresh "fv" in
      let bs, c = U.arrow_formals t in
      let vs = List.map (fun b -> fresh (Ident.string_of_id b.binder_bv.ppname), b.binder_bv.sort) bs in

      let pat_s = MLP_Const (MLC_String (Ident.string_of_lid lid)) in
      (* let pat_args = MLP_CTor ((["Prims"], "Nil"), List.map (fun (v, _) -> MLP_Var v) vs) in *)
      let pat_args = vs |> List.map (fun (v,_) -> MLP_Var v) |> pats_to_list_pat in
      let pat_both = MLP_Tuple [pat_s; pat_args] in

      let ret =
        match record_fields with
        | Some fields ->
          ml_record lid (List.map2 (fun (v, _) fld -> snd fld, mk (MLE_Var v)) vs fields)
        | None ->
          ml_ctor lid (List.map (fun (v, _) -> mk (MLE_Var v)) vs)
      in
      let ret = mk (MLE_App (ml_some, [ret])) in // final return

      let body = List.fold_right (fun (v, ty) body ->
        let body = mk (MLE_Fun ([mk_binder v MLTY_Top], body)) in

        mk (MLE_App (bind_opt, [
                      mk (MLE_App (unembed, [embedding_for tcenv mutuals SyntaxTerm [] ty; mk (MLE_Var v)]));
                      body;
                      ]))
      ) vs ret
      in
      let br = (pat_both, None, body) in

      e_branches := br :: !e_branches
    | _ -> failwith "impossible, filter above"
  );
  let nomatch : mlbranch = (MLP_Wild, None, ml_none) in
  let branches = List.rev (nomatch :: !e_branches) in
  let sc = mk (MLE_Var arg_v) in
  let def = mk (MLE_Match (sc, branches)) in
  let lam = mk (MLE_Fun ([mk_binder arg_v MLTY_Top], def)) in
  lam

(* Creates an embedding function for the type *)
let mk_embed
    (tcenv:Env.env)                           // tc environment mostly used to lookup fvs
    (mutuals : list Ident.lid)                // mutual inductives we are defining embedding for
    (record_fields : option (list mlpath))    // if this type is a record, these are the (extracted) field names
    (ctors: list sigelt)                      // constructors of the inductive
: mlexpr
= let e_branches : ref (list mlbranch) = BU.mk_ref [] in
  let arg_v = fresh "tm" in
  ctors |> List.iter (fun ctor ->
    match ctor.sigel with
    | Sig_datacon {lid; us; t; ty_lid; num_ty_params; mutuals=_} ->
      let fv = fresh "fv" in
      let bs, c = U.arrow_formals t in
      let vs = List.map (fun b -> fresh (Ident.string_of_id b.binder_bv.ppname), b.binder_bv.sort) bs in
      let pat =
        match record_fields with
        | Some fields ->
          // [] -> assuming same module
          MLP_Record ([], List.map2 (fun v fld -> snd fld, MLP_Var (fst v)) vs fields)
        | None ->
          MLP_CTor (splitlast (Ident.path_of_lid lid), List.map (fun v -> MLP_Var (fst v)) vs)
      in
      let fvar = s_tdataconstr in
      let lid_of_str = lid_of_str in
      let head = mk (MLE_App (fvar, [
                    mk (MLE_App (lid_of_str, [mk (MLE_Const (MLC_String (Ident.string_of_lid lid)))]))]))
      in
      let mk_mk_app t ts =
        // FIXME: all explicit
        let ts = List.map (fun t -> mk (MLE_Tuple [t; ml_none])) ts in
        mk (MLE_App (mk_app, [t; as_ml_list ts]))
      in
      let args =
        vs |> List.map (fun (v, ty) ->
          let vt = mk (MLE_Var v) in
          mk (MLE_App (embed, [embedding_for tcenv mutuals SyntaxTerm [] ty; vt]))
        )
      in
      let ret = mk_mk_app head args in
      let br = (pat, None, ret) in

      e_branches := br :: !e_branches
    | _ -> failwith "impossible, filter above"
  );
  let branches = List.rev !e_branches in
  let sc = mk (MLE_Var arg_v) in
  let def = mk (MLE_Match (sc, branches)) in
  let lam = mk (MLE_Fun ([mk_binder arg_v MLTY_Top], def)) in
  lam


let __do_handle_plugin (g: uenv) (arity_opt: option int) (se: sigelt) : list mlmodule1 =
  // BU.print2 "Got plugin with attrs = %s; arity_opt=%s"
  //          (List.map show se.sigattrs |> String.concat " ")
  //          (match arity_opt with None -> "None" | Some x -> "Some " ^ string_of_int x);
  let r = se.sigrng in
  match se.sigel with
  | Sig_let {lbs} ->
      let mk_registration lb : list mlmodule1 =
         let fv = BU.right lb.lbname in
         let fv_lid = fv.fv_name.v in
         let fv_t = lb.lbtyp in
         let ml_name_str = MLE_Const (MLC_String (Ident.string_of_lid fv_lid)) in
         match interpret_plugin_as_term_fun g fv fv_t arity_opt ml_name_str with
         | Some (interp, nbe_interp, arity, plugin) ->
             let register, args =
               if plugin
               then (["Fstar_guts.FStarC_Tactics_Native"], "register_plugin"), [interp; nbe_interp]
               else (["Fstar_guts.FStarC_Tactics_Native"], "register_tactic"), [interp]
             in
             let h = with_ty MLTY_Top <| MLE_Name register in
             let arity  = MLE_Const (MLC_Int(string_of_int arity, None)) in
             let app = with_ty MLTY_Top <| MLE_App (h, [mk ml_name_str; mk arity] @ args) in
             [MLM_Top app |> mk_mlmodule1]
         | None -> []
      in
      List.collect mk_registration (snd lbs)

  | Sig_bundle {ses} ->
    let mutual_sigelts = List.filter (fun se -> match se.sigel with | Sig_inductive_typ _ -> true | _ -> false) ses in
    let mutual_lids = List.map (fun se -> match se.sigel with | Sig_inductive_typ {lid} -> lid ) mutual_sigelts in
    let proc_one (typ_sigelt:sigelt) =
      let Sig_inductive_typ {lid=tlid; params=ps} = typ_sigelt.sigel in
      if List.length ps > 0 then
        raise (Unsupported "parameters on inductive");
      let ns = Ident.ns_of_lid tlid in
      let name = Ident.string_of_id (List.last (Ident.ids_of_lid tlid)) in

      (* get constructors for this particular mutual *)
      let ctors =
        List.filter (fun se -> match se.sigel with | Sig_datacon {ty_lid} -> Ident.lid_equals ty_lid tlid | _ -> false) ses
      in
      let ml_name = mk (MLE_Const (MLC_String (Ident.string_of_lid tlid))) in

      let record_fields =
        match List.find (function RecordType _ -> true | _ -> false) typ_sigelt.sigquals with
        | Some (RecordType (_, b)) ->
          (* Extraction may change the names of fields to disambiguate them,
           * query the environment for the extracted names. *)
          Some (List.map (fun f -> lookup_record_field_name g (tlid, f)) b)
        | _ ->
          None
      in

      let tcenv = tcenv_of_uenv g in
      let ml_unembed = mk_unembed tcenv mutual_lids record_fields ctors in
      let ml_embed   = mk_embed   tcenv mutual_lids record_fields ctors in
      let def = mk (MLE_App (mk (MLE_Name (["Fstar_guts.FStarC"; "Syntax"; "Embeddings"; "Base"], "mk_extracted_embedding")), [
                      ml_name;
                      ml_unembed;
                      ml_embed]))
      in
      let def = mk (MLE_Fun ([mk_binder "_" MLTY_Erased], def)) in // thunk
      let lb = {
        mllb_name     = "__knot_e_" ^ name;
        mllb_tysc     = None;
        mllb_add_unit = false;
        mllb_def      = def;
        mllb_meta     = [];
        mllb_attrs    = [];
        print_typ     = false;
      }
      in
      // TODO: parameters
      register_embedding tlid {
        arity   = 0;
        syn_emb = Ident.lid_of_ns_and_id ns (Ident.mk_ident ("e_"^name, Range.dummyRange));
        nbe_emb = None;
      };
      [lb]
    in
    let lbs = List.concatMap proc_one mutual_sigelts in
    let unthunking : list mlmodule1 =
      mutual_sigelts |> List.concatMap (fun se ->
        let tlid = (match se.sigel with | Sig_inductive_typ {lid=tlid} -> tlid) in
        let name = Ident.string_of_id (List.last (Ident.ids_of_lid tlid)) in
        let app =
            let head = mk <| MLE_Var ("__knot_e_" ^ name) in
            mk (MLE_App (head, [ml_unit]))
        in
        let lb = {
          mllb_name     = "e_" ^ name;
          mllb_tysc     = None;
          mllb_add_unit = false;
          mllb_def      = app;
          mllb_meta     = [];
          mllb_attrs    = [];
          print_typ     = false;
        }
        in
        [MLM_Let (NonRec, [lb]) |> mk_mlmodule1]
      )
    in
    // TODO: We always make a let rec, we could check if that's really needed.
    [MLM_Let (Rec, lbs) |> mk_mlmodule1] @ unthunking

  | _ -> []

let do_handle_plugin (g: uenv) (arity_opt: option int) (se: sigelt) : list mlmodule1 =
  try __do_handle_plugin g arity_opt se with
  | Unsupported msg ->
    // Change error code?
    Errors.log_issue se Errors.Warning_PluginNotImplemented
      (BU.format2 "Could not generate a plugin for %s, reason = %s" (Print.sigelt_to_string_short se) msg);
    []
  | NoEmbedding msg ->
    not_implemented_warning se.sigrng
                            (Print.sigelt_to_string_short se)
                            msg;
    []

(* When extracting a plugin, each top-level definition marked with a `@plugin` attribute
   is extracted along with an invocation to FStarC.Tactics.Native.register_tactic or register_plugin,
   which installs the compiled term as a primitive step in the normalizer
 *)
let maybe_register_plugin (g:uenv) (se:sigelt) : list mlmodule1 =
  (* The `plugin` attribute takes an optional arity, parse it.
   *   None:          not a plugin
   *   Some None:     plugin without explicit arity
   *   Some (Some n): plugin with explicit arity n
   *)
  let plugin_with_arity (attrs: list term) : option (option int) =
    BU.find_map attrs (fun t ->
      let head, args = U.head_and_args t in
      if not (U.is_fvar PC.plugin_attr head) then
        None
      else match args with
      | [(a, _)] ->
         (* Try to unembed the argument as an int, warn if not possible. *)
         let nopt = EMB.unembed a EMB.id_norm_cb in
         Some nopt
      | _ -> Some None
    )
  in
  if not <| List.mem (Options.codegen()) [Some Options.Plugin; Some Options.PluginNoLib]
  then
    []
  else
    match plugin_with_arity se.sigattrs with
    | None -> []
    (* ignore projectors and discriminators, they get a @@plugin attribute inherited
    from the type, but we should not do anything for them. *)
    | Some _ when List.existsb (function Projector _ | Discriminator _ -> true | _ -> false) se.sigquals ->
      []
    | Some arity_opt ->
      do_handle_plugin g arity_opt se
