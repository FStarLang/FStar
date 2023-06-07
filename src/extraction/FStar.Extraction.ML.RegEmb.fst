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
module FStar.Extraction.ML.RegEmb

(* This module handles registering plugins and generating
embeddings for their types. *)

open FStar
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.Const
open FStar.Extraction.ML.Syntax
open FStar.Extraction.ML.UEnv
open FStar.Syntax.Syntax

module BU    = FStar.Compiler.Util
module Code  = FStar.Extraction.ML.Code
module EMB   = FStar.Syntax.Embeddings
module Env   = FStar.TypeChecker.Env
module N     = FStar.TypeChecker.Normalize
module PC    = FStar.Parser.Const
module Print = FStar.Syntax.Print
module S     = FStar.Syntax.Syntax
module SS    = FStar.Syntax.Subst
module Term  = FStar.Extraction.ML.Term
module U     = FStar.Syntax.Util
module Util  = FStar.Extraction.ML.Util

exception Unsupported of string

let splitlast s = let x::xs = List.rev s in (List.rev xs, x)

let mk e = with_ty MLTY_Top e

let ml_name : Ident.lid -> mlexpr =
  fun l ->
    let s = Ident.path_of_lid l in
    let ns, id = splitlast s in
    mk (MLE_Name (ns, id))
let ml_ctor : Ident.lid -> list mlexpr -> mlexpr =
  fun l args ->
    let s = Ident.path_of_lid l in
    let ns, id = splitlast s in
    mk (MLE_CTor ((ns, id), args))

let ml_none : mlexpr = mk (MLE_Name (["FStar"; "Pervasives"; "Native"], "None"))
let ml_some : mlexpr = mk (MLE_Name (["FStar"; "Pervasives"; "Native"], "Some"))

let tm_fvar_lid    = Ident.lid_of_str "FStar.Syntax.Syntax.Tm_fvar"
let fv_eq_lid_lid  = Ident.lid_of_str "FStar.Syntax.Syntax.fv_eq_lid"
let s_fvar_lid     = Ident.lid_of_str "FStar.Syntax.Syntax.fvar"
let lid_of_str_lid = Ident.lid_of_str "FStar.Ident.lid_of_str" // :^)
let mk_app_lid     = Ident.lid_of_str "FStar.Syntax.Util.mk_app"
let nil_lid        = Ident.lid_of_str "Prims.Nil"
let cons_lid       = Ident.lid_of_str "Prims.Cons"
let embed_lid      = Ident.lid_of_str "FStar.Syntax.Embeddings.Base.extracted_embed"
let unembed_lid    = Ident.lid_of_str "FStar.Syntax.Embeddings.Base.extracted_unembed"
let bind_opt_lid   = Ident.lid_of_str "FStar.Compiler.Util.bind_opt"

let ml_magic : mlexpr =
  mk (MLE_Coerce (ml_unit, MLTY_Top, MLTY_Top))

let embedding_for (a:S.typ) : mlexpr =
  ml_magic

let rec as_ml_list (ts : list mlexpr) : mlexpr =
  match ts with
  | [] -> ml_ctor nil_lid []
  | t::ts -> ml_ctor cons_lid [t; as_ml_list ts]

let rec pats_to_list_pat (vs : list mlpattern) : mlpattern =
  match vs with
  | [] -> MLP_CTor ((["Prims"], "Nil"), [])
  | p::ps -> MLP_CTor ((["Prims"], "Cons"), [p; pats_to_list_pat ps])

let fresh : string -> string =
  let r = BU.mk_ref 0 in
  fun s ->
    let v = !r in
    r := v+1;
    s^"_"^(string_of_int v)

let mk_unembed (ctors: list sigelt) : mlexpr =
  let e_branches : ref (list mlbranch) = BU.mk_ref [] in
  let arg_v = fresh "tm" in
  ctors |> List.iter (fun ctor ->
    match ctor.sigel with
    | Sig_datacon {lid; us; t; ty_lid; num_ty_params; mutuals} ->
      let fv = fresh "fv" in
      let bs, c = U.arrow_formals t in
      let vs = List.map (fun b -> fresh (Ident.string_of_id b.binder_bv.ppname), b.binder_bv.sort) bs in

      let pat_s = MLP_Const (MLC_String (Ident.string_of_lid lid)) in
      (* let pat_args = MLP_CTor ((["Prims"], "Nil"), List.map (fun (v, _) -> MLP_Var v) vs) in *)
      let pat_args = vs |> List.map (fun (v,_) -> MLP_Var v) |> pats_to_list_pat in
      let pat_both = MLP_Tuple [pat_s; pat_args] in

      let head = ml_name lid in
      let ret = mk (MLE_App (head, [mk (MLE_Tuple (List.map (fun (v, _) -> mk (MLE_Var v)) vs))])) in
      let ret = mk (MLE_App (ml_some, [ret])) in // final return

      let body = List.fold_right (fun (v, ty) body ->
        let body = mk (MLE_Fun ([(v, MLTY_Top)], body)) in
        mk (MLE_App (ml_name bind_opt_lid, [
                      mk (MLE_App (ml_name unembed_lid, [embedding_for ty; mk (MLE_Var v)]));
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
  let lam = mk (MLE_Fun ([arg_v, MLTY_Top], def)) in
  lam

let mk_embed (ctors: list sigelt) : mlexpr =
  let e_branches : ref (list mlbranch) = BU.mk_ref [] in
  let arg_v = fresh "tm" in
  ctors |> List.iter (fun ctor ->
    match ctor.sigel with
    | Sig_datacon {lid; us; t; ty_lid; num_ty_params; mutuals} ->
      let fv = fresh "fv" in
      let bs, c = U.arrow_formals t in
      let vs = List.map (fun b -> fresh (Ident.string_of_id b.binder_bv.ppname), b.binder_bv.sort) bs in
      let pat = MLP_CTor (splitlast (Ident.path_of_lid lid), List.map (fun v -> MLP_Var (fst v)) vs) in
      let fvar = ml_name s_fvar_lid in
      let lid_of_str = ml_name lid_of_str_lid in
      let head = mk (MLE_App (fvar, [
                    mk (MLE_App (lid_of_str, [mk (MLE_Const (MLC_String (Ident.string_of_lid lid)))]));
                    ml_none]))
      in
      let mk_mk_app t ts =
        // FIXME: all explicit
        let ts = List.map (fun t -> mk (MLE_Tuple [t; ml_none])) ts in
        mk (MLE_App (ml_name mk_app_lid, [t; as_ml_list ts]))
      in
      let args =
        vs |> List.map (fun (v, ty) ->
          let vt = mk (MLE_Var v) in
          mk (MLE_App (ml_name embed_lid, [embedding_for ty; vt]))
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
  let lam = mk (MLE_Fun ([arg_v, MLTY_Top], def)) in
  lam

(* helper functions used to extract, alongside a tactic, its corresponding call
   to FStar.Tactics.Native.register_tactic *)
module RC = FStar.Reflection.Constants
module SEmb = FStar.Syntax.Embeddings
module REmb = FStar.Reflection.Embeddings

exception NoTacticEmbedding of string

let not_implemented_warning r t msg =
    Errors.log_issue r
        (Errors.Warning_PluginNotImplemented,
         BU.format3 "Plugin %s can not run natively because %s (use --warn_error -%s to carry on)."
                        t
                        msg
                        (string_of_int <| Errors.error_number (Errors.lookup Errors.Warning_PluginNotImplemented)))

type emb_loc =
    | Syntax_term (* FStar.Syntax.Embeddings *)
    | Refl_emb    (* FStar.Reflection.Embeddings *)
    | NBE_t       (* FStar.TypeChecker.NBETerm *)
    | NBERefl_emb (* FStar.Reflection.NBEEmbeddings *)

type embedding_data = {
  arity : int;
  syn_emb : Ident.lid; (* lid for regular embedding *)
  nbe_emb : option Ident.lid; (* nbe embedding, optional! will abort _at runtime_ if None and called *)
}

let known_embeddings : ref (list (Ident.lident * embedding_data)) =
  let syn_emb_lid s      = Ident.lid_of_path ["FStar"; "Syntax"; "Embeddings"; s] Range.dummyRange in
  let nbe_emb_lid s      = Ident.lid_of_path ["FStar"; "TypeChecker"; "NBETerm"; s] Range.dummyRange in
  let refl_emb_lid s     = Ident.lid_of_path ["FStar"; "Reflection"; "Embeddings"; s] Range.dummyRange in
  let nbe_refl_emb_lid s = Ident.lid_of_path ["FStar"; "Reflection"; "NBEEmbeddings"; s] Range.dummyRange in
  BU.mk_ref [
    (PC.int_lid,                          {arity=0; syn_emb=syn_emb_lid  "e_int";        nbe_emb=Some(nbe_emb_lid "e_int")});
    (PC.bool_lid,                         {arity=0; syn_emb=syn_emb_lid  "e_bool";       nbe_emb=Some(nbe_emb_lid "e_bool")});
    (PC.unit_lid,                         {arity=0; syn_emb=syn_emb_lid  "e_unit";       nbe_emb=Some(nbe_emb_lid "e_unit")});
    (PC.string_lid,                       {arity=0; syn_emb=syn_emb_lid  "e_string";     nbe_emb=Some(nbe_emb_lid "e_string")});
    (PC.norm_step_lid,                    {arity=0; syn_emb=syn_emb_lid  "e_norm_step";  nbe_emb=Some(nbe_emb_lid "e_norm_step")});

    (PC.list_lid,                         {arity=1; syn_emb=syn_emb_lid  "e_list";       nbe_emb=Some(nbe_emb_lid "e_list")});
    (PC.option_lid,                       {arity=1; syn_emb=syn_emb_lid  "e_option";     nbe_emb=Some(nbe_emb_lid "e_option")});
    (PC.sealed_lid,                       {arity=1; syn_emb=syn_emb_lid  "e_sealed";     nbe_emb=Some(nbe_emb_lid "e_sealed")});

    (PC.mk_tuple_lid 2 Range.dummyRange,  {arity=1; syn_emb=syn_emb_lid  "e_tuple2";     nbe_emb=Some(nbe_emb_lid "e_tuple2")});

    (RC.fstar_refl_types_lid "term",      {arity=0; syn_emb=refl_emb_lid "e_term";      nbe_emb=Some(nbe_refl_emb_lid "e_term")});
    (RC.fstar_refl_types_lid "fv",        {arity=0; syn_emb=refl_emb_lid "e_fv";        nbe_emb=Some(nbe_refl_emb_lid "e_fv")});
    (RC.fstar_refl_types_lid "sigelt",    {arity=0; syn_emb=refl_emb_lid "e_sigelt";    nbe_emb=Some(nbe_refl_emb_lid "e_sigelt")});
    (RC.fstar_refl_types_lid "env",       {arity=0; syn_emb=refl_emb_lid "e_env";       nbe_emb=Some(nbe_refl_emb_lid "e_env")});
    (RC.fstar_refl_types_lid "binders",   {arity=0; syn_emb=refl_emb_lid "e_binders";   nbe_emb=Some(nbe_refl_emb_lid "e_binders")});
    (RC.fstar_refl_types_lid "binder",    {arity=0; syn_emb=refl_emb_lid "e_binder";    nbe_emb=Some(nbe_refl_emb_lid "e_binder")});
    (RC.fstar_refl_types_lid "term",      {arity=0; syn_emb=refl_emb_lid "e_term";      nbe_emb=Some(nbe_refl_emb_lid "e_term")});
  ]

let register_embedding (l: Ident.lident) (d: embedding_data) : unit =
  known_embeddings := (l,d) :: !known_embeddings

let find_embedding' (l: Ident.lident) : option embedding_data =
  match List.find (fun (l', _) -> Ident.lid_equals l l') !known_embeddings with
  | Some (_, data) -> Some data
  | None -> None

let find_embedding (l: Ident.lident) : embedding_data =
  match find_embedding' l with
  | Some data -> data
  | None ->
    // TODO: rename to NoEmbedding
    raise (NoTacticEmbedding ("Embedding not defined for type " ^ Ident.string_of_lid l))

type wrapped_term = mlexpr * mlexpr * int * bool

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
    let w = with_ty MLTY_Top in
    let as_name mlp       = with_ty MLTY_Top <| MLE_Name mlp in
    let lid_to_name l     = with_ty MLTY_Top <| MLE_Name (UEnv.mlpath_of_lident env l) in
    let str_to_name s     = as_name ([], s) in
    let fstar_tc_nbe_prefix s = as_name (["FStar_TypeChecker_NBETerm"], s) in
    let fstar_syn_emb_prefix s = as_name (["FStar_Syntax_Embeddings"], s) in
    let fstar_refl_emb_prefix s = as_name (["FStar_Reflection_Embeddings"], s) in
    let fstar_refl_nbeemb_prefix s = as_name (["FStar_Reflection_NBEEmbeddings"], s) in
    let fv_lid_embedded =
        with_ty MLTY_Top <|
            MLE_App (as_name (["FStar_Ident"],"lid_of_str"),
                     [with_ty MLTY_Top <| MLE_Const (MLC_String (Ident.string_of_lid fv_lid))])
    in
    let emb_prefix = function
        | Syntax_term -> fstar_syn_emb_prefix
        | Refl_emb -> fstar_refl_emb_prefix
        | NBE_t -> fstar_tc_nbe_prefix
        | NBERefl_emb -> fstar_refl_nbeemb_prefix
    in
    let mk_tactic_interpretation l arity =
      if arity > FStar.Tactics.InterpFuns.max_tac_arity then
        raise (NoTacticEmbedding("tactic plugins can only take up to 20 arguments"))
      else
      let idroot =
        match l with
        | Syntax_term ->
          "mk_tactic_interpretation_"
        | _ ->
          "mk_nbe_tactic_interpretation_"
      in
      as_name (["FStar_Tactics_InterpFuns"], idroot^string_of_int arity)
    in
    let mk_from_tactic l arity =
      let idroot =
        match l with
        | Syntax_term -> "from_tactic_"
        | _ -> "from_nbe_tactic_"
      in
      as_name (["FStar_Tactics_Native"], idroot^string_of_int arity)
    in
    let mk_arrow_as_prim_step l (arity: int): mlexpr =
        emb_prefix l ("arrow_as_prim_step_" ^ string_of_int arity)
    in
    let mk_any_embedding l (s: string): mlexpr =
        w <| MLE_App(emb_prefix l "mk_any_emb", [str_to_name s])
    in
    let mk_lam nm e =
        w <| MLE_Fun ([(nm, MLTY_Top)], e)
    in
    let emb_arrow l e1 e2 =
        w <| MLE_App(emb_prefix l "e_arrow", [e1; e2])
    in
    let find_env_entry bv (bv', _) = S.bv_eq bv bv' in
    (*  Generates the ML syntax of a term of type
           `FStar.Syntax.Embeddings.embedding [[t]]`
        where [[t]] is the ML denotation of the F* type t
    *)
    let rec mk_embedding l (env:list (bv * string)) (t: term): mlexpr =
        let t = FStar.TypeChecker.Normalize.unfold_whnf' [Env.ForExtraction] tcenv t in
        match (FStar.Syntax.Subst.compress t).n with
        | Tm_name bv
             when BU.for_some (find_env_entry bv) env ->
          mk_any_embedding l <| snd (BU.must (BU.find_opt (find_env_entry bv) env))

        | Tm_refine {b=x} ->
          (* Refinements are irrelevant to generate embeddings. *)
          mk_embedding l env x.sort

        | Tm_ascribed {tm=t} ->
          mk_embedding l env t

        | Tm_arrow {bs=[b]; comp=c} when U.is_pure_comp c ->
          let bs, c = FStar.Syntax.Subst.open_comp [b] c in
          let t0 = (List.hd bs).binder_bv.sort in
          let t1 = U.comp_result c in
          emb_arrow l (mk_embedding l env t0) (mk_embedding l env t1)

        | Tm_arrow {bs=b::more::bs; comp=c} ->
          let tail = S.mk (Tm_arrow {bs=more::bs; comp=c}) t.pos in
          let t = S.mk (Tm_arrow {bs=[b]; comp=S.mk_Total tail}) t.pos in
          mk_embedding l env t

        | Tm_fvar _
        | Tm_uinst _
        | Tm_app _ ->
          let head, args = U.head_and_args t in
          let n_args = List.length args in
          begin
          match (U.un_uinst head).n with
          | Tm_fvar fv when Some? (find_embedding' fv.fv_name.v) ->
            let arg_embeddings =
                args
                |> List.map (fun (t, _) -> mk_embedding l env t)
            in
            let emb_data = find_embedding fv.fv_name.v in
            let t_arity = emb_data.arity in
            let head =
              match l with
              | Syntax_term -> ml_name emb_data.syn_emb
              | NBE_t ->
                begin match emb_data.nbe_emb with
                | Some lid -> ml_name lid
                | None -> ml_magic // FIXME: something better please
                end
              | _ -> failwith "blah"
            in
            if t_arity = 0
            then head
            else w <| MLE_App (head, arg_embeddings)

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
              w <| MLE_App(as_name (["FStar_Syntax_Embeddings"], "debug_wrap"),
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
             w <| MLE_App(body, [as_name ([], "args")])
          in
          let default_branch =
              MLP_Wild,
              None,
              w <| MLE_App(str_to_name "failwith",
                            [w <| MLE_Const (MLC_String "arity mismatch")])
          in
          let body =
              w <| MLE_Match(as_name ([], "args"), [branch; default_branch])
          in
          let body =
              w <| MLE_App(as_name (["FStar_Syntax_Embeddings"], "debug_wrap"),
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
    let tvar_context : list (bv * string) = List.map2 (fun b nm -> b.binder_bv, nm) type_vars tvar_names in
    // The tvar_context records all the ML type variables in scope
    // All their embeddings will be just identity embeddings

    (* aux: The main function that builds the registration code

        accum_embeddings: all the embeddings of the arguments (in reverse order)
        bs: the remaining arguments

        returns (mlexpr, //the registration code
                 int,    //the arity of the compiled code (+1 for tactics)
                 bool)   //true if this is a tactic
    *)
    let rec aux loc (accum_embeddings:list mlexpr) bs : (mlexpr * int * bool) =
        match bs with
        | [] ->
          let arg_unembeddings = List.rev accum_embeddings in
          let res_embedding = mk_embedding loc tvar_context result_typ in
          let fv_lid = fv.fv_name.v in
          if U.is_pure_comp c
          then begin
            let cb = str_to_name "cb" in
            let embed_fun_N = mk_arrow_as_prim_step loc non_tvar_arity in
            let args = arg_unembeddings
                    @ [res_embedding;
                       lid_to_name fv_lid;
                       with_ty MLTY_Top <| MLE_Const (MLC_Int(string_of_int tvar_arity, None));
                       fv_lid_embedded;
                       cb]
            in
            let fun_embedding = w <| MLE_App(embed_fun_N, args) in
            let tabs = abstract_tvars tvar_names fun_embedding in
            let cb_tabs = mk_lam "cb" tabs in
            ((if loc = NBE_t then cb_tabs else mk_lam "_psc" cb_tabs),
             arity,
             true)
          end
          else if Ident.lid_equals (FStar.TypeChecker.Env.norm_eff_name tcenv (U.comp_effect_name c))
                                    PC.effect_TAC_lid
          then begin
            let h = mk_tactic_interpretation loc non_tvar_arity in
            let tac_fun = w <| MLE_App (mk_from_tactic loc non_tvar_arity,
                                      [lid_to_name fv_lid])
            in
            let psc = str_to_name "psc" in
            let ncb = str_to_name "ncb" in
            let all_args = str_to_name "args" in
            let args =
                [tac_fun] @
                arg_unembeddings @
                [res_embedding;
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

        | ({binder_bv=b})::bs ->
          aux loc (mk_embedding loc tvar_context b.sort::accum_embeddings) bs
    in
    try
        let w, a, b = aux Syntax_term [] bs in
        let w', _, _ = aux NBE_t [] bs in
        Some (w, w', a, b)
    with
    | NoTacticEmbedding msg ->
      not_implemented_warning (Ident.range_of_lid fv.fv_name.v)
                              (FStar.Syntax.Print.fv_to_string fv)
                              msg;
      None


















let __do_handle_plugin (g: uenv) (arity_opt: option int) (se: sigelt) : list mlmodule1 =
  // BU.print2 "Got plugin with attrs = %s; arity_opt=%s"
  //          (List.map Print.term_to_string se.sigattrs |> String.concat " ")
  //          (match arity_opt with None -> "None" | Some x -> "Some " ^ string_of_int x);
  let w = with_ty MLTY_Top in
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
               then (["FStar_Tactics_Native"], "register_plugin"), [interp; nbe_interp]
               else (["FStar_Tactics_Native"], "register_tactic"), [interp]
             in
             let h = with_ty MLTY_Top <| MLE_Name register in
             let arity  = MLE_Const (MLC_Int(string_of_int arity, None)) in
             let app = with_ty MLTY_Top <| MLE_App (h, [w ml_name_str; w arity] @ args) in
             [MLM_Top app]
         | None -> []
      in
      List.collect mk_registration (snd lbs)

  | Sig_bundle {ses} ->
    let typ_sigelt =
      match List.filter (fun se -> match se.sigel with | Sig_inductive_typ _ -> true | _ -> false) ses with
      | [se] -> se
      | _ -> raise (Unsupported "mutual inductives")
    in
    let Sig_inductive_typ {lid=tlid; params=ps} = typ_sigelt.sigel in
    if List.length ps > 0 then
      raise (Unsupported "parameters on inductive");
    let ns = Ident.ns_of_lid tlid in
    let name = Ident.string_of_id (List.last (Ident.ids_of_lid tlid)) in

    let ctors = List.filter (fun se -> match se.sigel with | Sig_datacon _ -> true | _ -> false) ses in
    let ml_name = mk (MLE_Const (MLC_String (Ident.string_of_lid tlid))) in
    let ml_unembed = mk_unembed ctors in
    let ml_embed = mk_embed ctors in
    let def = mk (MLE_App (mk (MLE_Name (["FStar"; "Syntax"; "Embeddings"; "Base"], "mk_extracted_embedding")), [
                    ml_name;
                    ml_unembed;
                    ml_embed]))
    in
    let lb = {
      mllb_name     = "e_" ^ name;
      mllb_tysc     = None;
      mllb_add_unit = false;
      mllb_def      = def;
      mllb_meta     = [];
      print_typ     = false;
    }
    in
    // TODO: parameters
    register_embedding tlid {
      arity   = 0;
      syn_emb = Ident.lid_of_ns_and_id ns (Ident.mk_ident ("e_"^name, Range.dummyRange));
      nbe_emb = None;
    };
    [MLM_Let (NonRec, [lb])]

  | _ -> []

let do_handle_plugin (g: uenv) (arity_opt: option int) (se: sigelt) : list mlmodule1 =
  try __do_handle_plugin g arity_opt se with
  | Unsupported msg ->
    // FIXME: Change error code
    Errors.log_issue se.sigrng (Errors.Warning_PluginNotImplemented,
        BU.format2 "Could not generate a plugin for %s, reason = %s" (Print.sigelt_to_string_short se) msg);
    []

(* When extracting a plugin, each top-level definition marked with a `@plugin` attribute
   is extracted along with an invocation to FStar.Tactics.Native.register_tactic or register_plugin,
   which installs the compiled term as a primitive step in the normalizer
 *)
let maybe_register_plugin (g:uenv) (se:sigelt) : list mlmodule1 =
    let plugin_with_arity attrs =
        BU.find_map attrs (fun t ->
              let head, args = U.head_and_args t in
              if not (U.is_fvar PC.plugin_attr head)
              then None
              else match args with
                   | [({n=Tm_constant (Const_int(s, _))}, _)] ->
                     Some (Some (BU.int_of_string s))
                   | _ -> Some None)
    in
    if Options.codegen() <> Some Options.Plugin
    then []
    else
      match plugin_with_arity se.sigattrs with
      | None -> []
      (* ignore projectors and discriminators, they get a @@plugin attribute inherited
      from the type, but we don't need to handle them. *)
      | Some _ when List.existsb (function Projector _ | Discriminator _ -> true | _ -> false) se.sigquals ->
        []
      | Some arity_opt ->
        do_handle_plugin g arity_opt se


