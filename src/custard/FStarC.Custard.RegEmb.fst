(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.Custard.RegEmb

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Custard.Syntax
open FStarC.Syntax.Syntax
open FStarC.Const

module BU      = FStarC.Util
module CSyn    = FStarC.Custard.Syntax
module E       = FStarC.Errors
module Extract = FStarC.Custard.Extract
module Ident   = FStarC.Ident
module N       = FStarC.TypeChecker.Normalize
module PC      = FStarC.Parser.Const
module RC      = FStarC.Reflection.V2.Constants
module S       = FStarC.Syntax.Syntax
module SMap    = FStarC.SMap
module SS      = FStarC.Syntax.Subst
module TcEnv   = FStarC.TypeChecker.Env
module U       = FStarC.Syntax.Util

open FStarC.Class.Show
open FStarC.Syntax.Print

(* Raised when some part of the plugin's type has no embedding.  It is not an
   error: the definition is still compiled, it just cannot be *called* by the
   normalizer, so the tactic runs interpreted instead of natively.  That is
   exactly what the ML pipeline does, and the warning is the same one. *)
exception NoEmbedding of string

let warn_not_implemented (r:Range.t) (what:string) (msg:string) : ML unit =
  let open FStarC.Pprint in
  let open FStarC.Errors.Msg in
  let open FStarC.Class.PP in
  E.log_issue r E.Warning_PluginNotImplemented [
    prefix 2 1 (text (Format.fmt1 "Plugin `%s' can not run natively because:" what))
      (text msg);
    text "Use --warn_error -"
      ^^ pp (E.error_number (E.lookup E.Warning_PluginNotImplemented))
      ^/^ text "to carry on."
  ]

(* -------------------------------------------------------------------- *)
(* The embeddings that already exist                                    *)
(* -------------------------------------------------------------------- *)

(* Deliberately a copy of {!FStarC.Extraction.ML.RegEmb.builtin_embeddings}
   rather than a reference to it: the two pipelines are kept independent of
   each other (see the header of {!FStarC.Custard.Syntax}), and this is a
   table of names, not logic.  The names themselves are checked by the build
   -- a typo here is an unbound identifier in the generated OCaml. *)
type embedding_data = {
  arity   : int;
  syn_emb : Ident.lident;
  nbe_emb : option Ident.lident;
}

let builtin_embeddings : list (Ident.lident & embedding_data) =
  let syn s      = Ident.lid_of_path ["FStarC"; "Syntax"; "Embeddings"; s] Range.dummyRange in
  let nbe s      = Ident.lid_of_path ["FStarC"; "TypeChecker"; "NBETerm"; s] Range.dummyRange in
  let refl s     = Ident.lid_of_path ["FStarC"; "Reflection"; "V2"; "Embeddings"; s] Range.dummyRange in
  let nbe_refl s = Ident.lid_of_path ["FStarC"; "Reflection"; "V2"; "NBEEmbeddings"; s] Range.dummyRange in
  let base n s = { arity = n; syn_emb = syn s; nbe_emb = Some (nbe s) } in
  let rfl s    = { arity = 0; syn_emb = refl s; nbe_emb = Some (nbe_refl s) } in
  [
    (PC.int_lid,        base 0 "e_int");
    (PC.bool_lid,       base 0 "e_bool");
    (PC.unit_lid,       base 0 "e_unit");
    (PC.string_lid,     base 0 "e_string");
    (PC.norm_step_lid,  base 0 "e_norm_step");
    (PC.range_lid,      base 0 "e_range");
    (PC.vconfig_lid,    base 0 "e_vconfig");

    (PC.list_lid,       base 1 "e_list");
    (PC.option_lid,     base 1 "e_option");
    (PC.sealed_lid,     base 1 "e_sealed");

    (PC.mk_tuple_lid 2 Range.dummyRange, base 2 "e_tuple2");
    (PC.mk_tuple_lid 3 Range.dummyRange, base 3 "e_tuple3");
    (PC.either_lid,     base 2 "e_either");

    (RC.fstar_refl_types_lid "namedv",             rfl "e_namedv");
    (RC.fstar_refl_types_lid "bv",                 rfl "e_bv");
    (RC.fstar_refl_types_lid "binder",             rfl "e_binder");
    (RC.fstar_refl_types_lid "term",               rfl "e_term");
    (RC.fstar_refl_types_lid "env",                rfl "e_env");
    (RC.fstar_refl_types_lid "fv",                 rfl "e_fv");
    (RC.fstar_refl_types_lid "comp",               rfl "e_comp");
    (RC.fstar_refl_types_lid "sigelt",             rfl "e_sigelt");
    (RC.fstar_refl_types_lid "ctx_uvar_and_subst", rfl "e_ctx_uvar_and_subst");
    (RC.fstar_refl_types_lid "letbinding",         rfl "e_letbinding");
    (RC.fstar_refl_types_lid "ident",              rfl "e_ident");
    (RC.fstar_refl_types_lid "universe_uvar",      rfl "e_universe_uvar");
    (RC.fstar_refl_types_lid "universe",           rfl "e_universe");

    (RC.fstar_refl_data_lid "vconst",         rfl "e_vconst");
    (RC.fstar_refl_data_lid "aqualv",         rfl "e_aqualv");
    (RC.fstar_refl_data_lid "pattern",        rfl "e_pattern");
    (RC.fstar_refl_data_lid "namedv_view",    rfl "e_namedv_view");
    (RC.fstar_refl_data_lid "bv_view",        rfl "e_bv_view");
    (RC.fstar_refl_data_lid "binder_view",    rfl "e_binder_view");
    (RC.fstar_refl_data_lid "binding",        rfl "e_binding");
    (RC.fstar_refl_data_lid "universe_view",  rfl "e_universe_view");
    (RC.fstar_refl_data_lid "term_view",      rfl "e_term_view");
    (RC.fstar_refl_data_lid "comp_view",      rfl "e_comp_view");
    (RC.fstar_refl_data_lid "lb_view",        rfl "e_lb_view");
    (RC.fstar_refl_data_lid "sigelt_view",    rfl "e_sigelt_view");
    (RC.fstar_refl_data_lid "qualifier",      rfl "e_qualifier");
  ]

(* Embeddings generated for a [@@plugin] datatype in this run, by the type's
   lid.  They are generated the first time the type is met and reused after
   that, so this survives across modules. *)
let generated : ref (list (Ident.lident & embedding_data)) = mk_ref []

let find_embedding (l:Ident.lident) : ML (option embedding_data) =
  match List.find (fun (l', _) -> Ident.lid_equals l l') (!generated @ builtin_embeddings) with
  | Some (_, d) -> Some d
  | None -> None

(* -------------------------------------------------------------------- *)
(* Building F* syntax                                                   *)
(* -------------------------------------------------------------------- *)

let lid (s:string) : ML Ident.lident = Ident.lid_of_str s

let str (s:string) : ML term = S.mk (Tm_constant (Const_string (s, Range.dummyRange))) Range.dummyRange

(* [call f [ty..] [arg..]] is [f #ty.. arg..].  Every function this module
   generates a call to is polymorphic only in leading implicit binders, which
   is what F* makes of the ['a] in a signature, so passing the type arguments
   first and positionally is exactly right.  {!signature_of} checks it. *)
let call (f:Ident.lident) (tys:list term) (args:list term) : ML term =
  U.mk_app (S.fvar f None) (List.map S.iarg tys @ List.map S.as_arg args)

(* The binders of [f] after its leading [tys] implicit ones have been
   instantiated, and its result type.  This is where the generated code gets
   the *types* of the variables it binds -- the [psc], the [args] -- rather
   than inventing them; and it is the check that [call]'s positional
   convention holds, since a mismatch shows up as too few binders. *)
let signature_of (st:Extract.state) (f:Ident.lident) (tys:list term)
  : ML (list binder & typ) =
  Extract.ensure_lid_available st f;
  match TcEnv.try_lookup_lid (Extract.tcenv st) f with
  | None -> raise (NoEmbedding ("no declaration for " ^ Ident.string_of_lid f))
  | Some ((_, ty), _) ->
    let bs, c = U.arrow_formals_comp ty in
    let n = List.length tys in
    if List.length bs < n then
      raise (NoEmbedding (Ident.string_of_lid f ^ " has too few binders"));
    let imps, rest = List.splitAt n bs in
    List.iter2 (fun (b:binder) (_:term) ->
      if None? b.binder_qual then
        raise (NoEmbedding (Ident.string_of_lid f ^ " does not begin with implicit binders"))) imps tys;
    let s = List.map2 (fun (b:binder) (t:term) -> NT (b.binder_bv, t)) imps tys in
    (SS.subst_binders s rest, SS.subst s (U.comp_result c))

(* [f]'s last [n] binders, which is what a generated lambda binds: the
   normalizer hands a primitive step its callbacks and its argument list, and
   those are the trailing parameters of every interpretation function. *)
let last_binders (n:int) (bs:list binder) : ML (list binder) =
  let k = List.length bs in
  if k < n then raise (NoEmbedding "interpretation function has too few binders");
  snd (List.splitAt (k - n) bs)

let fresh_bvs (bs:list binder) : ML (list bv) =
  bs |> List.map (fun (b:binder) -> S.new_bv None b.binder_bv.sort)

(* -------------------------------------------------------------------- *)
(* Embeddings for a type                                                *)
(* -------------------------------------------------------------------- *)

type kind =
  | SyntaxTerm
  | NBETerm

(* The NBE side is best-effort: a type whose syntax embedding exists may have
   no NBE one, and the honest answer is a value that fails if the normalizer
   ever reaches it, not a refusal to compile the plugin at all. *)
let nbe_unsupported (t:typ) : ML term =
  call (lid "FStarC.TypeChecker.NBETerm.e_unsupported") [t] []

(* The weak head normal form, with the modules it takes to get there loaded.

   [ppname_t] is [Sealed.sealed string] behind two abbreviations, and only a
   weak head normal form gets there without unfolding into lambdas.  But an
   abbreviation whose module the run has not loaded does not unfold at all, and
   the failure is silent: the type merely looks abstract, and the embedding for
   it merely looks missing.  Nothing has asked for these modules -- the type of
   a plugin's argument is not something the demand-driven loop looks at -- so
   each head has to be loaded here, and again after each unfolding, since what
   it unfolds to may live somewhere else again. *)
let whnf (st:Extract.state) (t:typ) : ML typ =
  let head_lid (t:typ) : ML (option Ident.lident) =
    match (SS.compress (U.un_uinst (fst (U.head_and_args_full t)))).n with
    | Tm_fvar fv -> Some (S.lid_of_fv fv)
    | _ -> None in
  let rec go (fuel:int) (t:typ) : ML typ =
    match head_lid t with
    | None -> t
    | Some l ->
      Extract.ensure_lid_available st l;
      let t' = SS.compress (U.un_uinst (N.unfold_whnf (Extract.tcenv st) t)) in
      if fuel <= 0 then t' else
      (match head_lid t' with
       | Some l' when Ident.lid_equals l l' -> t'
       | _ -> go (fuel - 1) t') in
  go 20 (SS.compress (U.un_uinst t))

(* An F* term of type [embedding t] (or [NBET.embedding t]).

   Its ML counterpart builds ML syntax, and so has to name the *extracted*
   form of every combinator.  Building F* syntax instead means the result goes
   through {!Extract.expr_of_term} like anything else: the combinators are
   requested, specialized and typed by the ordinary loop. *)
let rec embedding_for (st:Extract.state) (k:kind) (t:typ) : ML term =
  let t = whnf st t in
  match t.n with
  | Tm_refine {b=x} -> embedding_for st k x.sort
  | Tm_ascribed {tm=t} -> embedding_for st k t

  | Tm_arrow _ when (match U.arrow_one_ln t with
                     | Some (_, c) -> U.is_pure_comp c
                     | None -> false) ->
    let b, c = Some?.v (U.arrow_one t) in
    let t0 = b.binder_bv.sort in
    let t1 = U.comp_result c in
    let comb = match k with
               | SyntaxTerm -> lid "FStarC.Syntax.Embeddings.e_arrow"
               | NBETerm    -> lid "FStarC.TypeChecker.NBETerm.e_arrow" in
    call comb [t0; t1] [embedding_for st k t0; embedding_for st k t1]

  | Tm_app _ ->
    let head, args = U.head_and_args_full t in
    (* A parameterized embedding takes the parameters' *types* implicitly and
       their embeddings explicitly, in the same order.  That is the shape of
       every one of them -- [e_list], [e_option], [e_tuple2] -- so the
       application needs no table beyond the head's. *)
    let tys = List.map fst args in
    (match embedding_head st k head with
     | Some f -> call f tys (List.map (embedding_for st k) tys)
     | None -> raise (NoEmbedding ("no embedding for " ^ show t)))

  | Tm_fvar _ ->
    (match embedding_head st k t with
     | Some f -> call f [] []
     | None -> raise (NoEmbedding ("no embedding for " ^ show t)))

  | _ -> raise (NoEmbedding ("cannot embed type " ^ show t))

(* The lid of the embedding for a type *constructor*, unapplied. *)
and embedding_head (st:Extract.state) (k:kind) (t:term) : ML (option Ident.lident) =
  match (SS.compress (U.un_uinst t)).n with
  | Tm_fvar fv ->
    let l = S.lid_of_fv fv in
    (match find_embedding l with
     | Some d ->
       (match k with
        | SyntaxTerm -> Some d.syn_emb
        | NBETerm -> d.nbe_emb)
     | None -> None)
  | _ -> None

(* -------------------------------------------------------------------- *)
(* The registration itself                                              *)
(* -------------------------------------------------------------------- *)

let native_lid (s:string) : name =
  { ns = ["FStarC"; "Tactics"; "Native"]; id = s; spec = None }

(* [FStarC.Tactics.Native.register_plugin] and [register_tactic] exist only in
   the hand-written [src/ml/FStarC_Tactics_Native.ml]: the module's interface
   does not declare them, because nothing in F* calls them -- only generated
   code does.  So there is nothing to request, and the reference is a
   [DExternal] this module puts there itself. *)
let register_fn (st:Extract.state) (which:string) (ty:cty) : ML name =
  let nm = native_lid which in
  Extract.emit st ("regemb-extern:" ^ which)
    (DExternal { dx_name = nm; dx_typars = []; dx_ty = ty;
                 dx_target = None; dx_header = None; dx_flags = [] });
  nm

let ir_call (f:name) (fty:cty) (args:list expr) : ML expr =
  let rec res (t:cty) (n:int) : ML cty =
    if n <= 0 then t else
    match t with
    | TArrow (_, _, t) -> res t (n - 1)
    | _ -> TAny in
  CSyn.mk (EApp (CSyn.mk (EQual (f, [])) fty E_Pure, args))
          (res fty (List.length args)) E_Impure

(* The interpretation function for a plugin, as an F* term.

   Its shape is fixed by the normalizer: a primitive step is a function of the
   callbacks and the list of arguments, returning an embedded result.  Both
   kinds of plugin get there through a library function that takes the
   embeddings and the compiled definition; all this builds is the lambda that
   feeds that function the callbacks it was handed. *)
let interp_term (st:Extract.state) (k:kind) (tac:bool) (fv_lid:Ident.lident)
                (n:int) (bs:list binder) (res:typ) : ML term =
  let tys = List.map (fun (b:binder) -> b.binder_bv.sort) bs @ [res] in
  let embs = tys |> List.map (embedding_for st k) in
  let f = S.fvar fv_lid None in
  if tac then begin
    (* [mk_tactic_interpretation_n name t e1 .. en er psc ncb us args].  With
       the [Tac] effect reified (section 7.5) the compiled definition already
       has the type this expects -- a function into [tac] -- so unlike the ML
       pipeline there is no [from_tactic_n] to insert. *)
    let h = lid ("FStarC.Tactics.InterpFuns.mk_tactic_interpretation_" ^ show n) in
    let hbs, _ = signature_of st h tys in
    let vs = fresh_bvs (last_binders 4 hbs) in
    let body = call h tys ([str (Ident.string_of_lid fv_lid ^ " (plugin)"); f]
                           @ embs @ List.map S.bv_to_name vs) in
    U.abs (List.map S.mk_binder vs) body None
  end else begin
    (* [arrow_as_prim_step_n e1 .. en er f lid cb us args].  The syntax
       version's callbacks are [psc] and [ncb] and only the second is passed
       on; the NBE version has just the one.  Hence the extra ignored binder,
       whose type has to be named here since no signature mentions it. *)
    let h = match k with
            | SyntaxTerm -> lid ("FStarC.Syntax.Embeddings.arrow_as_prim_step_" ^ show n)
            | NBETerm    -> lid ("FStarC.TypeChecker.NBETerm.arrow_as_prim_step_" ^ show n) in
    let hbs, _ = signature_of st h tys in
    (* [cb], then the [universes] and [args] of the returned function. *)
    let vs = fresh_bvs (last_binders 3 hbs) in
    let lid_of_str = call (lid "FStarC.Ident.lid_of_str") [] [str (Ident.string_of_lid fv_lid)] in
    let body = call h tys (embs @ [f; lid_of_str] @ List.map S.bv_to_name vs) in
    let vs = match k with
             | NBETerm -> vs
             | SyntaxTerm ->
               S.new_bv None (S.fvar (lid "FStarC.TypeChecker.Primops.Base.psc") None) :: vs in
    U.abs (List.map S.mk_binder vs) body None
  end

(* Strip the leading type binders, if any.  A plugin polymorphic in a type is
   registered by the ML pipeline with an identity embedding for the variable
   and a hand-written prefix match to drop the type arguments off the argument
   list; Custard does not do that yet, and says so rather than registering
   something that would unembed at the wrong type. *)
let reject_type_binders (st:Extract.state) (bs:list binder) : ML unit =
  bs |> List.iter (fun (b:binder) ->
    match (SS.compress b.binder_bv.sort).n with
    | Tm_type _ -> raise (NoEmbedding "plugins with type arguments are not supported yet")
    | _ -> ())

let plugin_norm_steps : list TcEnv.step = [
  TcEnv.EraseUniverses;
  TcEnv.AllowUnboundUniverses;
  TcEnv.UnfoldUntil S.delta_constant;  (* see through [nat] and friends *)
  TcEnv.ForExtraction;
]

let registration (st:Extract.state) (arity_opt:option int) (r:Range.t)
                 (lb:letbinding) : ML unit =
  let fv = Inr?.v lb.lbname in
  let fv_lid = S.lid_of_fv fv in
  let name_str = Ident.string_of_lid fv_lid in
  let key = "regemb:" ^ name_str in
  if Extract.emitted st key then () else
  let t = N.normalize plugin_norm_steps (Extract.tcenv st) lb.lbtyp in
  let bs, c = U.arrow_formals_comp t in
  (* An explicit [@@plugin n] says how many of the arrows are the plugin's
     arguments; the rest belong to its result. *)
  let bs, c =
    match arity_opt with
    | None -> bs, c
    | Some k ->
      let nbs = List.length bs in
      if k = nbs then bs, c
      else if k < nbs then
        let bs, rest = BU.first_N k bs in
        bs, S.mk_Total (U.arrow rest c)
      else raise (NoEmbedding (Format.fmt2 "expected arity at least %s; got %s"
                                 (show k) (show nbs))) in
  reject_type_binders st bs;
  let n = List.length bs in
  let res = U.comp_result c in
  let tac =
    not (U.is_pure_comp c) &&
    Ident.lid_equals (TcEnv.norm_eff_name (Extract.tcenv st) (U.comp_effect_name c))
                     PC.effect_TAC_lid in
  if not tac && not (U.is_pure_comp c) then
    raise (NoEmbedding ("no plugin for effect " ^ Ident.string_of_lid (U.comp_effect_name c)));
  if n = 0 then
    raise (NoEmbedding "a plugin must take at least one argument");
  if tac && n > 20 then
    raise (NoEmbedding "tactic plugins can take at most 20 arguments");
  let string_ty = Extract.ty_of_typ st S.t_string in
  let int_ty    = Extract.ty_of_typ st S.t_int in
  let interp = Extract.expr_of_term st (interp_term st SyntaxTerm tac fv_lid n bs res) in
  let args, which, arity =
    if tac then [interp], "register_tactic", n + 1
    else
      let nbe = Extract.expr_of_term st (interp_term st NBETerm tac fv_lid n bs res) in
      [interp; nbe], "register_plugin", n in
  let fty = List.fold_right (fun (a:expr) (t:cty) -> TArrow (a.ty, E_Pure, t))
                            args TUnit in
  let fty = TArrow (string_ty, E_Pure, TArrow (int_ty, E_Pure, fty)) in
  let reg = register_fn st which fty in
  let body = ir_call reg fty
               ([CSyn.mk (EConst (CString name_str)) string_ty E_Pure;
                 CSyn.mk (EConst (CInt (show arity, None))) int_ty E_Pure] @ args) in
  let nm = Extract.name_of_lid fv_lid in
  Extract.emit st key
    (DLet { dl_name = { nm with id = "__plugin_" ^ nm.id };
            dl_typars = []; dl_binders = []; dl_ret = TUnit; dl_eff = E_Impure;
            dl_body = body;
            (* Nothing refers to a registration, so only [Root] keeps it. *)
            dl_flags = [Root; Comment ("Plugin registration for " ^ name_str)] })

(* -------------------------------------------------------------------- *)
(* Driving                                                              *)
(* -------------------------------------------------------------------- *)

(* [@@plugin] optionally takes an arity: [None] is not a plugin at all,
   [Some None] a plugin whose arity is its type's, [Some (Some n)] one that
   says so explicitly. *)
let plugin_arity (attrs:list term) : ML (option (option int)) =
  BU.find_map attrs (fun (t:term) ->
    let head, args = U.head_and_args_full t in
    if not (U.is_fvar PC.plugin_attr head) then None
    else match args with
         | [(a, _)] -> Some (FStarC.Syntax.Embeddings.unembed a FStarC.Syntax.Embeddings.id_norm_cb)
         | _ -> Some None)

let handle_sigelt (st:Extract.state) (arity_opt:option int) (se:sigelt) : ML unit =
  match se.sigel with
  | Sig_let {lbs=(_, lbs)} ->
    lbs |> List.iter (fun lb ->
      try registration st arity_opt se.sigrng lb with
      | NoEmbedding msg ->
        warn_not_implemented se.sigrng
          (match lb.lbname with
           | Inr fv -> Ident.string_of_lid (S.lid_of_fv fv)
           | Inl bv -> Ident.string_of_id bv.ppname) msg)
  | _ -> ()

(* Only a module the *program* asked for by name gets registrations.

   Custard loads a module because something in it is called, which says
   nothing about whether its plugins are wanted: a test that merely uses
   [FStar.Tactics] would otherwise acquire registrations for every [@@plugin]
   in the tactic library, together with all the embedding code they reach.
   Naming the module in [--custard_entry] is the request, and it is also what
   makes the plugin's own definition a root -- a plugin is a leaf of the
   program, nothing calls it. *)
let requested (roots:list Ident.lident) (md:modul) : ML bool =
  let m = Ident.string_of_lid md.name in
  roots |> List.existsb (fun l -> Ident.string_of_lid l = m)

let handle_module (st:Extract.state) (roots:list Ident.lident) (md:modul) : ML unit =
  if not (requested roots md) then () else
  md.declarations |> List.iter (fun (se:sigelt) ->
    match plugin_arity se.sigattrs with
    | None -> ()
    (* A projector or a discriminator inherits its type's attributes, so it
       inherits [@@plugin] too; it is not one. *)
    | Some _ when se.sigquals |> List.existsb (function Projector _ | Discriminator _ -> true
                                                      | _ -> false) -> ()
    | Some arity_opt -> handle_sigelt st arity_opt se)
