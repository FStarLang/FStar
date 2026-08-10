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
module Mono    = FStarC.Custard.Mono
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

let find_embedding (l:Ident.lident) : ML (option embedding_data) =
  match List.find (fun (l', _) -> Ident.lid_equals l l') builtin_embeddings with
  | Some (_, d) -> Some d
  | None -> None

(* -------------------------------------------------------------------- *)
(* Embeddings generated for a [@@plugin] datatype                       *)
(* -------------------------------------------------------------------- *)

(* A [@@plugin] datatype has no embedding of its own; one is generated beside
   it, as the ML pipeline does.  The generated embedding is a *declaration*,
   not an F* definition, so there is no lid for {!embedding_for} to return --
   and {!embedding_for} has to return F* syntax, because that is what the
   whole design of this module rests on (section 13.1).

   The way out is a placeholder: a fresh variable of type [embedding t], free
   in whatever term is being generated.  {!compile} abstracts over the ones a
   term actually mentions and applies the resulting IR lambda to the
   declarations they stand for.  Nothing else in the module has to know. *)
type gen_emb = {
  ge_lid  : Ident.lident;
  ge_ph   : bv;    (** the placeholder standing for this type's embedding *)
  ge_emb  : name;  (** [e_t], the embedding itself *)
  ge_knot : name;  (** [__knot_e_t], the thunk that breaks the recursion *)
}

let generated : ref (list gen_emb) = mk_ref []

(* The mutual group whose declarations are being generated right now.  A
   reference to one of *those* has to go through the thunk: [e_t] is defined
   by unthunking, so a body reaching for it directly would be reading a
   binding that is not initialized yet.  The ML pipeline has the same two
   levels, for the same reason -- OCaml's [let rec] admits mutually recursive
   *functions*, and [mk_extracted_embedding ...] is not one. *)
let building : ref (list Ident.lident) = mk_ref []

let find_generated (l:Ident.lident) : ML (option gen_emb) =
  List.find (fun (g:gen_emb) -> Ident.lid_equals g.ge_lid l) !generated

let emb_base (s:string) : ML Ident.lident =
  Ident.lid_of_str ("FStarC.Syntax.Embeddings.Base." ^ s)

let embedding_typ (t:typ) : ML typ =
  U.mk_app (S.fvar (Ident.lid_of_str "FStarC.Syntax.Embeddings.Base.embedding") None)
           [S.as_arg t]

(* Replace a variable by an expression, everywhere it occurs.

   This is a *substitution*, not a binding, and the difference is the whole
   point.  Binding the placeholder -- [let x = __knot_e_t () in body] -- forces
   the thunk before the body is built, and for a recursive type that is an
   infinite loop: [e_pattern]'s [Pat_Cons] payload reaches for [e_pattern]
   again.  The occurrences the generator wrote are inside the embedder and
   unembedder closures, which run only once there is a value to embed, and
   substitution is what leaves them there.  See {!building}.

   Nothing here has to worry about capture: the placeholder is a fresh name and
   the expression put in its place mentions only top-level declarations. *)
let rec subst_expr (x:string) (v:expr) (e:expr) : ML expr =
  let go = subst_expr x v in
  let go_br (br:CSyn.branch) : ML CSyn.branch =
    let (p, g, b) = br in (p, Option.map go g, go b) in
  match e.e with
  | EVar y when y = x -> v
  | EConst _ | EVar _ | EQual _ | EAny | EAbort _ -> e
  | ELet (y, t, e1, e2) ->
    (* A binder of the same name shadows the placeholder in its scope. *)
    { e with e = ELet (y, t, go e1, (if y = x then e2 else go e2)) }
  | EApp (h, args) -> { e with e = EApp (go h, List.map go args) }
  | EFun (bs, b) ->
    let shadows = List.existsb (fun (b:CSyn.binder) -> b.b_name = x) bs in
    { e with e = EFun (bs, (if shadows then b else go b)) }
  | EMatch (sc, brs) -> { e with e = EMatch (go sc, List.map go_br brs) }
  | EIf (c, a, b) -> { e with e = EIf (go c, go a, go b) }
  | ESeq (a, b) -> { e with e = ESeq (go a, go b) }
  | ECtor (n, es) -> { e with e = ECtor (n, List.map go es) }
  | ETuple es -> { e with e = ETuple (List.map go es) }
  | ERecord (n, fs) ->
    { e with e = ERecord (n, fs |> List.map (fun (f, a) -> (f, go a))) }
  | EProj (a, n, f) -> { e with e = EProj (go a, n, f) }
  | EDiscrim (a, n) -> { e with e = EDiscrim (go a, n) }
  | ECast (a, t) -> { e with e = ECast (go a, t) }
  | EOp (o, es) -> { e with e = EOp (o, List.map go es) }
  | EWhile (c, b) -> { e with e = EWhile (go c, go b) }
  | ERaise a -> { e with e = ERaise (go a) }
  | ETry (a, brs) -> { e with e = ETry (go a, List.map go_br brs) }

(* Translate a generated term, resolving its placeholders.  With none of them
   this is just {!Extract.expr_of_term}; with some, each placeholder is
   replaced, in place, by the declaration it stands for. *)
let compile (st:Extract.state) (t:term) : ML expr =
  let free = FStarC.Syntax.Free.names t in
  let used = !generated |> List.filter (fun (g:gen_emb) ->
               FStarC.Class.Setlike.mem g.ge_ph free) in
  match used with
  | [] -> Extract.expr_of_term st t
  | _ ->
    let e = Extract.expr_of_term st t in
    used |> List.fold_left (fun (e:expr) (g:gen_emb) ->
      let ety = Extract.ty_of_typ st g.ge_ph.sort in
      let v =
        if List.existsb (Ident.lid_equals g.ge_lid) !building
        then CSyn.mk (EApp (CSyn.mk (EQual (g.ge_knot, []))
                                    (TArrow (TUnit, E_Impure, ety)) E_Pure,
                            [CSyn.mk (EConst CUnit) TUnit E_Pure])) ety E_Impure
        else CSyn.mk (EQual (g.ge_emb, [])) ety E_Impure in
      subst_expr (CSyn.uniq (Ident.string_of_id g.ge_ph.ppname) g.ge_ph.index) v e) e

let dummy : Range.t = Range.dummyRange

let ctor_fv (l:Ident.lident) : ML fv = S.lid_and_dd_as_fv l (Some Data_ctor)

let pat_of (v:pat') : pat = withinfo v dummy

let dot_pat : pat = pat_of (Pat_dot_term None)

(* [[e1; ...; en]] at type [ty]. *)
let rec term_list (ty:typ) (es:list term) : ML term =
  match es with
  | [] -> U.mk_app (S.tdataconstr PC.nil_lid) [S.iarg ty]
  | e :: es -> U.mk_app (S.tdataconstr PC.cons_lid)
                        [S.iarg ty; S.as_arg e; S.as_arg (term_list ty es)]

let rec list_pat (vs:list bv) : ML pat =
  match vs with
  | [] -> pat_of (Pat_cons (ctor_fv PC.nil_lid, None, [(dot_pat, true)]))
  | v :: vs -> pat_of (Pat_cons (ctor_fv PC.cons_lid, None,
                                 [(dot_pat, true);
                                  (pat_of (Pat_var v), false);
                                  (list_pat vs, false)]))

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
    (* Stop at a type the table knows.  Unfolding is a means of *reaching* one
       of those, and going past it loses: [range] is an abbreviation of
       [FStarC.Range.Type.range], which nothing has an embedding for. *)
    | Some l when Some? (find_embedding l) -> t
    | Some l ->
      Extract.ensure_lid_available st l;
      let t' = Mono.norm_bounded (Extract.tcenv st) "an embedded type"
                                 [TcEnv.Primops; TcEnv.Weak; TcEnv.HNF;
                                  TcEnv.UnfoldUntil S.delta_constant; TcEnv.Beta]
                                 t in
      let t' = SS.compress (U.un_uinst t') in
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

  | Tm_fvar fv ->
    (match embedding_head st k t with
     | Some f -> call f [] []
     | None ->
       (* A [@@plugin] datatype gets an embedding generated for it, here and
          now if this is the first time it is met.  Generating it on demand
          rather than when its own module is handled means the order the
          modules happen to arrive in cannot matter. *)
       if not (TcEnv.fv_has_attr (Extract.tcenv st) fv PC.plugin_attr) then
         raise (NoEmbedding ("no embedding for " ^ show t))
       else match k with
            | NBETerm -> nbe_unsupported t
            | SyntaxTerm ->
              let l = S.lid_of_fv fv in
              ensure_generated st l;
              (match find_generated l with
               | Some g -> S.bv_to_name g.ge_ph
               | None -> raise (NoEmbedding ("no embedding for " ^ show t))))

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

(* Generate the embeddings for the mutual group [l] belongs to, unless they
   already exist.  Every member is registered *before* any body is built, so
   that a type that mentions itself -- which is most of them -- terminates. *)
and ensure_generated (st:Extract.state) (l:Ident.lident) : ML unit =
  if Some? (find_generated l) then () else
  match TcEnv.lookup_sigelt (Extract.tcenv st) l with
  | Some ({sigel = Sig_inductive_typ {params; mutuals}}) ->
    if Cons? params then
      raise (NoEmbedding ("cannot generate an embedding for " ^ Ident.string_of_lid l ^
                          ": the inductive has parameters"));
    let group = l :: (mutuals |> List.filter (fun m -> not (Ident.lid_equals m l))) in
    let entries = group |> List.map (fun (g:Ident.lident) ->
      let nm = Extract.name_of_lid g in
      let e = { ge_lid  = g;
                ge_ph   = S.new_bv None (embedding_typ (S.fvar g None));
                ge_emb  = { nm with id = "e_" ^ nm.id };
                ge_knot = { nm with id = "__knot_e_" ^ nm.id } } in
      generated := e :: !generated;
      e) in
    let saved = !building in
    building := group @ saved;
    entries |> List.iter (generate_one st);
    building := saved
  | _ ->
    raise (NoEmbedding ("no inductive declaration for " ^ Ident.string_of_lid l))

and generate_one (st:Extract.state) (g:gen_emb) : ML unit =
  let env = Extract.tcenv st in
  let gty = S.fvar g.ge_lid None in
  let _, cs = TcEnv.datacons_of_typ env g.ge_lid in
  let ctors = cs |> List.map (fun (c:Ident.lident) ->
    match TcEnv.lookup_sigelt env c with
    | Some ({sigel = Sig_datacon {t}}) -> (c, fst (U.arrow_formals t))
    | _ -> raise (NoEmbedding ("no declaration for constructor " ^ Ident.string_of_lid c))) in
  let body = compile st (call (emb_base "mk_extracted_embedding") [gty]
                              [str (Ident.string_of_lid g.ge_lid);
                               unembed_fun st gty ctors;
                               embed_fun st gty ctors]) in
  let ety = Extract.ty_of_typ st (embedding_typ gty) in
  Extract.emit st ("regemb-knot:" ^ Ident.string_of_lid g.ge_lid)
    (DLet { dl_name = g.ge_knot; dl_typars = [];
            dl_binders = [{ b_name = "_thunk"; b_ty = TUnit }];
            dl_ret = ety; dl_eff = E_Impure; dl_body = body;
            dl_flags = [Comment ("Embedding for " ^ Ident.string_of_lid g.ge_lid)] });
  Extract.emit st ("regemb-emb:" ^ Ident.string_of_lid g.ge_lid)
    (DLet { dl_name = g.ge_emb; dl_typars = []; dl_binders = []; dl_ret = ety;
            dl_eff = E_Impure;
            dl_body = CSyn.mk (EApp (CSyn.mk (EQual (g.ge_knot, []))
                                             (TArrow (TUnit, E_Impure, ety)) E_Pure,
                                     [CSyn.mk (EConst CUnit) TUnit E_Pure])) ety E_Impure;
            dl_flags = [] })

(* [fun (x:t) -> match x with | C v1 .. vk -> mk_app (tdataconstr "M.C")
                                                [as_arg (embed e1 v1); ...]] *)
and embed_fun (st:Extract.state) (gty:typ)
              (ctors:list (Ident.lident & list binder)) : ML term =
  let x = S.new_bv None gty in
  let arg_ty = S.fvar (Ident.lid_of_str "FStarC.Syntax.Syntax.arg") None in
  let brs = ctors |> List.map (fun (c, bs) ->
    let vs = bs |> List.map (fun (b:binder) -> S.new_bv None b.binder_bv.sort) in
    let p = pat_of (Pat_cons (ctor_fv c, None,
              List.map2 (fun (b:binder) (v:bv) ->
                (pat_of (Pat_var v), Some? b.binder_qual)) bs vs)) in
    let args = List.map2 (fun (b:binder) (v:bv) ->
      call (Ident.lid_of_str "FStarC.Syntax.Syntax.as_arg") []
        [call (emb_base "extracted_embed") [b.binder_bv.sort]
              [embedding_for st SyntaxTerm b.binder_bv.sort; S.bv_to_name v]]) bs vs in
    let head = call (Ident.lid_of_str "FStarC.Syntax.Syntax.tdataconstr") []
                 [call (Ident.lid_of_str "FStarC.Ident.lid_of_str") []
                       [str (Ident.string_of_lid c)]] in
    SS.close_branch (p, None,
      call (Ident.lid_of_str "FStarC.Syntax.Util.mk_app") []
           [head; term_list arg_ty args])) in
  U.abs [S.mk_binder x]
        (S.mk (Tm_match { scrutinee = S.bv_to_name x; ret_opt = None;
                          brs; rc_opt = None }) dummy) None

(* [fun (tm : string & list term) -> match tm with
     | ("M.C", [p1; ..; pk]) -> bind (unembed e1 p1) (fun v1 -> ... Some (C v1 ..))
     | _ -> None] *)
and unembed_fun (st:Extract.state) (gty:typ)
                (ctors:list (Ident.lident & list binder)) : ML term =
  let t_term = S.fvar (Ident.lid_of_str "FStarC.Syntax.Syntax.term") None in
  let t_terms = U.mk_app (S.fvar PC.list_lid None) [S.as_arg t_term] in
  let scrut_ty = U.mk_app (S.fvar (PC.mk_tuple_lid 2 dummy) None)
                          [S.as_arg S.t_string; S.as_arg t_terms] in
  let tm = S.new_bv None scrut_ty in
  let none = U.mk_app (S.tdataconstr PC.none_lid) [S.iarg gty] in
  let brs = ctors |> List.map (fun (c, bs) ->
    let ps = bs |> List.map (fun _ -> S.new_bv None t_term) in
    let vs = bs |> List.map (fun (b:binder) -> S.new_bv None b.binder_bv.sort) in
    let p = pat_of (Pat_cons (ctor_fv (Ident.lid_of_str "FStar.Pervasives.Native.Mktuple2"),
              None,
              [(dot_pat, true); (dot_pat, true);
               (pat_of (Pat_constant (Const_string (Ident.string_of_lid c, dummy))), false);
               (list_pat ps, false)])) in
    let ret = U.mk_app (S.tdataconstr PC.some_lid)
                [S.iarg gty;
                 S.as_arg (U.mk_app (S.tdataconstr c)
                             (List.map2 (fun (b:binder) (v:bv) ->
                                (S.bv_to_name v, U.aqual_of_binder b)) bs vs))] in
    let steps = List.map2 (fun (b:binder) ((pv, v):bv & bv) -> (b, pv, v))
                          bs (List.map2 (fun (a:bv) (b:bv) -> (a, b)) ps vs) in
    let body = List.fold_right (fun ((b, pv, v):binder & bv & bv) (acc:term) ->
      call (Ident.lid_of_str "FStarC.Option.bind") [b.binder_bv.sort; gty]
        [call (emb_base "extracted_unembed") [b.binder_bv.sort]
              [embedding_for st SyntaxTerm b.binder_bv.sort; S.bv_to_name pv];
         U.abs [S.mk_binder v] acc None]) steps ret in
    SS.close_branch (p, None, body)) in
  let catchall = SS.close_branch (pat_of (Pat_var (S.new_bv None scrut_ty)), None, none) in
  U.abs [S.mk_binder tm]
        (S.mk (Tm_match { scrutinee = S.bv_to_name tm; ret_opt = None;
                          brs = brs @ [catchall]; rc_opt = None }) dummy) None

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
  let t = Mono.norm_bounded (Extract.tcenv st) "a plugin's type"
                            plugin_norm_steps lb.lbtyp in
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
  let interp = compile st (interp_term st SyntaxTerm tac fv_lid n bs res) in
  let args, which, arity =
    if tac then [interp], "register_tactic", n + 1
    else
      let nbe = compile st (interp_term st NBETerm tac fv_lid n bs res) in
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
