(*
   Copyright 2008-2022 Microsoft Research

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
module FStarC.Reflection.V2.NBEEmbeddings
open FStarC
open FStarC
open FStarC.Effect
open FStarC.Reflection.V2.Data
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.NBETerm
open FStarC.Order
open FStarC.Errors
open FStarC.Dyn
open FStarC.Reflection.V2.Constants

module Env     = FStarC.TypeChecker.Env
module Err     = FStarC.Errors
module I       = FStarC.Ident
module NBETerm = FStarC.TypeChecker.NBETerm
module PC      = FStarC.Parser.Const
module Range   = FStarC.Range
module S       = FStarC.Syntax.Syntax // TODO: remove, it's open
module U       = FStarC.Syntax.Util

(*
 * embed   : from compiler to user
 * unembed : from user to compiler
 *)

let noaqs : antiquotations = (0, [])

(* -------------------------------------------------------------------------------------- *)
(* ------------------------------------- EMBEDDINGS ------------------------------------- *)
(* -------------------------------------------------------------------------------------- *)

(* PLEASE NOTE: Construct and FV accumulate their arguments BACKWARDS. That is,
 * the expression (f 1 2) is stored as FV (f, [], [Constant (Int 2); Constant (Int 1)].
 * So be careful when calling mkFV/mkConstruct and matching on them. *)

(* On that note, we use this (inefficient, FIXME) hack in this module *)
let mkFV fv us ts = mkFV fv (List.rev us) (List.rev ts)
let mkConstruct fv us ts = mkConstruct fv (List.rev us) (List.rev ts)
(* ^ We still need to match on them in reverse order though, so this is pretty dumb *)

let fv_as_emb_typ fv = S.ET_app (FStarC.Ident.string_of_lid fv.fv_name.v, [])
let mk_emb' x y fv = mk_emb x y (fun () -> mkFV fv [] []) (fun () -> fv_as_emb_typ fv)

let mk_lazy cb obj ty kind =
    let li = {
          blob = FStarC.Dyn.mkdyn obj
        ; lkind = kind
        ; ltyp = ty
        ; rng = Range.dummyRange
    }
    in
    let thunk = Thunk.mk (fun () -> translate_cb cb (U.unfold_lazy li)) in
    mk_t (Lazy (Inl li, thunk))

let e_bv =
    let embed_bv cb (bv:bv) : t =
        mk_lazy cb bv fstar_refl_bv Lazy_bv
    in
    let unembed_bv cb (t:t) : option bv =
        match t.nbe_t with
        | Lazy (Inl {blob=b; lkind=Lazy_bv}, _) ->
            Some <| FStarC.Dyn.undyn b
        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded bv: %s" (t_to_string t));
            None
    in
    mk_emb' embed_bv unembed_bv fstar_refl_bv_fv

let e_namedv =
    let embed_namedv cb (namedv:namedv) : t =
        mk_lazy cb namedv fstar_refl_namedv Lazy_namedv
    in
    let unembed_namedv cb (t:t) : option namedv =
        match t.nbe_t with
        | Lazy (Inl {blob=b; lkind=Lazy_namedv}, _) ->
            Some <| FStarC.Dyn.undyn b
        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded namedv: %s" (t_to_string t));
            None
    in
    mk_emb' embed_namedv unembed_namedv fstar_refl_namedv_fv

let e_binder =
    let embed_binder cb (b:binder) : t =
        mk_lazy cb b fstar_refl_binder Lazy_binder
    in
    let unembed_binder cb (t:t) : option binder =
        match t.nbe_t with
        | Lazy (Inl {blob=b; lkind=Lazy_binder}, _) ->
            Some (undyn b)
        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded binder: %s" (t_to_string t));
            None
    in
    mk_emb' embed_binder unembed_binder fstar_refl_binder_fv

let rec mapM_opt (f : ('a -> option 'b)) (l : list 'a) : option (list 'b) =
    match l with
    | [] -> Some []
    | x::xs ->
        Option.bind (f x) (fun x ->
        Option.bind (mapM_opt f xs) (fun xs ->
        Some (x :: xs)))

let e_term_aq aq =
    let embed_term cb (t:term) : NBETerm.t =
        let qi = { qkind = Quote_static; antiquotations = aq } in
        mk_t (NBETerm.Quote (t, qi))
    in
    let unembed_term cb (t:NBETerm.t) : option term =
        match t.nbe_t with
        | NBETerm.Quote (tm, qi) ->
            (* Just reuse the code from Reflection *)
            Syntax.Embeddings.unembed #_ #(Reflection.V2.Embeddings.e_term_aq (0, [])) (S.mk (Tm_quoted (tm, qi)) Range.dummyRange) Syntax.Embeddings.id_norm_cb
        | _ ->
            None
    in
    { NBETerm.em = embed_term
    ; NBETerm.un = unembed_term
    ; NBETerm.typ = (fun () -> mkFV fstar_refl_term_fv [] [])
    ; NBETerm.e_typ = (fun () -> fv_as_emb_typ fstar_refl_term_fv )
    }

let e_term = e_term_aq (0, [])

let e_sort = e_sealed e_term
let e_ppname = e_sealed e_string

let e_aqualv =
    let embed_aqualv cb (q : aqualv) : t =
        match q with
        | Data.Q_Explicit -> mkConstruct ref_Q_Explicit.fv [] []
        | Data.Q_Implicit -> mkConstruct ref_Q_Implicit.fv [] []
        | Data.Q_Meta t   -> mkConstruct ref_Q_Meta.fv [] [as_arg (embed e_term cb t)]
    in
    let unembed_aqualv cb (t : t) : option aqualv =
        match t.nbe_t with
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_Q_Explicit.lid -> Some Data.Q_Explicit
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_Q_Implicit.lid -> Some Data.Q_Implicit
        | Construct (fv, [], [(t, _)]) when S.fv_eq_lid fv ref_Q_Meta.lid ->
            Option.bind (unembed e_term cb t) (fun t ->
            Some (Data.Q_Meta t))

        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded aqualv: %s" (t_to_string t));
            None
    in
    mk_emb embed_aqualv unembed_aqualv
        (fun () -> mkConstruct fstar_refl_aqualv_fv [] [])
        (fun () -> fv_as_emb_typ fstar_refl_aqualv_fv)

let e_binders = e_list e_binder

let e_fv =
    let embed_fv cb (fv:fv) : t =
        mk_lazy cb fv fstar_refl_fv Lazy_fvar
    in
    let unembed_fv cb (t:t) : option fv =
        match t.nbe_t with
        | Lazy (Inl {blob=b; lkind=Lazy_fvar}, _) ->
            Some (undyn b)
        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded fvar: %s" (t_to_string t));
            None
    in
    mk_emb' embed_fv unembed_fv fstar_refl_fv_fv

let e_comp =
    let embed_comp cb (c:S.comp) : t =
        mk_lazy cb c fstar_refl_comp Lazy_comp
    in
    let unembed_comp cb (t:t) : option S.comp =
        match t.nbe_t with
        | Lazy (Inl {blob=b; lkind=Lazy_comp}, _) ->
            Some (undyn b)
        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded comp: %s" (t_to_string t));
            None
    in
    mk_emb' embed_comp unembed_comp fstar_refl_comp_fv

let e_env =
    let embed_env cb (e:Env.env) : t =
        mk_lazy cb e fstar_refl_env Lazy_env
    in
    let unembed_env cb (t:t) : option Env.env =
        match t.nbe_t with
        | Lazy (Inl {blob=b; lkind=Lazy_env}, _) ->
            Some (undyn b)
        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded env: %s" (t_to_string t));
            None
    in
    mk_emb' embed_env unembed_env fstar_refl_env_fv

let e_vconst =
    let embed_const cb (c:vconst) : t =
        match c with
        | C_Unit         -> mkConstruct ref_C_Unit.fv    [] []
        | C_True         -> mkConstruct ref_C_True.fv    [] []
        | C_False        -> mkConstruct ref_C_False.fv   [] []
        | C_Int i        -> mkConstruct ref_C_Int.fv     [] [as_arg (mk_t <| Constant (Int i))]
        | C_String s     -> mkConstruct ref_C_String.fv  [] [as_arg (embed e_string cb s)]
        | C_Range r      -> mkConstruct ref_C_Range.fv   [] [as_arg (embed e_range cb r)]
        | C_Reify        -> mkConstruct ref_C_Reify.fv   [] []
        | C_Reflect ns   -> mkConstruct ref_C_Reflect.fv [] [as_arg (embed e_string_list cb ns)]
    in
    let unembed_const cb (t:t) : option vconst =
        match t.nbe_t with
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_C_Unit.lid ->
            Some C_Unit

        | Construct (fv, [], []) when S.fv_eq_lid fv ref_C_True.lid ->
            Some C_True

        | Construct (fv, [], []) when S.fv_eq_lid fv ref_C_False.lid ->
            Some C_False

        | Construct (fv, [], [(i, _)]) when S.fv_eq_lid fv ref_C_Int.lid ->
            Option.bind (unembed e_int cb i) (fun i ->
            Some <| C_Int i)

        | Construct (fv, [], [(s, _)]) when S.fv_eq_lid fv ref_C_String.lid ->
            Option.bind (unembed e_string cb s) (fun s ->
            Some <| C_String s)

        | Construct (fv, [], [(r, _)]) when S.fv_eq_lid fv ref_C_Range.lid ->
            Option.bind (unembed e_range cb r) (fun r ->
            Some <| C_Range r)

        | Construct (fv, [], []) when S.fv_eq_lid fv ref_C_Reify.lid ->
            Some C_Reify

        | Construct (fv, [], [(ns, _)]) when S.fv_eq_lid fv ref_C_Reflect.lid ->
            Option.bind (unembed e_string_list cb ns) (fun ns ->
            Some <| C_Reflect ns)

        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded vconst: %s" (t_to_string t));
            None
    in
    mk_emb' embed_const unembed_const fstar_refl_vconst_fv

let e_universe =
  let embed_universe cb (u:universe) : t =
    mk_lazy cb u fstar_refl_universe Lazy_universe in
  let unembed_universe cb (t:t) : option S.universe =
    match t.nbe_t with
    | Lazy (Inl {blob=b; lkind=Lazy_universe}, _) ->
      Some (undyn b)
    | _ ->
      Err.log_issue0 Err.Warning_NotEmbedded
        (Format.fmt1 "Not an embedded universe: %s" (t_to_string t));
      None
    in
    mk_emb' embed_universe unembed_universe fstar_refl_universe_fv

let rec e_pattern_aq aq =
    let embed_pattern cb (p : pattern) : t =
        match p with
        | Pat_Constant c ->
            mkConstruct ref_Pat_Constant.fv [] [as_arg (embed e_vconst cb c)]
        | Pat_Cons fv us_opt ps ->
            mkConstruct ref_Pat_Cons.fv []
              [as_arg (embed e_fv cb fv);
               as_arg (embed (e_option (e_list e_universe)) cb us_opt);
               as_arg (embed (e_list (e_tuple2 (e_pattern_aq aq) e_bool)) cb ps)]
        | Pat_Var sort ppname ->
            mkConstruct ref_Pat_Var.fv [] [as_arg (embed e_sort cb sort); as_arg (embed e_ppname cb ppname)]
        | Pat_Dot_Term eopt ->
            mkConstruct ref_Pat_Dot_Term.fv [] [as_arg (embed (e_option e_term) cb eopt)]
    in
    let unembed_pattern cb (t : t) : option pattern =
        match t.nbe_t with
        | Construct (fv, [], [(c, _)]) when S.fv_eq_lid fv ref_Pat_Constant.lid ->
            Option.bind (unembed e_vconst cb c) (fun c ->
            Some <| Pat_Constant c)

        | Construct (fv, [], [(ps, _); (us_opt, _); (f, _)]) when S.fv_eq_lid fv ref_Pat_Cons.lid ->
            Option.bind (unembed e_fv cb f) (fun f ->
            Option.bind (unembed (e_option (e_list e_universe)) cb us_opt) (fun us ->
            Option.bind (unembed (e_list (e_tuple2 (e_pattern_aq aq) e_bool)) cb ps) (fun ps ->
            Some <| Pat_Cons f us ps)))

        | Construct (fv, [], [(ppname, _); (sort, _)]) when S.fv_eq_lid fv ref_Pat_Var.lid ->
            Option.bind (unembed e_sort cb sort) (fun sort ->
            Option.bind (unembed e_ppname cb ppname) (fun ppname ->
            Some <| Pat_Var sort ppname))

        | Construct (fv, [], [(eopt, _)]) when S.fv_eq_lid fv ref_Pat_Dot_Term.lid ->
            Option.bind (unembed (e_option e_term) cb eopt) (fun eopt ->
            Some <| Pat_Dot_Term eopt)

        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded pattern: %s" (t_to_string t));
            None
    in
    mk_emb' embed_pattern unembed_pattern fstar_refl_pattern_fv

let e_pattern = e_pattern_aq noaqs

let e_branch = e_tuple2 e_pattern e_term
let e_argv   = e_tuple2 e_term    e_aqualv

let e_branch_aq aq = e_tuple2 (e_pattern_aq aq) (e_term_aq aq)
let e_argv_aq   aq = e_tuple2 (e_term_aq aq) e_aqualv

let e_match_returns_annotation =
  e_option (e_tuple2 e_binder
                     (e_tuple3 (e_either e_term e_comp) (e_option e_term) e_bool))

let unlazy_as_t k t =
    let open FStarC.Class.Deq in
    match t.nbe_t with
    | Lazy (Inl {lkind=k'; blob=v}, _)
        when k =? k' ->
      FStarC.Dyn.undyn v
    | _ ->
      failwith "Not a Lazy of the expected kind (NBE)"

let e_ident : embedding I.ident =
    let embed_ident cb (se:I.ident) : t =
        mk_lazy cb se fstar_refl_ident Lazy_ident
    in
    let unembed_ident cb (t:t) : option I.ident =
        match t.nbe_t with
        | Lazy (Inl {blob=b; lkind=Lazy_ident}, _) ->
            Some (undyn b)
        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded ident: %s" (t_to_string t));
            None
    in
    mk_emb' embed_ident unembed_ident fstar_refl_ident_fv
let e_univ_name = e_ident
let e_univ_names = e_list e_univ_name

let e_universe_view =
  let embed_universe_view cb (uv:universe_view) : t =
    match uv with
    | Uv_Zero -> mkConstruct ref_Uv_Zero.fv [] []
    | Uv_Succ u ->
      mkConstruct
        ref_Uv_Succ.fv
        []
        [as_arg (embed e_universe cb u)]
    | Uv_Max us ->
      mkConstruct
        ref_Uv_Max.fv
        []
        [as_arg (embed (e_list e_universe) cb us)]
    | Uv_BVar n ->
      mkConstruct
        ref_Uv_BVar.fv
        []
        [as_arg (embed e_int cb n)]
    | Uv_Name i ->
      mkConstruct
        ref_Uv_Name.fv
        []
        [as_arg (embed e_ident cb i)]
    | Uv_Unif u ->
      mkConstruct
        ref_Uv_Unif.fv
        []
        [as_arg (mk_lazy cb u U.t_universe_uvar Lazy_universe_uvar)]
    | Uv_Unk -> mkConstruct ref_Uv_Unk.fv [] [] in

  let unembed_universe_view cb (t:t) : option universe_view =
    match t.nbe_t with
    | Construct (fv, _, []) when S.fv_eq_lid fv ref_Uv_Zero.lid -> Some Uv_Zero
    | Construct (fv, _, [u, _]) when S.fv_eq_lid fv ref_Uv_Succ.lid ->
      Option.bind (unembed e_universe cb u) (fun u -> u |> Uv_Succ |> Some)
    | Construct (fv, _, [us, _]) when S.fv_eq_lid fv ref_Uv_Max.lid ->
      Option.bind (unembed (e_list e_universe) cb us) (fun us -> us |> Uv_Max |> Some)
    | Construct (fv, _, [n, _]) when S.fv_eq_lid fv ref_Uv_BVar.lid ->
      Option.bind (unembed e_int cb n) (fun n -> n |> Uv_BVar |> Some)
    | Construct (fv, _, [i, _]) when S.fv_eq_lid fv ref_Uv_Name.lid ->
      Option.bind (unembed e_ident cb i) (fun i -> i |> Uv_Name |> Some)
    | Construct (fv, _, [u, _]) when S.fv_eq_lid fv ref_Uv_Unif.lid ->
      let u : universe_uvar = unlazy_as_t Lazy_universe_uvar u in
      u |> Uv_Unif |> Some
    | Construct (fv, _, []) when S.fv_eq_lid fv ref_Uv_Unk.lid -> Some Uv_Unk
    | _ ->
      Err.log_issue0 Err.Warning_NotEmbedded
        (Format.fmt1 "Not an embedded universe view: %s" (t_to_string t));
      None in

  mk_emb' embed_universe_view unembed_universe_view fstar_refl_universe_view_fv

let e_subst_elt =
    let embed_const cb (e:subst_elt) : t =
        match e with
        | DB (i, x) -> mkConstruct ref_DB.fv [] [as_arg (embed e_int cb i); as_arg (embed e_namedv cb x)]
        | NM (x, i) -> mkConstruct ref_NM.fv [] [as_arg (embed e_namedv cb x); as_arg (embed e_int cb i)]
        | NT (x, t) -> mkConstruct ref_NT.fv [] [as_arg (embed e_namedv cb x); as_arg (embed e_term cb t)]
        | UN (i, u) -> mkConstruct ref_UN.fv [] [as_arg (embed e_int cb i); as_arg (embed e_universe cb u)]
        | UD (n, i) -> mkConstruct ref_UD.fv [] [as_arg (embed e_univ_name cb n); as_arg (embed e_int cb i)]
    in
    let unembed_const cb (t:t) : option subst_elt =
        match t.nbe_t with
        | Construct (fv, [], [(x, _); (i, _)]) when S.fv_eq_lid fv ref_DB.lid ->
            Option.bind (unembed e_int cb i) (fun i ->
            Option.bind (unembed e_namedv cb x) (fun x ->
            Some <| DB (i, x)))
        | Construct (fv, [], [(i, _); (x, _)]) when S.fv_eq_lid fv ref_NM.lid ->
            Option.bind (unembed e_namedv cb x) (fun x ->
            Option.bind (unembed e_int cb i) (fun i ->
            Some <| NM (x, i)))
        | Construct (fv, [], [(t, _); (x, _)]) when S.fv_eq_lid fv ref_NT.lid ->
            Option.bind (unembed e_namedv cb x) (fun x ->
            Option.bind (unembed e_term cb t) (fun t ->
            Some <| NT (x, t)))
        | Construct (fv, [], [(u, _); (i, _)]) when S.fv_eq_lid fv ref_UN.lid ->
            Option.bind (unembed e_int cb i) (fun i ->
            Option.bind (unembed e_universe cb u) (fun u ->
            Some <| UN (i, u)))
        | Construct (fv, [], [(i, _); (n, _)]) when S.fv_eq_lid fv ref_UD.lid ->
            Option.bind (unembed e_univ_name cb n) (fun n ->
            Option.bind (unembed e_int cb i) (fun i ->
            Some <| UD (n, i)))
        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded vconst: %s" (t_to_string t));
            None
    in
    mk_emb' embed_const unembed_const fstar_refl_subst_elt_fv

let e_subst = e_list e_subst_elt

let e_term_view_aq aq =
    let shift (s, aqs) = (s + 1, aqs) in
    let embed_term_view cb (tv:term_view) : t =
        match tv with
        | Tv_FVar fv ->
            mkConstruct ref_Tv_FVar.fv [] [as_arg (embed e_fv cb fv)]

        | Tv_BVar bv ->
            mkConstruct ref_Tv_BVar.fv [] [as_arg (embed e_bv cb bv)]

        | Tv_Var bv ->
            mkConstruct ref_Tv_Var.fv [] [as_arg (embed e_bv cb bv)]

        | Tv_UInst (fv, us) ->
            mkConstruct ref_Tv_UInst.fv []
              [as_arg (embed e_fv cb fv);
               as_arg (embed (e_list e_universe) cb us)]

        | Tv_App (hd, a) ->
            mkConstruct ref_Tv_App.fv [] [as_arg (embed (e_term_aq aq) cb hd); as_arg (embed (e_argv_aq aq) cb a)]

        | Tv_Abs (b, t) ->
            mkConstruct ref_Tv_Abs.fv [] [as_arg (embed e_binder cb b); as_arg (embed (e_term_aq (shift aq)) cb t)]

        | Tv_Arrow (b, c) ->
            mkConstruct ref_Tv_Arrow.fv [] [as_arg (embed e_binder cb b); as_arg (embed e_comp cb c)]

        | Tv_Type u ->
            mkConstruct ref_Tv_Type.fv [] [as_arg (embed e_universe cb u)]

        | Tv_Refine (b, t) ->
            mkConstruct ref_Tv_Refine.fv [] [as_arg (embed e_binder cb b);
                                             as_arg (embed (e_term_aq (shift aq)) cb t)]

        | Tv_Const c ->
            mkConstruct ref_Tv_Const.fv [] [as_arg (embed e_vconst cb c)]

        | Tv_Uvar (u, d) ->
            mkConstruct ref_Tv_Uvar.fv [] [as_arg (embed e_int cb u); as_arg (mk_lazy cb (u,d) U.t_ctx_uvar_and_sust Lazy_uvar)]

        | Tv_Let (r, attrs, b, t1, t2) ->
            mkConstruct ref_Tv_Let.fv [] [as_arg (embed e_bool cb r);
                                   as_arg (embed (e_list e_term) cb attrs);
                                   as_arg (embed e_binder cb b);
                                   as_arg (embed (e_term_aq aq) cb t1);
                                   as_arg (embed (e_term_aq (shift aq)) cb t2)]

        | Tv_Match (t, ret_opt, brs) ->
            mkConstruct ref_Tv_Match.fv [] [
                as_arg (embed (e_term_aq aq) cb t);
                as_arg (embed e_match_returns_annotation cb ret_opt);
                as_arg (embed (e_list (e_branch_aq aq)) cb brs)]

        | Tv_AscribedT (e, t, tacopt, use_eq) ->
            mkConstruct ref_Tv_AscT.fv []
                        [as_arg (embed (e_term_aq aq) cb e);
                         as_arg (embed (e_term_aq aq) cb t);
                         as_arg (embed (e_option (e_term_aq aq)) cb tacopt);
                         as_arg (embed e_bool cb use_eq)]

        | Tv_AscribedC (e, c, tacopt, use_eq) ->
            mkConstruct ref_Tv_AscT.fv []
                        [as_arg (embed (e_term_aq aq) cb e);
                         as_arg (embed e_comp cb c);
                         as_arg (embed (e_option (e_term_aq aq)) cb tacopt);
                         as_arg (embed e_bool cb use_eq)]

        | Tv_Unknown -> mkConstruct ref_Tv_Unknown.fv [] []

        | Tv_Unsupp -> mkConstruct ref_Tv_Unsupp.fv [] []
    in
    let unembed_term_view cb (t:t) : option term_view =
        match t.nbe_t with
        | Construct (fv, _, [(b, _)]) when S.fv_eq_lid fv ref_Tv_Var.lid ->
            Option.bind (unembed e_bv cb b) (fun b ->
            Some <| Tv_Var b)

        | Construct (fv, _, [(b, _)]) when S.fv_eq_lid fv ref_Tv_BVar.lid ->
            Option.bind (unembed e_bv cb b) (fun b ->
            Some <| Tv_BVar b)

        | Construct (fv, _, [(f, _)]) when S.fv_eq_lid fv ref_Tv_FVar.lid ->
            Option.bind (unembed e_fv cb f) (fun f ->
            Some <| Tv_FVar f)

        | Construct (fv, _, [(f, _); (us, _)]) when S.fv_eq_lid fv ref_Tv_UInst.lid ->
            Option.bind (unembed e_fv cb f) (fun f ->
            Option.bind (unembed (e_list e_universe) cb us) (fun us ->
            Some <| Tv_UInst (f, us)))

        | Construct (fv, _, [(r, _); (l, _)]) when S.fv_eq_lid fv ref_Tv_App.lid ->
            Option.bind (unembed e_term cb l) (fun l ->
            Option.bind (unembed e_argv cb r) (fun r ->
            Some <| Tv_App (l, r)))

        | Construct (fv, _, [(t, _); (b, _)]) when S.fv_eq_lid fv ref_Tv_Abs.lid ->
            Option.bind (unembed e_binder cb b) (fun b ->
            Option.bind (unembed e_term cb t) (fun t ->
            Some <| Tv_Abs (b, t)))

        | Construct (fv, _, [(t, _); (b, _)]) when S.fv_eq_lid fv ref_Tv_Arrow.lid ->
            Option.bind (unembed e_binder cb b) (fun b ->
            Option.bind (unembed e_comp cb t) (fun c ->
            Some <| Tv_Arrow (b, c)))

        | Construct (fv, _, [(u, _)]) when S.fv_eq_lid fv ref_Tv_Type.lid ->
            Option.bind (unembed e_universe cb u) (fun u ->
            Some <| Tv_Type u)

        | Construct (fv, _, [(t, _); (b, _)]) when S.fv_eq_lid fv ref_Tv_Refine.lid ->
            Option.bind (unembed e_binder cb b) (fun b ->
            Option.bind (unembed e_term cb t) (fun t ->
            Some <| Tv_Refine (b, t)))

        | Construct (fv, _, [(c, _)]) when S.fv_eq_lid fv ref_Tv_Const.lid ->
            Option.bind (unembed e_vconst cb c) (fun c ->
            Some <| Tv_Const c)

        | Construct (fv, _, [(l, _); (u, _)]) when S.fv_eq_lid fv ref_Tv_Uvar.lid ->
            Option.bind (unembed e_int cb u) (fun u ->
            let ctx_u_s : ctx_uvar_and_subst = unlazy_as_t Lazy_uvar l in
            Some <| Tv_Uvar (u, ctx_u_s))

        | Construct (fv, _, [(t2, _); (t1, _); (b, _); (attrs, _); (r, _)]) when S.fv_eq_lid fv ref_Tv_Let.lid ->
            Option.bind (unembed e_bool cb r) (fun r ->
            Option.bind (unembed (e_list e_term) cb attrs) (fun attrs ->
            Option.bind (unembed e_binder cb b) (fun b ->
            Option.bind (unembed e_term cb t1) (fun t1 ->
            Option.bind (unembed e_term cb t2) (fun t2 ->
            Some <| Tv_Let (r, attrs, b, t1, t2))))))

        | Construct (fv, _, [(brs, _); (ret_opt, _); (t, _)]) when S.fv_eq_lid fv ref_Tv_Match.lid ->
            Option.bind (unembed e_term cb t) (fun t ->
            Option.bind (unembed (e_list e_branch) cb brs) (fun brs ->
            Option.bind (unembed e_match_returns_annotation cb ret_opt) (fun ret_opt ->
            Some <| Tv_Match (t, ret_opt, brs))))

        | Construct (fv, _, [(tacopt, _); (t, _); (e, _); (use_eq, _)]) when S.fv_eq_lid fv ref_Tv_AscT.lid ->
            Option.bind (unembed e_term cb e) (fun e ->
            Option.bind (unembed e_term cb t) (fun t ->
            Option.bind (unembed (e_option e_term) cb tacopt) (fun tacopt ->
            Option.bind (unembed e_bool cb use_eq) (fun use_eq ->
            Some <| Tv_AscribedT (e, t, tacopt, use_eq)))))

        | Construct (fv, _, [(tacopt, _); (c, _); (e, _); (use_eq, _)]) when S.fv_eq_lid fv ref_Tv_AscC.lid ->
            Option.bind (unembed e_term cb e) (fun e ->
            Option.bind (unembed e_comp cb c) (fun c ->
            Option.bind (unembed (e_option e_term) cb tacopt) (fun tacopt ->
            Option.bind (unembed e_bool cb use_eq) (fun use_eq ->
            Some <| Tv_AscribedC (e, c, tacopt, use_eq)))))

        | Construct (fv, _, []) when S.fv_eq_lid fv ref_Tv_Unknown.lid ->
            Some <| Tv_Unknown

        | Construct (fv, _, []) when S.fv_eq_lid fv ref_Tv_Unsupp.lid ->
            Some <| Tv_Unsupp

        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded term_view: %s" (t_to_string t));
            None
    in
    mk_emb' embed_term_view unembed_term_view fstar_refl_term_view_fv

let e_term_view = e_term_view_aq (0, [])

let e_namedv_view =
    let embed_namedv_view cb (namedvv:namedv_view) : t =
        mkConstruct ref_Mk_namedv_view.fv [] [
          as_arg (embed e_int    cb namedvv.uniq);
          as_arg (embed e_ppname cb namedvv.ppname);
          as_arg (embed e_sort   cb namedvv.sort);
        ]
    in
    let unembed_namedv_view cb (t : t) : option namedv_view =
        match t.nbe_t with
        | Construct (fv, _, [(sort, _); (ppname, _); (uniq, _)]) when S.fv_eq_lid fv ref_Mk_namedv_view.lid ->
            Option.bind (unembed e_int cb uniq) (fun uniq ->
            Option.bind (unembed e_ppname cb ppname) (fun ppname ->
            Option.bind (unembed e_sort cb sort) (fun sort ->
            let r : namedv_view = { ppname = ppname; uniq = uniq ; sort=sort } in
            Some r)))

        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded namedv_view: %s" (t_to_string t));
            None
    in
    mk_emb' embed_namedv_view unembed_namedv_view fstar_refl_namedv_view_fv

let e_bv_view =
    let embed_bv_view cb (bvv:bv_view) : t =
        mkConstruct ref_Mk_bv_view.fv [] [
          as_arg (embed e_int    cb bvv.index);
          as_arg (embed e_ppname cb bvv.ppname);
          as_arg (embed e_sort   cb bvv.sort);
        ]
    in
    let unembed_bv_view cb (t : t) : option bv_view =
        match t.nbe_t with
        | Construct (fv, _, [(sort, _); (ppname, _); (idx, _)]) when S.fv_eq_lid fv ref_Mk_bv_view.lid ->
            Option.bind (unembed e_int cb idx) (fun idx ->
            Option.bind (unembed e_ppname cb ppname) (fun ppname ->
            Option.bind (unembed e_sort cb sort) (fun sort ->
            let r : bv_view = { ppname = ppname; index = idx; sort=sort } in
            Some r)))

        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded bv_view: %s" (t_to_string t));
            None
    in
    mk_emb' embed_bv_view unembed_bv_view fstar_refl_bv_view_fv

let e_attribute  = e_term
let e_attributes = e_list e_attribute

let e_binding =
  let embed cb (b:RD.binding) : t =
    mkConstruct ref_Mk_binding.fv [] [
      as_arg (embed e_int cb b.uniq);
      as_arg (embed e_term cb b.sort);
      as_arg (embed e_ppname cb b.ppname);
    ]
  in
  let unembed cb (t:t) : option RD.binding =
    match t.nbe_t with
    | Construct (fv, _, [(ppname, _); (sort, _); (uniq, _)])
      when S.fv_eq_lid fv ref_Mk_binding.lid ->
      Option.bind (unembed e_int cb uniq) (fun uniq ->
      Option.bind (unembed e_term cb sort) (fun sort ->
      Option.bind (unembed e_ppname cb ppname) (fun ppname ->
      let r : RD.binding = {uniq=uniq; ppname=ppname; sort=sort} in
      Some r)))
  in
  mk_emb' embed unembed fstar_refl_binding_fv

let e_binder_view =
  let embed_binder_view cb (bview:binder_view) : t =
    mkConstruct ref_Mk_binder_view.fv [] [
      as_arg (embed e_term cb bview.sort);
      as_arg (embed e_aqualv cb bview.qual);
      as_arg (embed e_attributes cb bview.attrs);
      as_arg (embed e_ppname cb bview.ppname);
    ] in

  let unembed_binder_view cb (t:t) : option binder_view =
    match t.nbe_t with
    | Construct (fv, _, [(ppname, _); (attrs, _); (q, _); (sort, _)])
      when S.fv_eq_lid fv ref_Mk_binder_view.lid ->
      Option.bind (unembed e_term cb sort) (fun sort ->
      Option.bind (unembed e_aqualv cb q) (fun q ->
      Option.bind (unembed e_attributes cb attrs) (fun attrs ->
      Option.bind (unembed e_ppname cb ppname) (fun ppname ->
      let r : binder_view = {ppname=ppname; qual=q; attrs=attrs; sort=sort} in
      Some r))))

    | _ ->
      Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded binder_view: %s" (t_to_string t));
      None
    in
    mk_emb' embed_binder_view unembed_binder_view fstar_refl_binder_view_fv

let e_comp_view =
    let embed_comp_view cb (cv : comp_view) : t =
        match cv with
        | C_Total t ->
            mkConstruct ref_C_Total.fv [] [
              as_arg (embed e_term cb t)]

        | C_GTotal t ->
            mkConstruct ref_C_GTotal.fv [] [
              as_arg (embed e_term cb t)]

        | C_Lemma (pre, post, pats) ->
            mkConstruct ref_C_Lemma.fv [] [as_arg (embed e_term cb pre); as_arg (embed e_term cb post); as_arg (embed e_term cb pats)]

        | C_Eff (us, eff, res, args, decrs) ->
            mkConstruct ref_C_Eff.fv []
                [ as_arg (embed (e_list e_universe) cb us)
                ; as_arg (embed e_string_list cb eff)
                ; as_arg (embed e_term cb res)
                ; as_arg (embed (e_list e_argv) cb args)
                ; as_arg (embed (e_list e_term) cb decrs)]
    in
    let unembed_comp_view cb (t : t) : option comp_view =
        match t.nbe_t with
        | Construct (fv, _, [(t, _)])
          when S.fv_eq_lid fv ref_C_Total.lid ->
            Option.bind (unembed e_term cb t) (fun t ->
            Some <| C_Total t)

        | Construct (fv, _, [(t, _)])
          when S.fv_eq_lid fv ref_C_GTotal.lid ->
            Option.bind (unembed e_term cb t) (fun t ->
            Some <| C_GTotal t)

        | Construct (fv, _, [(post, _); (pre, _); (pats, _)]) when S.fv_eq_lid fv ref_C_Lemma.lid ->
            Option.bind (unembed e_term cb pre) (fun pre ->
            Option.bind (unembed e_term cb post) (fun post ->
            Option.bind (unembed e_term cb pats) (fun pats ->
            Some <| C_Lemma (pre, post, pats))))

        | Construct (fv, _, [(decrs, _); (args, _); (res, _); (eff, _); (us, _)])
          when S.fv_eq_lid fv ref_C_Eff.lid ->
            Option.bind (unembed (e_list e_universe) cb us) (fun us ->
            Option.bind (unembed e_string_list cb eff) (fun eff ->
            Option.bind (unembed e_term cb res) (fun res->
            Option.bind (unembed (e_list e_argv) cb args) (fun args ->
            Option.bind (unembed (e_list e_term) cb decrs) (fun decrs ->
            Some <| C_Eff (us, eff, res, args, decrs))))))

        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded comp_view: %s" (t_to_string t));
            None
    in
    mk_emb' embed_comp_view unembed_comp_view fstar_refl_comp_view_fv

let e_sigelt =
    let embed_sigelt cb (se:sigelt) : t =
        mk_lazy cb se fstar_refl_sigelt Lazy_sigelt
    in
    let unembed_sigelt cb (t:t) : option sigelt =
        match t.nbe_t with
        | Lazy (Inl {blob=b; lkind=Lazy_sigelt}, _) ->
            Some (undyn b)
        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded sigelt: %s" (t_to_string t));
            None
    in
    mk_emb' embed_sigelt unembed_sigelt fstar_refl_sigelt_fv

let e_string_list = e_list e_string

let e_ctor = e_tuple2 e_string_list e_term

let e_lb_view =
    let embed_lb_view cb (lbv:lb_view) : t =
        mkConstruct ref_Mk_lb.fv [] [as_arg (embed e_fv         cb lbv.lb_fv);
                                 as_arg (embed e_univ_names cb lbv.lb_us);
                                 as_arg (embed e_term       cb lbv.lb_typ);
                                 as_arg (embed e_term       cb lbv.lb_def)]
    in
    let unembed_lb_view cb (t : t) : option lb_view =
       match t.nbe_t with
       | Construct (fv, _, [(fv', _); (us, _); (typ, _); (def,_)])
          when S.fv_eq_lid fv ref_Mk_lb.lid ->
            Option.bind (unembed e_fv cb fv') (fun fv' ->
            Option.bind (unembed e_univ_names cb us) (fun us ->
            Option.bind (unembed e_term cb typ) (fun typ ->
            Option.bind (unembed e_term cb def) (fun def ->
            Some <|
              { lb_fv = fv'; lb_us = us; lb_typ = typ; lb_def = def }))))

        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded lb_view: %s" (t_to_string t));
            None
    in
    mk_emb' embed_lb_view unembed_lb_view fstar_refl_lb_view_fv

(* embeds as a string list *)
let e_lid : embedding I.lid =
    let embed rng lid : t =
        embed e_string_list rng (I.path_of_lid lid)
    in
    let unembed cb (t : t) : option I.lid =
        Option.map (fun p -> I.lid_of_path p Range.dummyRange) (unembed e_string_list cb t)
    in
    mk_emb embed unembed
        (fun () -> mkConstruct fstar_refl_aqualv_fv [] [])
        (fun () -> fv_as_emb_typ fstar_refl_aqualv_fv)

let e_letbinding =
    let embed_letbinding cb (lb:letbinding) : t =
        mk_lazy cb lb fstar_refl_letbinding Lazy_letbinding
    in
    let unembed_letbinding cb (t : t) : option letbinding =
         match t.nbe_t with
        | Lazy (Inl {blob=lb; lkind=Lazy_letbinding}, _) ->
            Some (undyn lb)

        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded letbinding: %s" (t_to_string t));
            None
    in
    mk_emb' embed_letbinding unembed_letbinding fstar_refl_letbinding_fv

let e_sigelt_view =
    let embed_sigelt_view cb (sev:sigelt_view) : t =
        match sev with
        | Sg_Let (r, lbs) ->
            mkConstruct ref_Sg_Let.fv [] [as_arg (embed e_bool cb r);
                                   as_arg (embed (e_list e_letbinding) cb lbs)]

        | Sg_Inductive (nm, univs, bs, t, dcs) ->
            mkConstruct ref_Sg_Inductive.fv [] [as_arg (embed e_string_list cb nm);
                                         as_arg (embed e_univ_names cb univs);
                                         as_arg (embed e_binders cb bs);
                                         as_arg (embed e_term cb t);
                                         as_arg (embed (e_list e_ctor) cb dcs)]

        | Sg_Val (nm, univs, t) ->
            mkConstruct ref_Sg_Val.fv []
                        [as_arg (embed e_string_list cb nm);
                         as_arg (embed e_univ_names cb univs);
                         as_arg (embed e_term cb t)]

        | Unk ->
            mkConstruct ref_Unk.fv [] []
    in
    let unembed_sigelt_view cb (t:t) : option sigelt_view =
        match t.nbe_t with
        | Construct (fv, _, [(dcs, _); (t, _); (bs, _); (us, _); (nm, _)]) when S.fv_eq_lid fv ref_Sg_Inductive.lid ->
            Option.bind (unembed e_string_list cb nm) (fun nm ->
            Option.bind (unembed e_univ_names cb us) (fun us ->
            Option.bind (unembed e_binders cb bs) (fun bs ->
            Option.bind (unembed e_term cb t) (fun t ->
            Option.bind (unembed (e_list e_ctor) cb dcs) (fun dcs ->
            Some <| Sg_Inductive (nm, us, bs, t, dcs))))))

        | Construct (fv, _, [(lbs, _); (r, _)]) when S.fv_eq_lid fv ref_Sg_Let.lid ->
            Option.bind (unembed e_bool cb r) (fun r ->
            Option.bind (unembed (e_list e_letbinding) cb lbs) (fun lbs ->
            Some <| Sg_Let (r, lbs)))

        | Construct (fv, _, [(t, _); (us, _); (nm, _)]) when S.fv_eq_lid fv ref_Sg_Val.lid ->
            Option.bind (unembed e_string_list cb nm) (fun nm ->
            Option.bind (unembed e_univ_names cb us) (fun us ->
            Option.bind (unembed e_term cb t) (fun t ->
            Some <| Sg_Val(nm, us, t))))

        | Construct (fv, _, []) when S.fv_eq_lid fv ref_Unk.lid ->
            Some Unk

        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded sigelt_view: %s" (t_to_string t));
            None
    in
    mk_emb' embed_sigelt_view unembed_sigelt_view fstar_refl_sigelt_view_fv

let e_name : embedding name = e_list e_string

let e_qualifier =
    let embed cb (q:RD.qualifier) : t =
        match q with
        | RD.Assumption                       -> mkConstruct ref_qual_Assumption.fv [] []
        | RD.New                              -> mkConstruct ref_qual_New.fv [] []
        | RD.Private                          -> mkConstruct ref_qual_Private.fv [] []
        | RD.Unfold_for_unification_and_vcgen -> mkConstruct ref_qual_Unfold_for_unification_and_vcgen.fv [] []
        | RD.Visible_default                  -> mkConstruct ref_qual_Visible_default.fv [] []
        | RD.Irreducible                      -> mkConstruct ref_qual_Irreducible.fv [] []
        | RD.Inline_for_extraction            -> mkConstruct ref_qual_Inline_for_extraction.fv [] []
        | RD.NoExtract                        -> mkConstruct ref_qual_NoExtract.fv [] []
        | RD.Noeq                             -> mkConstruct ref_qual_Noeq.fv [] []
        | RD.Unopteq                          -> mkConstruct ref_qual_Unopteq.fv [] []
        | RD.TotalEffect                      -> mkConstruct ref_qual_TotalEffect.fv [] []
        | RD.Logic                            -> mkConstruct ref_qual_Logic.fv [] []
        | RD.Reifiable                        -> mkConstruct ref_qual_Reifiable.fv [] []
        | RD.ExceptionConstructor             -> mkConstruct ref_qual_ExceptionConstructor.fv [] []
        | RD.HasMaskedEffect                  -> mkConstruct ref_qual_HasMaskedEffect.fv [] []
        | RD.Effect                           -> mkConstruct ref_qual_Effect.fv [] []
        | RD.OnlyName                         -> mkConstruct ref_qual_OnlyName.fv [] []
        | RD.Reflectable l ->
            mkConstruct ref_qual_Reflectable.fv [] [as_arg (embed e_name cb l)]

        | RD.Discriminator l ->
            mkConstruct ref_qual_Discriminator.fv [] [as_arg (embed e_name cb l)]

        | RD.Action l ->
            mkConstruct ref_qual_Action.fv [] [as_arg (embed e_name cb l)]

        | RD.Projector li ->
            mkConstruct ref_qual_Projector.fv [] [as_arg (embed (e_tuple2 e_name e_ident) cb li)]

        | RD.RecordType ids12 ->
            mkConstruct ref_qual_RecordType.fv [] [as_arg (embed (e_tuple2 (e_list e_ident) (e_list e_ident)) cb ids12)]

        | RD.RecordConstructor ids12 ->
            mkConstruct ref_qual_RecordConstructor.fv [] [as_arg (embed (e_tuple2 (e_list e_ident) (e_list e_ident)) cb ids12)]
    in
    let unembed cb (t:t) : option RD.qualifier =
        match t.nbe_t with
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_qual_Assumption.lid -> Some RD.Assumption
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_qual_New.lid -> Some RD.New
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_qual_Private.lid -> Some RD.Private
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_qual_Unfold_for_unification_and_vcgen.lid -> Some RD.Unfold_for_unification_and_vcgen
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_qual_Visible_default.lid -> Some RD.Visible_default
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_qual_Irreducible.lid -> Some RD.Irreducible
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_qual_Inline_for_extraction.lid -> Some RD.Inline_for_extraction
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_qual_NoExtract.lid -> Some RD.NoExtract
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_qual_Noeq.lid -> Some RD.Noeq
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_qual_Unopteq.lid -> Some RD.Unopteq
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_qual_TotalEffect.lid -> Some RD.TotalEffect
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_qual_Logic.lid -> Some RD.Logic
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_qual_Reifiable.lid -> Some RD.Reifiable
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_qual_ExceptionConstructor.lid -> Some RD.ExceptionConstructor
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_qual_HasMaskedEffect.lid -> Some RD.HasMaskedEffect
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_qual_Effect.lid -> Some RD.Effect
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_qual_OnlyName.lid -> Some RD.OnlyName

        | Construct (fv, [], [(l, _)]) when S.fv_eq_lid fv ref_qual_Reflectable.lid ->
            Option.bind (unembed e_name cb l) (fun l ->
            Some (RD.Reflectable l))

        | Construct (fv, [], [(l, _)]) when S.fv_eq_lid fv ref_qual_Discriminator.lid ->
            Option.bind (unembed e_name cb l) (fun l ->
            Some (RD.Discriminator l))

        | Construct (fv, [], [(l, _)]) when S.fv_eq_lid fv ref_qual_Action.lid ->
            Option.bind (unembed e_name cb l) (fun l ->
            Some (RD.Action l))

        | Construct (fv, [], [(li, _)]) when S.fv_eq_lid fv ref_qual_Projector.lid ->
            Option.bind (unembed (e_tuple2 e_name e_ident) cb li) (fun li ->
            Some (RD.Projector li))

        | Construct (fv, [], [(ids12, _)]) when S.fv_eq_lid fv ref_qual_RecordType.lid ->
            Option.bind (unembed (e_tuple2 (e_list e_ident) (e_list e_ident)) cb ids12) (fun ids12 ->
            Some (RD.RecordType ids12))

        | Construct (fv, [], [(ids12, _)]) when S.fv_eq_lid fv ref_qual_RecordConstructor.lid ->
            Option.bind (unembed (e_tuple2 (e_list e_ident) (e_list e_ident)) cb ids12) (fun ids12 ->
            Some (RD.RecordConstructor ids12))

        | _ ->
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded qualifier: %s" (t_to_string t));
            None
    in
    mk_emb embed unembed
        (fun () -> mkConstruct fstar_refl_qualifier_fv [] [])
        (fun () -> fv_as_emb_typ fstar_refl_qualifier_fv)

let e_qualifiers = e_list e_qualifier

let e_vconfig =
    let emb cb (o:order) : t =
      failwith "emb vconfig NBE"
    in
    let unemb cb (t:t) : option order =
      failwith "unemb vconfig NBE"
    in
    mk_emb' emb unemb (lid_as_fv PC.vconfig_lid None)
