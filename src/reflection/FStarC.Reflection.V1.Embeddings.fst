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
module FStarC.Reflection.V1.Embeddings

open FStarC.Effect
open FStarC.Reflection.V1.Data
open FStarC.Syntax.Syntax
open FStarC.Syntax.Embeddings
open FStar.Order
open FStarC.Errors

module BU      = FStarC.Util
module EMB     = FStarC.Syntax.Embeddings
module Env     = FStarC.TypeChecker.Env
module Err     = FStarC.Errors
module I       = FStarC.Ident
module List    = FStarC.List
module NBETerm = FStarC.TypeChecker.NBETerm
module O       = FStarC.Options
module PC      = FStarC.Parser.Const
module Print   = FStarC.Syntax.Print
module Range   = FStarC.Range
module RD      = FStarC.Reflection.V1.Data
module S       = FStarC.Syntax.Syntax
module SS      = FStarC.Syntax.Subst
module U       = FStarC.Syntax.Util
module Z       = FStarC.BigInt

module EmbV2 = FStarC.Reflection.V2.Embeddings

open FStarC.Dyn
open FStarC.Reflection.V1.Builtins //needed for inspect_fv, but that feels wrong
open FStarC.Reflection.V1.Constants

(*
 * embed   : from compiler to user
 * unembed : from user to compiler
 *)

let noaqs : antiquotations = (0, [])

(* -------------------------------------------------------------------------------------- *)
(* ------------------------------------- EMBEDDINGS ------------------------------------- *)
(* -------------------------------------------------------------------------------------- *)
let mk_emb f g t =
    mk_emb (fun x r _topt _norm -> f r x)
           (fun x _norm -> g x)
           (EMB.term_as_fv t)
let embed {|embedding 'a|} r (x:'a) = embed x r None id_norm_cb
let unembed {|embedding 'a|} x : option 'a = try_unembed x id_norm_cb

(* Abstract, reexport *)
let e_bv       = EmbV2.e_bv
let e_binder   = EmbV2.e_binder
let e_term_aq  = EmbV2.e_term_aq
let e_term     = EmbV2.e_term
let e_binders  = EmbV2.e_binders
let e_fv       = EmbV2.e_fv
let e_comp     = EmbV2.e_comp
let e_universe = EmbV2.e_universe

instance e_aqualv =
    let embed_aqualv (rng:Range.range) (q : aqualv) : term =
        let r =
        match q with
        | Data.Q_Explicit -> ref_Q_Explicit.t
        | Data.Q_Implicit -> ref_Q_Implicit.t
        | Data.Q_Meta t   ->
            S.mk_Tm_app ref_Q_Meta.t [S.as_arg (embed #_ #e_term rng t)]
                        Range.dummyRange
        in { r with pos = rng }
    in
    let unembed_aqualv (t : term) : option aqualv =
        let t = U.unascribe t in
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_Q_Explicit.lid -> Some Data.Q_Explicit
        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_Q_Implicit.lid -> Some Data.Q_Implicit
        | Tm_fvar fv, [(t, _)] when S.fv_eq_lid fv ref_Q_Meta.lid ->
            BU.bind_opt (unembed #_ #e_term t) (fun t ->
            Some (Data.Q_Meta t))

        | _ ->
            None
    in
    mk_emb embed_aqualv unembed_aqualv  fstar_refl_aqualv

instance e_ident : embedding RD.ident =
    e_tuple2 e_string e_range

instance e_universe_view =
  let embed_universe_view (rng:Range.range) (uv:universe_view) : term =
    match uv with
    | Uv_Zero -> ref_Uv_Zero.t
    | Uv_Succ u ->
      S.mk_Tm_app
        ref_Uv_Succ.t
        [S.as_arg (embed rng u)]
        rng
    | Uv_Max us ->
      S.mk_Tm_app
        ref_Uv_Max.t
        [S.as_arg (embed rng us)]
        rng
    | Uv_BVar n ->
      S.mk_Tm_app
        ref_Uv_BVar.t
        [S.as_arg (embed rng n)]
        rng
    | Uv_Name i ->
      S.mk_Tm_app
        ref_Uv_Name.t
        [S.as_arg (embed rng i)]
        rng
    | Uv_Unif u ->
      S.mk_Tm_app
        ref_Uv_Unif.t
        [S.as_arg (U.mk_lazy u U.t_universe_uvar Lazy_universe_uvar None)]
        rng
    | Uv_Unk ->
      ref_Uv_Unk.t in

  let unembed_universe_view (t:term) : option universe_view =
    let t = U.unascribe t in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [] when S.fv_eq_lid fv ref_Uv_Zero.lid -> Some Uv_Zero
    | Tm_fvar fv, [u, _] when S.fv_eq_lid fv ref_Uv_Succ.lid ->
      BU.bind_opt (unembed u) (fun u -> u |> Uv_Succ |> Some)
    | Tm_fvar fv, [us, _] when S.fv_eq_lid fv ref_Uv_Max.lid ->
      BU.bind_opt (unembed  us) (fun us -> us |> Uv_Max |> Some)
    | Tm_fvar fv, [n, _] when S.fv_eq_lid fv ref_Uv_BVar.lid ->
      BU.bind_opt (unembed n) (fun n -> n |> Uv_BVar |> Some)
    | Tm_fvar fv, [i, _] when S.fv_eq_lid fv ref_Uv_Name.lid ->
      BU.bind_opt (unembed  i) (fun i -> i |> Uv_Name |> Some)
    | Tm_fvar fv, [u, _] when S.fv_eq_lid fv ref_Uv_Unif.lid ->
      let u : universe_uvar = U.unlazy_as_t Lazy_universe_uvar u in
      u |> Uv_Unif |> Some
    | Tm_fvar fv, [] when S.fv_eq_lid fv ref_Uv_Unk.lid -> Some Uv_Unk
    | _ ->
      None in

  mk_emb embed_universe_view unembed_universe_view fstar_refl_universe_view

let e_env =
    let embed_env (rng:Range.range) (e:Env.env) : term =
        U.mk_lazy e fstar_refl_env Lazy_env (Some rng)
    in
    let unembed_env (t:term) : option Env.env =
        match (SS.compress t).n with
        | Tm_lazy {blob=b; lkind=Lazy_env} ->
            Some (undyn b)
        | _ ->
            None
    in
    mk_emb embed_env unembed_env fstar_refl_env

instance e_const =
    let embed_const (rng:Range.range) (c:vconst) : term =
        let r =
        match c with
        | C_Unit    -> ref_C_Unit.t
        | C_True    -> ref_C_True.t
        | C_False   -> ref_C_False.t

        | C_Int i ->
            S.mk_Tm_app ref_C_Int.t [S.as_arg (U.exp_int (Z.string_of_big_int i))]
                        Range.dummyRange
        | C_String s ->
            S.mk_Tm_app ref_C_String.t [S.as_arg (embed rng s)]
                        Range.dummyRange

        | C_Range r ->
            S.mk_Tm_app ref_C_Range.t [S.as_arg (embed rng r)]
                        Range.dummyRange

        | C_Reify -> ref_C_Reify.t

        | C_Reflect ns ->
            S.mk_Tm_app ref_C_Reflect.t [S.as_arg (embed rng ns)]
                        Range.dummyRange

        in { r with pos = rng }
    in
    let unembed_const (t:term) : option vconst =
        let t = U.unascribe t in
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_C_Unit.lid ->
            Some C_Unit

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_C_True.lid ->
            Some C_True

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_C_False.lid ->
            Some C_False

        | Tm_fvar fv, [(i, _)] when S.fv_eq_lid fv ref_C_Int.lid ->
            BU.bind_opt (unembed i) (fun i ->
            Some <| C_Int i)

        | Tm_fvar fv, [(s, _)] when S.fv_eq_lid fv ref_C_String.lid ->
            BU.bind_opt (unembed s) (fun s ->
            Some <| C_String s)

        | Tm_fvar fv, [(r, _)] when S.fv_eq_lid fv ref_C_Range.lid ->
            BU.bind_opt (unembed r) (fun r ->
            Some <| C_Range r)

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_C_Reify.lid ->
            Some <| C_Reify

        | Tm_fvar fv, [(ns, _)] when S.fv_eq_lid fv ref_C_Reflect.lid ->
            BU.bind_opt (unembed ns) (fun ns ->
            Some <| C_Reflect ns)

        | _ ->
            None
    in
    mk_emb embed_const unembed_const fstar_refl_vconst

let rec e_pattern_aq aq =
    let rec embed_pattern (rng:Range.range) (p : pattern) : term =
        match p with
        | Pat_Constant c ->
            S.mk_Tm_app ref_Pat_Constant.t [S.as_arg (embed rng c)] rng
        | Pat_Cons (fv, us_opt, ps) ->
            S.mk_Tm_app ref_Pat_Cons.t
              [S.as_arg (embed rng fv);
               S.as_arg (embed rng us_opt);
               S.as_arg (embed #_ #(e_list (e_tuple2 (e_pattern_aq aq) e_bool)) rng ps)] rng
        | Pat_Var (bv, sort) ->
            S.mk_Tm_app ref_Pat_Var.t [S.as_arg (embed #_ #e_bv rng bv); S.as_arg (embed #_ #(e_sealed e_term) rng sort)] rng
        | Pat_Dot_Term eopt ->
            S.mk_Tm_app ref_Pat_Dot_Term.t [S.as_arg (embed #_ #(e_option e_term) rng eopt)]
                        rng
    in
    let rec unembed_pattern (t : term) : option pattern =
        let t = U.unascribe t in
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [(c, _)] when S.fv_eq_lid fv ref_Pat_Constant.lid ->
            BU.bind_opt (unembed c) (fun c ->
            Some <| Pat_Constant c)

        | Tm_fvar fv, [(f, _); (us_opt, _); (ps, _)] when S.fv_eq_lid fv ref_Pat_Cons.lid ->
            BU.bind_opt (unembed f) (fun f ->
            BU.bind_opt (unembed  us_opt) (fun us_opt ->
            BU.bind_opt (unembed #_ #(e_list (e_tuple2 (e_pattern_aq aq) e_bool)) ps) (fun ps ->
            Some <| Pat_Cons (f, us_opt, ps))))

        | Tm_fvar fv, [(bv, _); (sort, _)] when S.fv_eq_lid fv ref_Pat_Var.lid ->
            BU.bind_opt (unembed #_ #e_bv bv) (fun bv ->
            BU.bind_opt (unembed #_ #(e_sealed e_term) sort) (fun sort ->
            Some <| Pat_Var (bv, sort)))

        | Tm_fvar fv, [(eopt, _)] when S.fv_eq_lid fv ref_Pat_Dot_Term.lid ->
            BU.bind_opt (unembed #_ #(e_option e_term) eopt) (fun eopt ->
            Some <| Pat_Dot_Term eopt)

        | _ ->
            None
    in
    mk_emb embed_pattern unembed_pattern fstar_refl_pattern

let e_pattern = e_pattern_aq noaqs

let e_branch = e_tuple2 e_pattern e_term
let e_argv   = e_tuple2 e_term    e_aqualv

let e_args   = e_list e_argv

let e_branch_aq aq = e_tuple2 (e_pattern_aq aq) (e_term_aq aq)
let e_argv_aq   aq = e_tuple2 (e_term_aq aq) e_aqualv

let e_match_returns_annotation =
  e_option (e_tuple2 e_binder
                     (e_tuple3 (e_either e_term e_comp) (e_option e_term) e_bool))

let e_term_view_aq aq =
    let push (s, aq) = (s+1, aq) in
    let embed_term_view (rng:Range.range) (t:term_view) : term =
        match t with
        | Tv_FVar fv ->
            S.mk_Tm_app ref_Tv_FVar.t [S.as_arg (embed rng fv)]
                        rng

        | Tv_BVar fv ->
            S.mk_Tm_app ref_Tv_BVar.t [S.as_arg (embed #_ #e_bv rng fv)]
                        rng

        | Tv_Var bv ->
            S.mk_Tm_app ref_Tv_Var.t [S.as_arg (embed #_ #e_bv rng bv)]
                        rng

        | Tv_UInst (fv, us) ->
          S.mk_Tm_app
            ref_Tv_UInst.t
            [S.as_arg (embed rng fv);
             S.as_arg (embed  rng us)]
            rng

        | Tv_App (hd, a) ->
            S.mk_Tm_app ref_Tv_App.t [S.as_arg (embed #_ #(e_term_aq aq) rng hd); S.as_arg (embed #_ #(e_argv_aq aq) rng a)]
                        rng

        | Tv_Abs (b, t) ->
            S.mk_Tm_app ref_Tv_Abs.t [S.as_arg (embed rng b); S.as_arg (embed #_ #(e_term_aq (push aq)) rng t)]
                        rng

        | Tv_Arrow (b, c) ->
            S.mk_Tm_app ref_Tv_Arrow.t [S.as_arg (embed rng b); S.as_arg (embed rng c)]
                        rng

        | Tv_Type u ->
            S.mk_Tm_app ref_Tv_Type.t [S.as_arg (embed rng u)]
                        rng

        | Tv_Refine (bv, s, t) ->
            S.mk_Tm_app ref_Tv_Refine.t [S.as_arg (embed #_ #e_bv rng bv);
                                         S.as_arg (embed #_ #(e_term_aq aq) rng s);
                                         S.as_arg (embed #_ #(e_term_aq (push aq)) rng t)]
                        rng

        | Tv_Const c ->
            S.mk_Tm_app ref_Tv_Const.t [S.as_arg (embed rng c)]
                        rng

        | Tv_Uvar (u, d) ->
            S.mk_Tm_app ref_Tv_Uvar.t
                        [S.as_arg (embed rng u);
                         S.as_arg (U.mk_lazy (u,d) U.t_ctx_uvar_and_sust Lazy_uvar None)]
                        rng

        | Tv_Let (r, attrs, b, ty, t1, t2) ->
            S.mk_Tm_app ref_Tv_Let.t [S.as_arg (embed rng r);
                                      S.as_arg (embed #_ #(e_list e_term) rng attrs);
                                      S.as_arg (embed #_ #e_bv rng b);
                                      S.as_arg (embed #_ #(e_term_aq aq) rng ty);
                                      S.as_arg (embed #_ #(e_term_aq aq) rng t1);
                                      S.as_arg (embed #_ #(e_term_aq (push aq)) rng t2)]
                        rng

        | Tv_Match (t, ret_opt, brs) ->
            S.mk_Tm_app ref_Tv_Match.t [S.as_arg (embed #_ #(e_term_aq aq) rng t);
                                        S.as_arg (embed #_ #e_match_returns_annotation rng ret_opt);
                                        S.as_arg (embed #_ #(e_list (e_branch_aq aq)) rng brs)]
                        rng

        | Tv_AscribedT (e, t, tacopt, use_eq) ->
            S.mk_Tm_app ref_Tv_AscT.t
                        [S.as_arg (embed #_ #(e_term_aq aq) rng e);
                         S.as_arg (embed #_ #(e_term_aq aq) rng t);
                         S.as_arg (embed #_ #(e_option (e_term_aq aq)) rng tacopt);
                         S.as_arg (embed rng use_eq)]
                        rng

        | Tv_AscribedC (e, c, tacopt, use_eq) ->
            S.mk_Tm_app ref_Tv_AscC.t
                        [S.as_arg (embed #_ #(e_term_aq aq) rng e);
                         S.as_arg (embed rng c);
                         S.as_arg (embed #_ #(e_option (e_term_aq aq)) rng tacopt);
                         S.as_arg (embed rng use_eq)]
                        rng

        | Tv_Unknown ->
            { ref_Tv_Unknown.t with pos = rng }

        | Tv_Unsupp ->
            { ref_Tv_Unsupp.t with pos = rng }
    in
    let unembed_term_view (t:term) : option term_view =
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [(b, _)] when S.fv_eq_lid fv ref_Tv_Var.lid ->
            BU.bind_opt (unembed #_ #e_bv b) (fun b ->
            Some <| Tv_Var b)

        | Tm_fvar fv, [(b, _)] when S.fv_eq_lid fv ref_Tv_BVar.lid ->
            BU.bind_opt (unembed #_ #e_bv b) (fun b ->
            Some <| Tv_BVar b)

        | Tm_fvar fv, [(f, _)] when S.fv_eq_lid fv ref_Tv_FVar.lid ->
            BU.bind_opt (unembed f) (fun f ->
            Some <| Tv_FVar f)

        | Tm_fvar fv, [(f, _); (us, _)]
          when S.fv_eq_lid fv ref_Tv_UInst.lid ->
          BU.bind_opt (unembed f) (fun f ->
          BU.bind_opt (unembed  us) (fun us ->
          Some <| Tv_UInst (f, us)))

        | Tm_fvar fv, [(l, _); (r, _)] when S.fv_eq_lid fv ref_Tv_App.lid ->
            BU.bind_opt (unembed #_ #e_term l) (fun l ->
            BU.bind_opt (unembed #_ #e_argv r) (fun r ->
            Some <| Tv_App (l, r)))

        | Tm_fvar fv, [(b, _); (t, _)] when S.fv_eq_lid fv ref_Tv_Abs.lid ->
            BU.bind_opt (unembed b) (fun b ->
            BU.bind_opt (unembed #_ #e_term t) (fun t ->
            Some <| Tv_Abs (b, t)))

        | Tm_fvar fv, [(b, _); (t, _)] when S.fv_eq_lid fv ref_Tv_Arrow.lid ->
            BU.bind_opt (unembed b) (fun b ->
            BU.bind_opt (unembed t) (fun c ->
            Some <| Tv_Arrow (b, c)))

        | Tm_fvar fv, [(u, _)] when S.fv_eq_lid fv ref_Tv_Type.lid ->
            BU.bind_opt (unembed u) (fun u ->
            Some <| Tv_Type u)

        | Tm_fvar fv, [(b, _); (sort, _); (t, _)] when S.fv_eq_lid fv ref_Tv_Refine.lid ->
            BU.bind_opt (unembed #_ #e_bv b) (fun b ->
            BU.bind_opt (unembed #_ #e_term sort) (fun sort ->
            BU.bind_opt (unembed #_ #e_term t) (fun t ->
            Some <| Tv_Refine (b, sort, t))))

        | Tm_fvar fv, [(c, _)] when S.fv_eq_lid fv ref_Tv_Const.lid ->
            BU.bind_opt (unembed c) (fun c ->
            Some <| Tv_Const c)

        | Tm_fvar fv, [(u, _); (l, _)] when S.fv_eq_lid fv ref_Tv_Uvar.lid ->
            BU.bind_opt (unembed u) (fun u ->
            let ctx_u_s : ctx_uvar_and_subst = U.unlazy_as_t Lazy_uvar l in
            Some <| Tv_Uvar (u, ctx_u_s))

        | Tm_fvar fv, [(r, _); (attrs, _); (b, _); (ty, _); (t1, _); (t2, _)] when S.fv_eq_lid fv ref_Tv_Let.lid ->
            BU.bind_opt (unembed r) (fun r ->
            BU.bind_opt (unembed #_ #(e_list e_term) attrs) (fun attrs ->
            BU.bind_opt (unembed #_ #e_bv b) (fun b ->
            BU.bind_opt (unembed #_ #e_term ty) (fun ty->
            BU.bind_opt (unembed #_ #e_term t1) (fun t1 ->
            BU.bind_opt (unembed #_ #e_term t2) (fun t2 ->
            Some <| Tv_Let (r, attrs, b, ty, t1, t2)))))))

        | Tm_fvar fv, [(t, _); (ret_opt, _); (brs, _)] when S.fv_eq_lid fv ref_Tv_Match.lid ->
            BU.bind_opt (unembed #_ #e_term t) (fun t ->
            BU.bind_opt (unembed #_ #e_match_returns_annotation ret_opt) (fun ret_opt ->
            BU.bind_opt (unembed #_ #(e_list e_branch) brs) (fun brs ->
            Some <| Tv_Match (t, ret_opt, brs))))

        | Tm_fvar fv, [(e, _); (t, _); (tacopt, _); (use_eq, _)] when S.fv_eq_lid fv ref_Tv_AscT.lid ->
            BU.bind_opt (unembed #_ #e_term e) (fun e ->
            BU.bind_opt (unembed #_ #e_term t) (fun t ->
            BU.bind_opt (unembed #_ #(e_option e_term) tacopt) (fun tacopt ->
            BU.bind_opt (unembed use_eq) (fun use_eq ->
            Some <| Tv_AscribedT (e, t, tacopt, use_eq)))))

        | Tm_fvar fv, [(e, _); (c, _); (tacopt, _); (use_eq, _)] when S.fv_eq_lid fv ref_Tv_AscC.lid ->
            BU.bind_opt (unembed #_ #e_term e) (fun e ->
            BU.bind_opt (unembed #_ #e_comp c) (fun c ->
            BU.bind_opt (unembed #_ #(e_option e_term) tacopt) (fun tacopt ->
            BU.bind_opt (unembed use_eq) (fun use_eq ->
            Some <| Tv_AscribedC (e, c, tacopt, use_eq)))))

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_Tv_Unknown.lid ->
            Some <| Tv_Unknown

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_Tv_Unsupp.lid ->
            Some <| Tv_Unsupp

        | _ ->
            None
    in
    mk_emb embed_term_view unembed_term_view fstar_refl_term_view

let e_term_view = e_term_view_aq noaqs

(* embeds as a string list *)
// instance e_lid : embedding I.lid =
//     let embed rng lid : term =
//         embed rng (I.path_of_lid lid)
//     in
//     let unembed t : option I.lid =
//         BU.map_opt (unembed t) (fun p -> I.lid_of_path p t.pos)
//     in
//     EMB.mk_emb_full (fun x r _ _ -> embed r x)
//                (fun x _ -> unembed x)
//                (fun () -> t_list_of t_string)
//                I.string_of_lid
//                (fun () -> ET_abstract)

let e_name = e_list e_string

instance e_bv_view =
    let embed_bv_view (rng:Range.range) (bvv:bv_view) : term =
        S.mk_Tm_app ref_Mk_bv.t [S.as_arg (embed #_ #(e_sealed e_string) rng bvv.bv_ppname);
                                 S.as_arg (embed rng bvv.bv_index)]
                    rng
    in
    let unembed_bv_view (t : term) : option bv_view =
        let t = U.unascribe t in
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [(nm, _); (idx, _)] when S.fv_eq_lid fv ref_Mk_bv.lid ->
            BU.bind_opt (unembed #_ #(e_sealed e_string) nm) (fun nm ->
            BU.bind_opt (unembed idx) (fun idx ->
            Some <| { bv_ppname = nm ; bv_index = idx }))

        | _ ->
            None
    in
    mk_emb embed_bv_view unembed_bv_view fstar_refl_bv_view


let e_attribute  = e_term
let e_attributes = e_list e_attribute

instance e_binder_view =
  let embed_binder_view (rng:Range.range) (bview:binder_view) : term =
    S.mk_Tm_app ref_Mk_binder.t [S.as_arg (embed #_ #e_bv rng bview.binder_bv);
                                 S.as_arg (embed rng bview.binder_qual);
                                 S.as_arg (embed #_ #e_attributes rng bview.binder_attrs);
                                 S.as_arg (embed #_ #e_term rng bview.binder_sort)]
                rng in

  let unembed_binder_view (t:term) : option binder_view =
    let t = U.unascribe t in
    let hd, args = U.head_and_args t in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [(bv, _); (q, _); (attrs, _); (sort, _)]
      when S.fv_eq_lid fv ref_Mk_binder.lid ->
      BU.bind_opt (unembed #_ #e_bv bv) (fun bv ->
      BU.bind_opt (unembed q) (fun q ->
      BU.bind_opt (unembed #_ #e_attributes attrs) (fun attrs ->
      BU.bind_opt (unembed #_ #e_term sort) (fun sort ->
      Some <| RD.({ binder_bv=bv;binder_qual=q; binder_attrs=attrs; binder_sort = sort})))))

    | _ ->
      None in

  mk_emb embed_binder_view unembed_binder_view fstar_refl_binder_view

instance e_comp_view =
    let embed_comp_view (rng:Range.range) (cv : comp_view) : term =
        match cv with
        | C_Total t ->
            S.mk_Tm_app ref_C_Total.t [S.as_arg (embed #_ #e_term rng t)]
                        rng

        | C_GTotal t ->
            S.mk_Tm_app ref_C_GTotal.t [S.as_arg (embed #_ #e_term rng t)]
                        rng

        | C_Lemma (pre, post, pats) ->
            S.mk_Tm_app ref_C_Lemma.t [S.as_arg (embed #_ #e_term rng pre);
                                       S.as_arg (embed #_ #e_term rng post);
                                       S.as_arg (embed #_ #e_term rng pats)]
                        rng

        | C_Eff (us, eff, res, args, decrs) ->
            S.mk_Tm_app ref_C_Eff.t
                [ S.as_arg (embed rng us)
                ; S.as_arg (embed rng eff)
                ; S.as_arg (embed #_ #e_term rng res)
                ; S.as_arg (embed #_ #(e_list e_argv) rng args)
                ; S.as_arg (embed #_ #(e_list e_term) rng decrs)] rng


    in
    let unembed_comp_view (t : term) : option comp_view =
        let t = U.unascribe t in
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [(t, _)]
          when S.fv_eq_lid fv ref_C_Total.lid ->
            BU.bind_opt (unembed #_ #e_term t) (fun t ->
            Some <| C_Total t)

        | Tm_fvar fv, [(t, _)]
          when S.fv_eq_lid fv ref_C_GTotal.lid ->
            BU.bind_opt (unembed #_ #e_term t) (fun t ->
            Some <| C_GTotal t)

        | Tm_fvar fv, [(pre, _); (post, _); (pats, _)] when S.fv_eq_lid fv ref_C_Lemma.lid ->
            BU.bind_opt (unembed #_ #e_term pre) (fun pre ->
            BU.bind_opt (unembed #_ #e_term post) (fun post ->
            BU.bind_opt (unembed #_ #e_term pats) (fun pats ->
            Some <| C_Lemma (pre, post, pats))))

        | Tm_fvar fv, [(us, _); (eff, _); (res, _); (args, _); (decrs, _)]
                when S.fv_eq_lid fv ref_C_Eff.lid ->
            BU.bind_opt (unembed  us) (fun us ->
            BU.bind_opt (unembed eff) (fun eff ->
            BU.bind_opt (unembed #_ #e_term res)   (fun res->
            BU.bind_opt (unembed #_ #(e_list e_argv) args)  (fun args ->
            BU.bind_opt (unembed #_ #(e_list e_term) decrs)  (fun decrs ->
            Some <| C_Eff (us, eff, res, args, decrs))))))

        | _ ->
            None
    in
    mk_emb embed_comp_view unembed_comp_view fstar_refl_comp_view


(* TODO: move to, Syntax.Embeddings or somewhere better even *)
instance e_sigelt =
    let embed_sigelt (rng:Range.range) (se:sigelt) : term =
        U.mk_lazy se fstar_refl_sigelt Lazy_sigelt (Some rng)
    in
    let unembed_sigelt (t:term) : option sigelt =
        match (SS.compress t).n with
        | Tm_lazy {blob=b; lkind=Lazy_sigelt} ->
            Some (undyn b)
        | _ ->
            None
    in
    mk_emb embed_sigelt unembed_sigelt fstar_refl_sigelt

let e_univ_name =
    set_type fstar_refl_univ_name e_ident

let e_lb_view =
    let embed_lb_view (rng:Range.range) (lbv:lb_view) : term =
        S.mk_Tm_app ref_Mk_lb.t [S.as_arg (embed rng lbv.lb_fv);
                                 S.as_arg (embed rng lbv.lb_us);
                                 S.as_arg (embed #_ #e_term rng lbv.lb_typ);
                                 S.as_arg (embed #_ #e_term rng lbv.lb_def)]
                    rng
    in
    let unembed_lb_view (t : term) : option lb_view =
        let t = U.unascribe t in
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [(fv', _); (us, _); (typ, _); (def,_)]
          when S.fv_eq_lid fv ref_Mk_lb.lid ->
            BU.bind_opt (unembed fv') (fun fv' ->
            BU.bind_opt (unembed us) (fun us ->
            BU.bind_opt (unembed #_ #e_term typ) (fun typ ->
            BU.bind_opt (unembed #_ #e_term def) (fun def ->
            Some <|
              { lb_fv = fv'; lb_us = us; lb_typ = typ; lb_def = def }))))

        | _ ->
            None
    in
    mk_emb embed_lb_view unembed_lb_view fstar_refl_lb_view

let e_letbinding =
    let embed_letbinding (rng:Range.range) (lb:letbinding) : term =
        U.mk_lazy lb fstar_refl_letbinding Lazy_letbinding (Some rng)
    in
    let unembed_letbinding (t : term) : option letbinding =
        match (SS.compress t).n with
        | Tm_lazy {blob=lb; lkind=Lazy_letbinding} ->
            Some (undyn lb)
        | _ ->
            None
    in
    mk_emb embed_letbinding unembed_letbinding fstar_refl_letbinding

let e_ctor : embedding RD.ctor = e_tuple2 (e_list e_string) e_term

instance e_sigelt_view =
    let embed_sigelt_view (rng:Range.range) (sev:sigelt_view) : term =
        match sev with
        | Sg_Let (r, lbs) ->
            S.mk_Tm_app ref_Sg_Let.t
                        [S.as_arg (embed rng r);
                         S.as_arg (embed rng lbs)]
                        rng

        | Sg_Inductive (nm, univs, bs, t, dcs) ->
            S.mk_Tm_app ref_Sg_Inductive.t
                        [S.as_arg (embed rng nm);
                            S.as_arg (embed rng univs);
                            S.as_arg (embed rng bs);
                            S.as_arg (embed #_ #e_term rng t);
                            S.as_arg (embed #_ #(e_list e_ctor) rng dcs)]
                        rng

        | Sg_Val (nm, univs, t) ->
            S.mk_Tm_app ref_Sg_Val.t
                        [S.as_arg (embed rng nm);
                         S.as_arg (embed rng univs);
                         S.as_arg (embed #_ #e_term rng t)]
                        rng

        | Unk ->
            { ref_Unk.t with pos = rng }
    in
    let unembed_sigelt_view (t:term) : option sigelt_view =
        let t = U.unascribe t in
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [(nm, _); (us, _); (bs, _); (t, _); (dcs, _)] when S.fv_eq_lid fv ref_Sg_Inductive.lid ->
            BU.bind_opt (unembed nm) (fun nm ->
            BU.bind_opt (unembed us) (fun us ->
            BU.bind_opt (unembed bs) (fun bs ->
            BU.bind_opt (unembed #_ #e_term t) (fun t ->
            BU.bind_opt (unembed #_ #(e_list e_ctor) dcs) (fun dcs ->
            Some <| Sg_Inductive (nm, us, bs, t, dcs))))))

        | Tm_fvar fv, [(r, _); (lbs, _)] when S.fv_eq_lid fv ref_Sg_Let.lid ->
            BU.bind_opt (unembed r) (fun r ->
            BU.bind_opt (unembed lbs) (fun lbs ->
            Some <| Sg_Let (r, lbs)))

        | Tm_fvar fv, [(nm, _); (us, _); (t, _)] when S.fv_eq_lid fv ref_Sg_Val.lid ->
            BU.bind_opt (unembed nm) (fun nm ->
            BU.bind_opt (unembed us) (fun us ->
            BU.bind_opt (unembed #_ #e_term t) (fun t ->
            Some <| Sg_Val (nm, us, t))))

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_Unk.lid ->
            Some Unk

        | _  ->
            None
    in
    mk_emb embed_sigelt_view unembed_sigelt_view fstar_refl_sigelt_view

let e_qualifier =
    let embed (rng:Range.range) (q:RD.qualifier) : term =
        let r =
        match q with
        | RD.Assumption                       -> ref_qual_Assumption.t
        | RD.InternalAssumption               -> ref_qual_InternalAssumption.t
        | RD.New                              -> ref_qual_New.t
        | RD.Private                          -> ref_qual_Private.t
        | RD.Unfold_for_unification_and_vcgen -> ref_qual_Unfold_for_unification_and_vcgen.t
        | RD.Visible_default                  -> ref_qual_Visible_default.t
        | RD.Irreducible                      -> ref_qual_Irreducible.t
        | RD.Inline_for_extraction            -> ref_qual_Inline_for_extraction.t
        | RD.NoExtract                        -> ref_qual_NoExtract.t
        | RD.Noeq                             -> ref_qual_Noeq.t
        | RD.Unopteq                          -> ref_qual_Unopteq.t
        | RD.TotalEffect                      -> ref_qual_TotalEffect.t
        | RD.Logic                            -> ref_qual_Logic.t
        | RD.Reifiable                        -> ref_qual_Reifiable.t
        | RD.ExceptionConstructor             -> ref_qual_ExceptionConstructor.t
        | RD.HasMaskedEffect                  -> ref_qual_HasMaskedEffect.t
        | RD.Effect                           -> ref_qual_Effect.t
        | RD.OnlyName                         -> ref_qual_OnlyName.t
        | RD.Reflectable l ->
            S.mk_Tm_app ref_qual_Reflectable.t [S.as_arg (embed rng l)]
                        Range.dummyRange

        | RD.Discriminator l ->
            S.mk_Tm_app ref_qual_Discriminator.t [S.as_arg (embed rng l)]
                        Range.dummyRange

        | RD.Action l ->
            S.mk_Tm_app ref_qual_Action.t [S.as_arg (embed rng l)]
                        Range.dummyRange

        | RD.Projector (l, i) ->
            S.mk_Tm_app ref_qual_Projector.t [S.as_arg (embed rng (l, i))]
                        Range.dummyRange

        | RD.RecordType (ids1, ids2) ->
            S.mk_Tm_app ref_qual_RecordType.t [S.as_arg (embed rng (ids1, ids2))]
                        Range.dummyRange

        | RD.RecordConstructor (ids1, ids2) ->
            S.mk_Tm_app ref_qual_RecordConstructor.t [S.as_arg (embed rng (ids1, ids2))]
                        Range.dummyRange

        in { r with pos = rng }
    in
    let unembed (t: term) : option RD.qualifier =
        let t = U.unascribe t in
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_qual_Assumption.lid ->
             Some RD.Assumption

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_qual_InternalAssumption.lid ->
             Some RD.InternalAssumption

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_qual_New.lid ->
             Some RD.New

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_qual_Private.lid ->
              Some RD.Private

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_qual_Unfold_for_unification_and_vcgen.lid ->
              Some RD.Unfold_for_unification_and_vcgen

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_qual_Visible_default.lid ->
              Some RD.Visible_default

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_qual_Irreducible.lid ->
              Some RD.Irreducible

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_qual_Inline_for_extraction.lid ->
              Some RD.Inline_for_extraction

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_qual_NoExtract.lid ->
              Some RD.NoExtract

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_qual_Noeq.lid ->
              Some RD.Noeq

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_qual_Unopteq.lid ->
              Some RD.Unopteq

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_qual_TotalEffect.lid ->
              Some RD.TotalEffect

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_qual_Logic.lid ->
              Some RD.Logic

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_qual_Reifiable.lid ->
              Some RD.Reifiable

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_qual_ExceptionConstructor.lid ->
              Some RD.ExceptionConstructor

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_qual_HasMaskedEffect.lid ->
              Some RD.HasMaskedEffect

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_qual_Effect.lid ->
              Some RD.Effect

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_qual_OnlyName.lid ->
              Some RD.OnlyName

        | Tm_fvar fv, [(l, _)] when S.fv_eq_lid fv ref_qual_Reflectable.lid ->
            BU.bind_opt (unembed l) (fun l ->
            Some <| RD.Reflectable l)

        | Tm_fvar fv, [(l, _)] when S.fv_eq_lid fv ref_qual_Discriminator.lid ->
            BU.bind_opt (unembed l) (fun l ->
            Some <| RD.Discriminator l)

        | Tm_fvar fv, [(l, _)] when S.fv_eq_lid fv ref_qual_Action.lid ->
            BU.bind_opt (unembed l) (fun l ->
            Some <| RD.Action l)

        | Tm_fvar fv, [(payload, _)] when S.fv_eq_lid fv ref_qual_Projector.lid ->
            BU.bind_opt (unembed payload) (fun (l, i) ->
            Some <| RD.Projector (l, i))

        | Tm_fvar fv, [(payload, _)] when S.fv_eq_lid fv ref_qual_RecordType.lid ->
            BU.bind_opt (unembed payload) (fun (ids1, ids2) ->
            Some <| RD.RecordType (ids1, ids2))

        | Tm_fvar fv, [(payload, _)] when S.fv_eq_lid fv ref_qual_RecordConstructor.lid ->
            BU.bind_opt (unembed payload) (fun (ids1, ids2) ->
            Some <| RD.RecordConstructor (ids1, ids2))

        | _ ->
            None
    in
    mk_emb embed unembed fstar_refl_qualifier

let e_qualifiers = e_list e_qualifier

(* -------------------------------------------------------------------------------------- *)
(* ------------------------------------- UNFOLDINGS ------------------------------------- *)
(* -------------------------------------------------------------------------------------- *)


(* Note that most of these are never needed during normalization, since
 * the types are abstract.
 *)

let unfold_lazy_bv  (i : lazyinfo) : term =
    let bv : bv = undyn i.blob in
    S.mk_Tm_app fstar_refl_pack_bv.t [S.as_arg (embed i.rng (inspect_bv bv))]
                i.rng

let unfold_lazy_binder (i : lazyinfo) : term =
    let binder : binder = undyn i.blob in
    S.mk_Tm_app fstar_refl_pack_binder.t [S.as_arg (embed i.rng (inspect_binder binder))]
                i.rng

let unfold_lazy_letbinding (i : lazyinfo) : term =
    let lb : letbinding = undyn i.blob in
    let lbv = inspect_lb lb in
    S.mk_Tm_app fstar_refl_pack_lb.t
        [
            S.as_arg (embed i.rng lbv.lb_fv);
            S.as_arg (embed i.rng lbv.lb_us);
            S.as_arg (embed #_ #e_term i.rng lbv.lb_typ);
            S.as_arg (embed #_ #e_term i.rng lbv.lb_def)
        ]
        i.rng

let unfold_lazy_fvar (i : lazyinfo) : term =
    let fv : fv = undyn i.blob in
    S.mk_Tm_app fstar_refl_pack_fv.t [S.as_arg (embed i.rng (inspect_fv fv))]
                i.rng

let unfold_lazy_comp (i : lazyinfo) : term =
    let comp : comp = undyn i.blob in
    S.mk_Tm_app fstar_refl_pack_comp.t [S.as_arg (embed i.rng (inspect_comp comp))]
                i.rng

let unfold_lazy_env (i : lazyinfo) : term =
    (* Not needed, metaprograms never see concrete environments. *)
    U.exp_unit

let unfold_lazy_optionstate (i : lazyinfo) : term =
    (* Not needed, metaprograms never see concrete optionstates . *)
    U.exp_unit

let unfold_lazy_sigelt (i : lazyinfo) : term =
    let sigelt : sigelt = undyn i.blob in
    S.mk_Tm_app fstar_refl_pack_sigelt.t [S.as_arg (embed i.rng (inspect_sigelt sigelt))]
                i.rng

let unfold_lazy_universe (i : lazyinfo) : term =
    let u : universe = undyn i.blob in
    S.mk_Tm_app fstar_refl_pack_universe.t [S.as_arg (embed i.rng (inspect_universe u))]
                i.rng
