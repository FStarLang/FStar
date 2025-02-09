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
module FStarC.Reflection.V2.Embeddings

open FStarC.Effect
open FStarC.Reflection.V2.Data
open FStarC.Syntax.Syntax
open FStarC.Syntax.Embeddings
open FStar.Order
open FStarC.Errors

module BU      = FStarC.Util
module EMB     = FStarC.Syntax.Embeddings
module I       = FStarC.Ident
module List    = FStarC.List
module Range   = FStarC.Range
module RD      = FStarC.Reflection.V2.Data
module S       = FStarC.Syntax.Syntax // TODO: remove, it's open
module SS      = FStarC.Syntax.Subst
module U       = FStarC.Syntax.Util
module Z       = FStarC.BigInt

open FStarC.Reflection.V2.Builtins //needed for inspect_fv, but that feels wrong
open FStarC.Dyn
open FStarC.Syntax.Embeddings.AppEmb
open FStarC.Class.Monad

(* We only use simple embeddings here *)
let mk_emb f g t =
    mk_emb (fun x r _topt _norm -> f r x)
           (fun x _norm -> g x)
           (term_as_fv t)
let embed {|embedding 'a|} r (x:'a) = embed x r None id_norm_cb
let try_unembed {|embedding 'a|} x : option 'a = try_unembed x id_norm_cb

open FStarC.Reflection.V2.Constants

let curry f x y = f (x,y)
let curry3 f x y z = f (x,y,z)
let curry4 f x y z w = f (x,y,z,w)
let curry5 f x y z w v = f (x,y,z,w,v)

let head_fv_and_args (t : term) : option (fv & args) =
  let t = U.unascribe t in
  let hd, args = U.head_and_args t in
  match (U.un_uinst hd).n with
  | Tm_fvar fv -> Some (fv, args)
  | _ -> None

let noaqs : antiquotations = (0, [])

(* -------------------------------------------------------------------------------------- *)
(* ------------------------------------- EMBEDDINGS ------------------------------------- *)
(* -------------------------------------------------------------------------------------- *)

(* The lazy embeddings: just embedding whatever value as a blob inside a Tm_Lazy node. *)
let e_bv                 : embedding bv                 = EMB.e_lazy Lazy_bv fstar_refl_bv
let e_namedv             : embedding namedv             = EMB.e_lazy Lazy_namedv fstar_refl_namedv
let e_binder             : embedding binder             = EMB.e_lazy Lazy_binder fstar_refl_binder
let e_fv                 : embedding fv                 = EMB.e_lazy Lazy_fvar fstar_refl_fv
let e_comp               : embedding comp               = EMB.e_lazy Lazy_comp fstar_refl_comp
let e_universe           : embedding universe           = EMB.e_lazy Lazy_universe fstar_refl_universe
let e_ident              : embedding I.ident            = EMB.e_lazy Lazy_ident fstar_refl_ident
let e_env                : embedding env                = EMB.e_lazy Lazy_env fstar_refl_env
let e_sigelt             : embedding sigelt             = EMB.e_lazy Lazy_sigelt fstar_refl_sigelt
let e_letbinding         : embedding letbinding         = EMB.e_lazy Lazy_letbinding fstar_refl_letbinding

instance e_ctx_uvar_and_subst : embedding ctx_uvar_and_subst = EMB.e_lazy Lazy_uvar fstar_refl_ctx_uvar_and_subst
instance e_universe_uvar      : embedding universe_uvar      = EMB.e_lazy Lazy_universe_uvar fstar_refl_universe_uvar

let rec mapM_opt (f : ('a -> option 'b)) (l : list 'a) : option (list 'b) =
    match l with
    | [] -> Some []
    | x::xs ->
        BU.bind_opt (f x) (fun x ->
        BU.bind_opt (mapM_opt f xs) (fun xs ->
        Some (x :: xs)))

let e_term_aq aq =
    let embed_term (rng:Range.range) (t:term) : term =
        let qi = { qkind = Quote_static; antiquotations = aq } in
        S.mk (Tm_quoted (t, qi)) rng
    in
    let rec unembed_term (t:term) : option term =
        let apply_antiquotations (t:term) (aq:antiquotations) : option term =
            let shift, aqs = aq in
            let aqs = List.rev aqs in
            // Try to unembed all antiquotations
            BU.bind_opt (mapM_opt unembed_term aqs) (fun aq_ts ->
            // Create a substitution of the DB indices of t for the antiquotations
            (* let n = List.length aq_ts - 1 in *)
            let subst_open, subst =
               aq_ts
               |> List.mapi (fun i at ->
                    let x = S.new_bv None S.t_term in
                    DB(shift+i, x), NT (x, at))
               |> List.unzip
            in

            // Substitute and return
            Some (SS.subst subst <| SS.subst subst_open t))
        in
        let t = U.unmeta t in
        match (SS.compress t).n with
        | Tm_quoted (tm, qi) ->
            apply_antiquotations tm qi.antiquotations
        | _ -> None
    in
    mk_emb embed_term unembed_term S.t_term

let e_term = e_term_aq noaqs

let e_sort   : embedding (Sealed.sealed term)   = e_sealed e_term
let e_ppname : embedding ppname_t = e_sealed e_string

let e_aqualv =
    let embed_aqualv (rng:Range.range) (q : aqualv) : term =
      let r =
      match q with
      | Data.Q_Explicit -> ref_Q_Explicit.t
      | Data.Q_Implicit -> ref_Q_Implicit.t
      | Data.Q_Equality -> ref_Q_Equality.t
      | Data.Q_Meta t ->
          S.mk_Tm_app ref_Q_Meta.t [S.as_arg (embed #_ #e_term rng t)]
                      Range.dummyRange
      in { r with pos = rng }
    in
    let unembed_aqualv (t : term) : option aqualv =
      let? fv, args = head_fv_and_args t in
      match () with
      | _ when S.fv_eq_lid fv ref_Q_Explicit.lid -> run args (pure Data.Q_Explicit)
      | _ when S.fv_eq_lid fv ref_Q_Implicit.lid -> run args (pure Data.Q_Implicit)
      | _ when S.fv_eq_lid fv ref_Q_Equality.lid -> run args (pure Data.Q_Equality)
      | _ when S.fv_eq_lid fv ref_Q_Meta.lid -> run args (Data.Q_Meta <$$> e_term)
      | _ -> None
    in
    mk_emb embed_aqualv unembed_aqualv fstar_refl_aqualv

let e_binders = e_list e_binder

let e_universe_view =
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
        [S.as_arg (embed rng u)]
        rng
    | Uv_Unk ->
      ref_Uv_Unk.t in

  let unembed_universe_view (t:term) : option universe_view =
    let? fv, args = head_fv_and_args t in
    match () with
    | _ when S.fv_eq_lid fv ref_Uv_Zero.lid  -> run args (pure Uv_Zero)
    | _ when S.fv_eq_lid fv ref_Uv_Succ.lid  -> run args (Uv_Succ <$$> e_universe)
    | _ when S.fv_eq_lid fv ref_Uv_Max.lid   -> run args (Uv_Max <$$> e_list e_universe)
    | _ when S.fv_eq_lid fv ref_Uv_BVar.lid  -> run args (Uv_BVar <$$> e_int)
    | _ when S.fv_eq_lid fv ref_Uv_Name.lid  -> run args (Uv_Name <$$> e_ident)
    | _ when S.fv_eq_lid fv ref_Uv_Unif.lid  -> run args (Uv_Unif <$$> e_universe_uvar)
    | _ when S.fv_eq_lid fv ref_Uv_Unk.lid -> run args (pure Uv_Unk)
    | _ -> None
  in

  mk_emb embed_universe_view unembed_universe_view fstar_refl_universe_view

let e_vconst =
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

        | C_Real s ->
            S.mk_Tm_app ref_C_Real.t [S.as_arg (embed rng s)]
                        Range.dummyRange

        in { r with pos = rng }
    in
    let unembed_const (t:term) : option vconst =
      let? fv, args = head_fv_and_args t in
      match () with
      | _ when S.fv_eq_lid fv ref_C_Unit.lid -> run args (pure C_Unit)
      | _ when S.fv_eq_lid fv ref_C_True.lid -> run args (pure C_True)
      | _ when S.fv_eq_lid fv ref_C_False.lid -> run args (pure C_False)
      | _ when S.fv_eq_lid fv ref_C_Int.lid -> run args (C_Int <$$> e_int)
      | _ when S.fv_eq_lid fv ref_C_String.lid -> run args (C_String <$$> e_string)
      | _ when S.fv_eq_lid fv ref_C_Range.lid -> run args (C_Range <$$> e_range)
      | _ when S.fv_eq_lid fv ref_C_Reify.lid -> run args (pure C_Reify)
      | _ when S.fv_eq_lid fv ref_C_Reflect.lid -> run args (C_Reflect <$$> e_string_list)
      | _ when S.fv_eq_lid fv ref_C_Real.lid -> run args (C_Real <$$> e_string)
      | _ -> None
    in
    mk_emb embed_const unembed_const fstar_refl_vconst

let rec e_pattern_aq aq =
    let rec embed_pattern (rng:Range.range) (p : pattern) : term =
        match p with
        | Pat_Constant c ->
            S.mk_Tm_app ref_Pat_Constant.t [S.as_arg (embed rng c)] rng
        | Pat_Cons head univs subpats ->
            S.mk_Tm_app ref_Pat_Cons.t
              [S.as_arg (embed rng head);
               S.as_arg (embed rng univs);
               S.as_arg (embed #_ #(e_list (e_tuple2 (e_pattern_aq aq) e_bool)) rng subpats)] rng
        | Pat_Var sort ppname ->
            S.mk_Tm_app ref_Pat_Var.t [
              S.as_arg (embed #_ #e_sort rng sort);
              S.as_arg (embed rng ppname);
            ] rng
        | Pat_Dot_Term eopt ->
            S.mk_Tm_app ref_Pat_Dot_Term.t [S.as_arg (embed #_ #(e_option e_term) rng eopt)]
                        rng
    in
    let rec unembed_pattern (t : term) : option pattern =
        let? fv, args = head_fv_and_args t in
        match () with
        | _ when S.fv_eq_lid fv ref_Pat_Constant.lid ->
            run args (Pat_Constant <$$> e_vconst)

        | _ when S.fv_eq_lid fv ref_Pat_Cons.lid ->
            run args (Pat_Cons <$$> e_fv <**> e_option (e_list e_universe) <**> e_list (e_tuple2 (e_pattern_aq aq) e_bool))

        | _ when S.fv_eq_lid fv ref_Pat_Var.lid ->
            run args (Pat_Var <$$> e_sort <**> e_ppname)

        | _ when S.fv_eq_lid fv ref_Pat_Dot_Term.lid ->
            run args (Pat_Dot_Term <$$> e_option e_term)

        | _ -> None
    in
    mk_emb embed_pattern unembed_pattern fstar_refl_pattern

let e_pattern = e_pattern_aq noaqs

let e_branch = e_tuple2 e_pattern e_term
let e_argv   = e_tuple2 e_term    e_aqualv

let e_args   = e_list e_argv

let e_branch_aq aq = e_tuple2 (e_pattern_aq aq) (e_term_aq aq)
let e_argv_aq   aq = e_tuple2 (e_term_aq aq) e_aqualv

instance e_match_returns_annotation =
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
            S.mk_Tm_app ref_Tv_Var.t [S.as_arg (embed #_ #e_namedv rng bv)]
                        rng

        | Tv_UInst (fv, us) ->
          S.mk_Tm_app
            ref_Tv_UInst.t
            [S.as_arg (embed rng fv);
             S.as_arg (embed rng us)]
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

        | Tv_Refine (b, t) ->
            S.mk_Tm_app ref_Tv_Refine.t [S.as_arg (embed rng b);
                                         S.as_arg (embed #_ #(e_term_aq (push aq)) rng t)]
                        rng

        | Tv_Const c ->
            S.mk_Tm_app ref_Tv_Const.t [S.as_arg (embed rng c)]
                        rng

        | Tv_Uvar (u, ctx_u) ->
            S.mk_Tm_app ref_Tv_Uvar.t
                        [S.as_arg (embed rng u);
                         S.as_arg (embed rng ctx_u)]
                        rng

        | Tv_Let (r, attrs, b, t1, t2) ->
            S.mk_Tm_app ref_Tv_Let.t [S.as_arg (embed rng r);
                                      S.as_arg (embed #_ #(e_list e_term) rng attrs);
                                      S.as_arg (embed rng b);
                                      S.as_arg (embed #_ #(e_term_aq aq) rng t1);
                                      S.as_arg (embed #_ #(e_term_aq (push aq)) rng t2)]
                        rng

        | Tv_Match (t, ret_opt, brs) ->
            S.mk_Tm_app ref_Tv_Match.t [S.as_arg (embed #_ #(e_term_aq aq) rng t);
                                        S.as_arg (embed rng ret_opt);
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
        let? fv, args = head_fv_and_args t in
        let xTv_Let a b c d e = Tv_Let (a,b,c,d,e) in
        match () with
        | _ when S.fv_eq_lid fv ref_Tv_FVar.lid -> run args (Tv_FVar <$$> e_fv)
        | _ when S.fv_eq_lid fv ref_Tv_BVar.lid -> run args (Tv_BVar <$$> e_bv)
        | _ when S.fv_eq_lid fv ref_Tv_Var.lid -> run args (Tv_Var <$$> e_namedv)
        | _ when S.fv_eq_lid fv ref_Tv_UInst.lid -> run args (curry Tv_UInst <$$> e_fv <**> e_list e_universe)
        | _ when S.fv_eq_lid fv ref_Tv_App.lid -> run args (curry Tv_App <$$> e_term_aq aq <**> e_argv_aq aq)
        | _ when S.fv_eq_lid fv ref_Tv_Abs.lid -> run args (curry Tv_Abs <$$> e_binder <**> e_term_aq (push aq))
        | _ when S.fv_eq_lid fv ref_Tv_Arrow.lid -> run args (curry Tv_Arrow <$$> e_binder <**> e_comp)
        | _ when S.fv_eq_lid fv ref_Tv_Type.lid -> run args (Tv_Type <$$> e_universe)
        | _ when S.fv_eq_lid fv ref_Tv_Refine.lid -> run args (curry Tv_Refine <$$> e_binder <**> e_term_aq (push aq))
        | _ when S.fv_eq_lid fv ref_Tv_Const.lid -> run args (Tv_Const <$$> e_vconst)
        | _ when S.fv_eq_lid fv ref_Tv_Uvar.lid -> run args (curry Tv_Uvar <$$> e_int <**> e_ctx_uvar_and_subst)
        | _ when S.fv_eq_lid fv ref_Tv_Let.lid -> run args (xTv_Let <$$> e_bool <**> e_list e_term <**> e_binder <**> e_term_aq aq <**> e_term_aq (push aq))
        | _ when S.fv_eq_lid fv ref_Tv_Match.lid -> run args (curry3 Tv_Match <$$> e_term_aq aq <**> e_match_returns_annotation <**> e_list (e_branch_aq aq))
        | _ when S.fv_eq_lid fv ref_Tv_AscT.lid -> run args (curry4 Tv_AscribedT <$$> e_term_aq aq <**> e_term_aq aq <**> e_option (e_term_aq aq) <**> e_bool)
        | _ when S.fv_eq_lid fv ref_Tv_AscC.lid -> run args (curry4 Tv_AscribedC <$$> e_term_aq aq <**> e_comp <**> e_option (e_term_aq aq) <**> e_bool)
        | _ when S.fv_eq_lid fv ref_Tv_Unknown.lid -> run args (pure Tv_Unknown)
        | _ when S.fv_eq_lid fv ref_Tv_Unsupp.lid -> run args (pure Tv_Unsupp)
        | _ -> None
    in
    mk_emb embed_term_view unembed_term_view fstar_refl_term_view

let e_term_view = e_term_view_aq noaqs

let e_name = e_list e_string

(* embeds as a string list *)
// instance e_name : embedding I.lid =
//     let embed rng lid : term =
//         embed rng (I.path_of_lid lid)
//     in
//     let uu t _norm : option I.lid =
//         BU.map_opt (try_unembed t) (fun p -> I.lid_of_path p t.pos)
//     in
//     EMB.mk_emb_full (fun x r _ _ -> embed r x)
//                uu
//                (fun () -> t_list_of t_string)
//                I.string_of_lid
//                (fun () -> ET_abstract)


instance e_namedv_view =
    let embed_namedv_view (rng:Range.range) (namedvv:namedv_view) : term =
        S.mk_Tm_app ref_Mk_namedv_view.t [
          S.as_arg (embed rng namedvv.uniq);
          S.as_arg (embed #_ #e_sort   rng namedvv.sort);
          S.as_arg (embed rng namedvv.ppname);
        ]
                    rng
    in
    let unembed_namedv_view (t : term) : option namedv_view =
        let? fv, args = head_fv_and_args t in
        match () with
        | _ when S.fv_eq_lid fv ref_Mk_namedv_view.lid ->
          run args (Mknamedv_view <$$> e_int <**> e_sort <**> e_ppname)
        | _ -> None
    in
    mk_emb embed_namedv_view unembed_namedv_view fstar_refl_namedv_view

instance e_bv_view =
    let embed_bv_view (rng:Range.range) (bvv:bv_view) : term =
        S.mk_Tm_app ref_Mk_bv_view.t [
          S.as_arg (embed rng bvv.index);
          S.as_arg (embed #_ #e_sort   rng bvv.sort);
          S.as_arg (embed rng bvv.ppname);
        ]
                    rng
    in
    let unembed_bv_view (t : term) : option bv_view =
        let? fv, args = head_fv_and_args t in
        match () with
        | _ when S.fv_eq_lid fv ref_Mk_bv_view.lid ->
          run args (Mkbv_view <$$> e_int <**> e_sort <**> e_ppname)
        | _ -> None
    in
    mk_emb embed_bv_view unembed_bv_view fstar_refl_bv_view

instance e_binding =
    let embed (rng:Range.range) (bindingv:RD.binding) : term =
        S.mk_Tm_app ref_Mk_binding.t [
          S.as_arg (embed rng bindingv.uniq);
          S.as_arg (embed #_ #e_term   rng bindingv.sort);
          S.as_arg (embed rng bindingv.ppname);
        ]
                    rng
    in
    let unembed (t : term) : option RD.binding =
        let? fv, args = head_fv_and_args t in
        match () with
        | _ when S.fv_eq_lid fv ref_Mk_binding.lid ->
          run args (Mkbinding <$$> e_int <**> e_term <**> e_ppname)
        | _ -> None
    in
    mk_emb embed unembed fstar_refl_binding

let e_attribute  = e_term
let e_attributes = e_list e_attribute

let e_binder_view =
  let embed_binder_view (rng:Range.range) (bview:binder_view) : term =
    S.mk_Tm_app ref_Mk_binder_view.t [
      S.as_arg (embed #_ #e_term rng bview.sort);
      S.as_arg (embed rng bview.qual);
      S.as_arg (embed #_ #e_attributes rng bview.attrs);
      S.as_arg (embed rng bview.ppname);
    ]
                rng in

  let unembed_binder_view (t:term) : option binder_view =
    let? fv, args = head_fv_and_args t in
    match () with
    | _ when S.fv_eq_lid fv ref_Mk_binder_view.lid ->
      run args (Mkbinder_view <$$> e_term <**> e_aqualv <**> e_list e_term <**> e_ppname)
    | _ -> None
  in
  mk_emb embed_binder_view unembed_binder_view fstar_refl_binder_view

let e_comp_view =
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
        let? fv, args = head_fv_and_args t in
        match () with
        | _ when S.fv_eq_lid fv ref_C_Total.lid -> run args (C_Total <$$> e_term)
        | _ when S.fv_eq_lid fv ref_C_GTotal.lid -> run args (C_GTotal <$$> e_term)
        | _ when S.fv_eq_lid fv ref_C_Lemma.lid ->
          run args (curry3 C_Lemma <$$> e_term <**> e_term <**> e_term)
        | _ when S.fv_eq_lid fv ref_C_Eff.lid ->
          run args (curry5 C_Eff <$$> e_list e_universe <**> e_string_list <**> e_term <**> e_list e_argv <**> e_list e_term)
        | _ -> None
    in
    mk_emb embed_comp_view unembed_comp_view fstar_refl_comp_view

let e_univ_name = e_ident
let e_univ_names = e_list e_univ_name

let e_subst_elt =
    let ee (rng:Range.range) (e:subst_elt) : term =
        match e with
        | DB (i, x) ->
            S.mk_Tm_app ref_DB.t [
                S.as_arg (embed rng i);
                S.as_arg (embed #_ #e_namedv rng x);
               ]
               rng

        | DT (i, t) ->
            S.mk_Tm_app ref_DT.t [
                S.as_arg (embed rng i);
                S.as_arg (embed #_ #e_term rng t);
               ]
               rng

        | NM (x, i) ->
            S.mk_Tm_app ref_NM.t [
                S.as_arg (embed #_ #e_namedv rng x);
                S.as_arg (embed rng i);
               ]
               rng

        | NT (x, t) ->
            S.mk_Tm_app ref_NT.t [
                S.as_arg (embed #_ #e_namedv rng x);
                S.as_arg (embed #_ #e_term rng t);
               ]
               rng

        | UN (i, u) ->
            S.mk_Tm_app ref_UN.t [
                S.as_arg (embed rng i);
                S.as_arg (embed rng u);
               ]
               rng

        | UD (u, i) ->
            S.mk_Tm_app ref_UD.t [
                S.as_arg (embed rng u);
                S.as_arg (embed rng i);
               ]
               rng
    in
    let uu (t:term) : option subst_elt =
        let? fv, args = head_fv_and_args t in
        match () with
        | _ when S.fv_eq_lid fv ref_DB.lid ->
            run args (curry DB <$$> e_fsint <**> e_namedv)
        | _ when S.fv_eq_lid fv ref_DT.lid ->
            run args (curry DT <$$> e_fsint <**> e_term)
        | _ when S.fv_eq_lid fv ref_NM.lid ->
            run args (curry NM <$$> e_namedv <**> e_fsint)
        | _ when S.fv_eq_lid fv ref_NT.lid ->
            run args (curry NT <$$> e_namedv <**> e_term)
        | _ when S.fv_eq_lid fv ref_UN.lid ->
            run args (curry UN <$$> e_fsint <**> e_universe)
        | _ when S.fv_eq_lid fv ref_UD.lid ->
            run args (curry UD <$$> e_ident <**> e_fsint)
        | _ -> None
    in
    mk_emb ee uu fstar_refl_subst_elt

let e_subst = e_list e_subst_elt
let e_ctor = e_tuple2 (e_string_list) e_term

let e_lb_view =
    let embed_lb_view (rng:Range.range) (lbv:lb_view) : term =
        S.mk_Tm_app ref_Mk_lb.t [S.as_arg (embed rng lbv.lb_fv);
                                 S.as_arg (embed rng lbv.lb_us);
                                 S.as_arg (embed #_ #e_term       rng lbv.lb_typ);
                                 S.as_arg (embed #_ #e_term       rng lbv.lb_def)]
                    rng
    in
    let unembed_lb_view (t : term) : option lb_view =
        let? fv, args = head_fv_and_args t in
        match () with
        | _ when S.fv_eq_lid fv ref_Mk_lb.lid ->
          run args (Mklb_view <$$> e_fv <**> e_univ_names <**> e_term <**> e_term)
        | _ -> None
    in
    mk_emb embed_lb_view unembed_lb_view fstar_refl_lb_view

let e_sigelt_view =
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
        let? fv, args = head_fv_and_args t in
        match () with
        | _ when S.fv_eq_lid fv ref_Sg_Inductive.lid ->
            run args (curry5 Sg_Inductive <$$> e_string_list <**> e_univ_names <**> e_binders <**> e_term <**> e_list e_ctor)
        | _ when S.fv_eq_lid fv ref_Sg_Let.lid ->
            run args (curry Sg_Let <$$> e_bool <**> e_list e_letbinding)
        | _ when S.fv_eq_lid fv ref_Sg_Val.lid ->
            run args (curry3 Sg_Val <$$> e_string_list <**> e_univ_names <**> e_term)
        | _ when S.fv_eq_lid fv ref_Unk.lid ->
            run args (pure Unk)
        | _ -> None
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
      let? fv, args = head_fv_and_args t in
        match () with
        | _ when S.fv_eq_lid fv ref_qual_Assumption.lid                       -> run args (pure RD.Assumption)
        | _ when S.fv_eq_lid fv ref_qual_InternalAssumption.lid               -> run args (pure RD.InternalAssumption)
        | _ when S.fv_eq_lid fv ref_qual_New.lid                              -> run args (pure RD.New)
        | _ when S.fv_eq_lid fv ref_qual_Private.lid                          -> run args (pure RD.Private)
        | _ when S.fv_eq_lid fv ref_qual_Unfold_for_unification_and_vcgen.lid -> run args (pure RD.Unfold_for_unification_and_vcgen)
        | _ when S.fv_eq_lid fv ref_qual_Visible_default.lid                  -> run args (pure RD.Visible_default)
        | _ when S.fv_eq_lid fv ref_qual_Irreducible.lid                      -> run args (pure RD.Irreducible)
        | _ when S.fv_eq_lid fv ref_qual_Inline_for_extraction.lid            -> run args (pure RD.Inline_for_extraction)
        | _ when S.fv_eq_lid fv ref_qual_NoExtract.lid                        -> run args (pure RD.NoExtract)
        | _ when S.fv_eq_lid fv ref_qual_Noeq.lid                             -> run args (pure RD.Noeq)
        | _ when S.fv_eq_lid fv ref_qual_Unopteq.lid                          -> run args (pure RD.Unopteq)
        | _ when S.fv_eq_lid fv ref_qual_TotalEffect.lid                      -> run args (pure RD.TotalEffect)
        | _ when S.fv_eq_lid fv ref_qual_Logic.lid                            -> run args (pure RD.Logic)
        | _ when S.fv_eq_lid fv ref_qual_Reifiable.lid                        -> run args (pure RD.Reifiable)
        | _ when S.fv_eq_lid fv ref_qual_ExceptionConstructor.lid             -> run args (pure RD.ExceptionConstructor)
        | _ when S.fv_eq_lid fv ref_qual_HasMaskedEffect.lid                  -> run args (pure RD.HasMaskedEffect)
        | _ when S.fv_eq_lid fv ref_qual_Effect.lid                           -> run args (pure RD.Effect)
        | _ when S.fv_eq_lid fv ref_qual_OnlyName.lid                         -> run args (pure RD.OnlyName)
        | _ when S.fv_eq_lid fv ref_qual_Reflectable.lid ->
            run args (RD.Reflectable <$$> e_name)
        | _ when S.fv_eq_lid fv ref_qual_Discriminator.lid ->
            run args (RD.Discriminator <$$> e_name)
        | _ when S.fv_eq_lid fv ref_qual_Action.lid ->
            run args (RD.Action <$$> e_name)
        | _ when S.fv_eq_lid fv ref_qual_Projector.lid ->
            run args (RD.Projector <$$> e_tuple2 e_name e_ident)
        | _ when S.fv_eq_lid fv ref_qual_RecordType.lid ->
            run args (RD.RecordType <$$> e_tuple2 (e_list e_ident) (e_list e_ident))
        | _ when S.fv_eq_lid fv ref_qual_RecordConstructor.lid ->
            run args (RD.RecordConstructor <$$> e_tuple2 (e_list e_ident) (e_list e_ident))
        | _ -> None
    in
    mk_emb embed unembed fstar_refl_qualifier

let e_qualifiers = e_list e_qualifier

(* -------------------------------------------------------------------------------------- *)
(* ------------------------------------- UNFOLDINGS ------------------------------------- *)
(* -------------------------------------------------------------------------------------- *)


(* Note that most of these are never needed during normalization, since
 * the types are abstract.
 *)

let unfold_lazy_bv (i : lazyinfo) : term =
    let bv : bv = undyn i.blob in
    S.mk_Tm_app fstar_refl_pack_bv.t [S.as_arg (embed i.rng (inspect_bv bv))]
                i.rng

let unfold_lazy_namedv (i : lazyinfo) : term =
    let namedv : namedv = undyn i.blob in
    S.mk_Tm_app fstar_refl_pack_namedv.t [S.as_arg (embed i.rng (inspect_namedv namedv))]
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

let unfold_lazy_doc (i : lazyinfo) : term =
  let open FStarC.Pprint in
  let d : Pprint.document = undyn i.blob in
  let lid = Ident.lid_of_str "FStar.Pprint.arbitrary_string" in
  let s = Pprint.render d in
  S.mk_Tm_app (S.fvar lid None) [S.as_arg (embed i.rng s)]
              i.rng
