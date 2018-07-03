#light "off"
module FStar.Reflection.NBEEmbeddings

open FStar.All
open FStar.Reflection.Data
open FStar.Syntax.Syntax
open FStar.TypeChecker.NBETerm
open FStar.Order
open FStar.Errors

module S = FStar.Syntax.Syntax // TODO: remove, it's open

module I = FStar.Ident
module SS = FStar.Syntax.Subst
module BU = FStar.Util
module Range = FStar.Range
module U = FStar.Syntax.Util
module Print = FStar.Syntax.Print
module Env = FStar.TypeChecker.Env
module Err = FStar.Errors
module Z = FStar.BigInt
open FStar.Reflection.Basic //needed for inspect_fv, but that feels wrong
module PC = FStar.Parser.Const
module NBETerm = FStar.TypeChecker.NBETerm
open FStar.TypeChecker.NBETerm


open FStar.Dyn

(*
 * embed   : from compiler to user
 * unembed : from user to compiler
 *)

(* -------------------------------------------------------------------------------------- *)
(* ------------------------------------- EMBEDDINGS ------------------------------------- *)
(* -------------------------------------------------------------------------------------- *)

(* PLEASE NOTE: Construct and FV accumulate their arguments BACKWARDS. That is,
 * the expression (f 1 2) is stored as FV (f, [], [Constant (Int 2); Constant (Int 1)].
 * So be careful when calling mkFV/mkConstruct and matching on them. *)

(* On that note, we use this (inefficient, FIXME) hack in this module *)
let mkFV fv us ts = mkFV fv (List.rev us) (List.rev ts)
let mkConstruct fv us ts = mkConstruct fv (List.rev us) (List.rev ts)

(* We still need to match on them in reverse order though, so this is pretty dumb *)

let mk_lazy obj ty kind =
    let li = {
          blob = FStar.Dyn.mkdyn obj
        ; lkind = kind
        ; ltyp = ty
        ; rng = Range.dummyRange
    }
    in Lazy li

let e_bv =
    let embed_bv cb (bv:bv) : t =
        mk_lazy bv fstar_refl_bv Lazy_bv
    in
    let unembed_bv cb (t:t) : option<bv> =
        match t with
        | Lazy {blob=b; lkind=Lazy_bv} ->
            Some <| FStar.Dyn.undyn b
        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded bv: %s" (t_to_string t)));
            None
    in
    mk_emb embed_bv unembed_bv (mkFV fstar_refl_bv_fv [] [])

let e_binder =
    let embed_binder cb (b:binder) : t =
        mk_lazy b fstar_refl_binder Lazy_binder
    in
    let unembed_binder cb (t:t) : option<binder> =
        match t with
        | Lazy {blob=b; lkind=Lazy_binder} ->
            Some (undyn b)
        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded binder: %s" (t_to_string t)));
            None
    in
    mk_emb embed_binder unembed_binder (mkFV fstar_refl_binder_fv [] [])

let rec mapM_opt (f : ('a -> option<'b>)) (l : list<'a>) : option<list<'b>> =
    match l with
    | [] -> Some []
    | x::xs ->
        BU.bind_opt (f x) (fun x ->
        BU.bind_opt (mapM_opt f xs) (fun xs ->
        Some (x :: xs)))

let e_term_aq aq =
    let embed_term cb (t:term) : NBETerm.t =
        let qi = { qkind = Quote_static; antiquotes = aq } in
        NBETerm.Quote (t, qi)
    in
    let rec unembed_term cb (t:NBETerm.t) : option<term> =
        (* let apply_antiquotes (t:term) (aq:antiquotations) : option<term> = *)
        (*     BU.bind_opt (mapM_opt (fun (bv, b, e) -> *)
        (*                            if b *)
        (*                            then Some (NT (bv, e)) *)
        (*                            else BU.bind_opt (unembed_term e) (fun e -> Some (NT (bv, e)))) *)
        (*                       aq) (fun s -> *)
        (*     Some (SS.subst s t)) *)
        (* in *)
        match t with
        | NBETerm.Quote (tm, qi) ->
            // antiquotes!!????
            Some tm
        | _ ->
            None
    in
    { NBETerm.em = embed_term
    ; NBETerm.un = unembed_term
    ; NBETerm.typ = mkFV fstar_refl_term_fv [] [] }

let e_term = e_term_aq []

let e_aqualv =
    let embed_aqualv cb (q : aqualv) : t =
        match q with
        | Data.Q_Explicit -> mkConstruct ref_Q_Explicit.fv [] []
        | Data.Q_Implicit -> mkConstruct ref_Q_Implicit.fv [] []
        | Data.Q_Meta t   -> mkConstruct ref_Q_Meta.fv [] [as_arg (embed e_term cb t)]
    in
    let unembed_aqualv cb (t : t) : option<aqualv> =
        match t with
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_Q_Explicit.lid -> Some Data.Q_Explicit
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_Q_Implicit.lid -> Some Data.Q_Implicit
        | Construct (fv, [], [(t, _)]) when S.fv_eq_lid fv ref_Q_Meta.lid ->
            BU.bind_opt (unembed e_term cb t) (fun t ->
            Some (Data.Q_Meta t))

        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded aqualv: %s" (t_to_string t)));
            None
    in
    mk_emb embed_aqualv unembed_aqualv (mkConstruct fstar_refl_aqualv_fv [] [])

let e_binders = e_list e_binder

let e_fv =
    let embed_fv cb (fv:fv) : t =
        mk_lazy fv fstar_refl_fv Lazy_fvar
    in
    let unembed_fv cb (t:t) : option<fv> =
        match t with
        | Lazy {blob=b; lkind=Lazy_fvar} ->
            Some (undyn b)
        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded fvar: %s" (t_to_string t)));
            None
    in
    mk_emb embed_fv unembed_fv (mkFV fstar_refl_fv_fv [] [])

let e_comp =
    let embed_comp cb (c:S.comp) : t =
        mk_lazy c fstar_refl_comp Lazy_comp
    in
    let unembed_comp cb (t:t) : option<S.comp> =
        match t with
        | Lazy {blob=b; lkind=Lazy_comp} ->
            Some (undyn b)
        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded comp: %s" (t_to_string t)));
            None
    in
    mk_emb embed_comp unembed_comp (mkFV fstar_refl_comp_fv [] [])

let e_env =
    let embed_env cb (e:Env.env) : t =
        mk_lazy e fstar_refl_env Lazy_env
    in
    let unembed_env cb (t:t) : option<Env.env> =
        match t with
        | Lazy {blob=b; lkind=Lazy_env} ->
            Some (undyn b)
        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded env: %s" (t_to_string t)));
            None
    in
    mk_emb embed_env unembed_env (mkFV fstar_refl_env_fv [] [])

let e_const =
    let embed_const cb (c:vconst) : t =
        match c with
        | C_Unit     -> mkConstruct ref_C_Unit.fv    [] []
        | C_True     -> mkConstruct ref_C_True.fv    [] []
        | C_False    -> mkConstruct ref_C_False.fv   [] []
        | C_Int i    -> mkConstruct ref_C_Int.fv     [] [as_arg (Constant (Int i))]
        | C_String s -> mkConstruct ref_C_String.fv  [] [as_arg (embed e_string cb s)]
    in
    let unembed_const cb (t:t) : option<vconst> =
        match t with
        | Construct (fv, [], []) when S.fv_eq_lid fv ref_C_Unit.lid ->
            Some C_Unit

        | Construct (fv, [], []) when S.fv_eq_lid fv ref_C_True.lid ->
            Some C_True

        | Construct (fv, [], []) when S.fv_eq_lid fv ref_C_False.lid ->
            Some C_False

        | Construct (fv, [], [(i, _)]) when S.fv_eq_lid fv ref_C_Int.lid ->
            BU.bind_opt (unembed e_int cb i) (fun i ->
            Some <| C_Int i)

        | Construct (fv, [], [(s, _)]) when S.fv_eq_lid fv ref_C_String.lid ->
            BU.bind_opt (unembed e_string cb s) (fun s ->
            Some <| C_String s)

        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded vconst: %s" (t_to_string t)));
            None
    in
    mk_emb embed_const unembed_const (mkFV fstar_refl_vconst_fv [] [])

let rec e_pattern' () =
    let embed_pattern cb (p : pattern) : t =
        match p with
        | Pat_Constant c ->
            mkConstruct ref_Pat_Constant.fv [] [as_arg (embed e_const cb c)]
        | Pat_Cons (fv, ps) ->
            mkConstruct ref_Pat_Cons.fv [] [as_arg (embed e_fv cb fv); as_arg (embed (e_list (e_pattern' ())) cb ps)]
        | Pat_Var bv ->
            mkConstruct ref_Pat_Var.fv [] [as_arg (embed e_bv cb bv)]
        | Pat_Wild bv ->
            mkConstruct ref_Pat_Wild.fv [] [as_arg (embed e_bv cb bv)]
        | Pat_Dot_Term (bv, t) ->
            mkConstruct ref_Pat_Dot_Term.fv [] [as_arg (embed e_bv cb bv); as_arg (embed e_term cb t)]
    in
    let unembed_pattern cb (t : t) : option<pattern> =
        match t with
        | Construct (fv, [], [(c, _)]) when S.fv_eq_lid fv ref_Pat_Constant.lid ->
            BU.bind_opt (unembed e_const cb c) (fun c ->
            Some <| Pat_Constant c)

        | Construct (fv, [], [(ps, _); (f, _)]) when S.fv_eq_lid fv ref_Pat_Cons.lid ->
            BU.bind_opt (unembed e_fv cb f) (fun f ->
            BU.bind_opt (unembed (e_list (e_pattern' ())) cb ps) (fun ps ->
            Some <| Pat_Cons (f, ps)))

        | Construct (fv, [], [(bv, _)]) when S.fv_eq_lid fv ref_Pat_Var.lid ->
            BU.bind_opt (unembed e_bv cb bv) (fun bv ->
            Some <| Pat_Var bv)

        | Construct (fv, [], [(bv, _)]) when S.fv_eq_lid fv ref_Pat_Wild.lid ->
            BU.bind_opt (unembed e_bv cb bv) (fun bv ->
            Some <| Pat_Wild bv)

        | Construct (fv, [], [(t, _); (bv, _)]) when S.fv_eq_lid fv ref_Pat_Dot_Term.lid ->
            BU.bind_opt (unembed e_bv cb bv) (fun bv ->
            BU.bind_opt (unembed e_term cb t) (fun t ->
            Some <| Pat_Dot_Term (bv, t)))

        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded pattern: %s" (t_to_string t)));
            None
    in
    mk_emb embed_pattern unembed_pattern (mkFV fstar_refl_pattern_fv [] [])

let e_pattern = e_pattern' ()

let e_branch = e_tuple2 e_pattern e_term
let e_argv   = e_tuple2 e_term    e_aqualv

let e_branch_aq aq = e_tuple2 e_pattern      (e_term_aq aq)
let e_argv_aq   aq = e_tuple2 (e_term_aq aq) e_aqualv

let rec unlazy_as_t k t =
    match t with
    | Lazy ({lkind=k'; blob=v})
        when U.eq_lazy_kind k k' ->
      FStar.Dyn.undyn v
    | _ ->
      failwith "Not a Lazy of the expected kind (NBE)"

let e_term_view_aq aq =
    let embed_term_view cb (tv:term_view) : t =
        match tv with
        | Tv_FVar fv ->
            mkConstruct ref_Tv_Var.fv [] [as_arg (embed e_fv cb fv)]

        | Tv_BVar bv ->
            mkConstruct ref_Tv_BVar.fv [] [as_arg (embed e_bv cb bv)]

        | Tv_Var bv ->
            mkConstruct ref_Tv_Var.fv [] [as_arg (embed e_bv cb bv)]

        | Tv_App (hd, a) ->
            mkConstruct ref_Tv_App.fv [] [as_arg (embed (e_term_aq aq) cb hd); as_arg (embed (e_argv_aq aq) cb a)]

        | Tv_Abs (b, t) ->
            mkConstruct ref_Tv_Abs.fv [] [as_arg (embed e_binder cb b); as_arg (embed (e_term_aq aq) cb t)]

        | Tv_Arrow (b, c) ->
            mkConstruct ref_Tv_Arrow.fv [] [as_arg (embed e_binder cb b); as_arg (embed e_comp cb c)]

        | Tv_Type u ->
            mkConstruct ref_Tv_Type.fv [] [as_arg (embed e_unit cb ())]

        | Tv_Refine (bv, t) ->
            mkConstruct ref_Tv_Refine.fv [] [as_arg (embed e_bv cb bv); as_arg (embed (e_term_aq aq) cb t)]

        | Tv_Const c ->
            mkConstruct ref_Tv_Const.fv [] [as_arg (embed e_const cb c)]

        | Tv_Uvar (u, d) ->
            mkConstruct ref_Tv_Uvar.fv [] [as_arg (embed e_int cb u); as_arg (mk_lazy (u,d) U.t_ctx_uvar_and_sust Lazy_uvar)]

        | Tv_Let (r, b, t1, t2) ->
            mkConstruct ref_Tv_Let.fv [] [as_arg (embed e_bool cb r);
                                   as_arg (embed e_bv cb b);
                                   as_arg (embed (e_term_aq aq) cb t1);
                                   as_arg (embed (e_term_aq aq) cb t2)]

        | Tv_Match (t, brs) ->
            mkConstruct ref_Tv_Match.fv [] [as_arg (embed (e_term_aq aq) cb t);
                                     as_arg (embed (e_list (e_branch_aq aq)) cb brs)]

        | Tv_AscribedT (e, t, tacopt) ->
            mkConstruct ref_Tv_AscT.fv []
                        [as_arg (embed (e_term_aq aq) cb e);
                         as_arg (embed (e_term_aq aq) cb t);
                         as_arg (embed (e_option (e_term_aq aq)) cb tacopt)]

        | Tv_AscribedC (e, c, tacopt) ->
            mkConstruct ref_Tv_AscT.fv []
                        [as_arg (embed (e_term_aq aq) cb e);
                         as_arg (embed e_comp cb c);
                         as_arg (embed (e_option (e_term_aq aq)) cb tacopt)]

        | Tv_Unknown ->
            mkConstruct ref_Tv_Unknown.fv [] []
    in
    let unembed_term_view cb (t:t) : option<term_view> =
        match t with
        | Construct (fv, _, [(b, _)]) when S.fv_eq_lid fv ref_Tv_Var.lid ->
            BU.bind_opt (unembed e_bv cb b) (fun b ->
            Some <| Tv_Var b)

        | Construct (fv, _, [(b, _)]) when S.fv_eq_lid fv ref_Tv_BVar.lid ->
            BU.bind_opt (unembed e_bv cb b) (fun b ->
            Some <| Tv_BVar b)

        | Construct (fv, _, [(f, _)]) when S.fv_eq_lid fv ref_Tv_FVar.lid ->
            BU.bind_opt (unembed e_fv cb f) (fun f ->
            Some <| Tv_FVar f)

        | Construct (fv, _, [(r, _); (l, _)]) when S.fv_eq_lid fv ref_Tv_App.lid ->
            BU.bind_opt (unembed e_term cb l) (fun l ->
            BU.bind_opt (unembed e_argv cb r) (fun r ->
            Some <| Tv_App (l, r)))

        | Construct (fv, _, [(t, _); (b, _)]) when S.fv_eq_lid fv ref_Tv_Abs.lid ->
            BU.bind_opt (unembed e_binder cb b) (fun b ->
            BU.bind_opt (unembed e_term cb t) (fun t ->
            Some <| Tv_Abs (b, t)))

        | Construct (fv, _, [(t, _); (b, _)]) when S.fv_eq_lid fv ref_Tv_Arrow.lid ->
            BU.bind_opt (unembed e_binder cb b) (fun b ->
            BU.bind_opt (unembed e_comp cb t) (fun c ->
            Some <| Tv_Arrow (b, c)))

        | Construct (fv, _, [(u, _)]) when S.fv_eq_lid fv ref_Tv_Type.lid ->
            BU.bind_opt (unembed e_unit cb u) (fun u ->
            Some <| Tv_Type u)

        | Construct (fv, _, [(t, _); (b, _)]) when S.fv_eq_lid fv ref_Tv_Refine.lid ->
            BU.bind_opt (unembed e_bv cb b) (fun b ->
            BU.bind_opt (unembed e_term cb t) (fun t ->
            Some <| Tv_Refine (b, t)))

        | Construct (fv, _, [(c, _)]) when S.fv_eq_lid fv ref_Tv_Const.lid ->
            BU.bind_opt (unembed e_const cb c) (fun c ->
            Some <| Tv_Const c)

        | Construct (fv, _, [(l, _); (u, _)]) when S.fv_eq_lid fv ref_Tv_Uvar.lid ->
            BU.bind_opt (unembed e_int cb u) (fun u ->
            let ctx_u_s : ctx_uvar_and_subst = unlazy_as_t Lazy_uvar l in
            Some <| Tv_Uvar (u, ctx_u_s))

        | Construct (fv, _, [(t2, _); (t1, _); (b, _); (r, _)]) when S.fv_eq_lid fv ref_Tv_Let.lid ->
            BU.bind_opt (unembed e_bool cb r) (fun r ->
            BU.bind_opt (unembed e_bv cb b) (fun b ->
            BU.bind_opt (unembed e_term cb t1) (fun t1 ->
            BU.bind_opt (unembed e_term cb t2) (fun t2 ->
            Some <| Tv_Let (r, b, t1, t2)))))

        | Construct (fv, _, [(brs, _); (t, _)]) when S.fv_eq_lid fv ref_Tv_Match.lid ->
            BU.bind_opt (unembed e_term cb t) (fun t ->
            BU.bind_opt (unembed (e_list e_branch) cb brs) (fun brs ->
            Some <| Tv_Match (t, brs)))

        | Construct (fv, _, [(tacopt, _); (t, _); (e, _)]) when S.fv_eq_lid fv ref_Tv_AscT.lid ->
            BU.bind_opt (unembed e_term cb e) (fun e ->
            BU.bind_opt (unembed e_term cb t) (fun t ->
            BU.bind_opt (unembed (e_option e_term) cb tacopt) (fun tacopt ->
            Some <| Tv_AscribedT (e, t, tacopt))))

        | Construct (fv, _, [(tacopt, _); (c, _); (e, _)]) when S.fv_eq_lid fv ref_Tv_AscC.lid ->
            BU.bind_opt (unembed e_term cb e) (fun e ->
            BU.bind_opt (unembed e_comp cb c) (fun c ->
            BU.bind_opt (unembed (e_option e_term) cb tacopt) (fun tacopt ->
            Some <| Tv_AscribedC (e, c, tacopt))))

        | Construct (fv, _, []) when S.fv_eq_lid fv ref_Tv_Unknown.lid ->
            Some <| Tv_Unknown

        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded term_view: %s" (t_to_string t)));
            None
    in
    mk_emb embed_term_view unembed_term_view (mkFV fstar_refl_term_view_fv [] [])


let e_term_view = e_term_view_aq []

let e_bv_view =
    let embed_bv_view cb (bvv:bv_view) : t =
        mkConstruct ref_Mk_bv.fv [] [as_arg (embed e_string cb bvv.bv_ppname);
                              as_arg (embed e_int    cb bvv.bv_index);
                              as_arg (embed e_term   cb bvv.bv_sort)]
    in
    let unembed_bv_view cb (t : t) : option<bv_view> =
        match t with
        | Construct (fv, _, [(s, _); (idx, _); (nm, _)]) when S.fv_eq_lid fv ref_Mk_bv.lid ->
            BU.bind_opt (unembed e_string cb nm) (fun nm ->
            BU.bind_opt (unembed e_int cb idx) (fun idx ->
            BU.bind_opt (unembed e_term cb s) (fun s ->
            Some <| { bv_ppname = nm ; bv_index = idx ; bv_sort = s })))

        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded bv_view: %s" (t_to_string t)));
            None
    in
    mk_emb embed_bv_view unembed_bv_view (mkFV fstar_refl_bv_view_fv [] [])

let e_comp_view =
    let embed_comp_view cb (cv : comp_view) : t =
        match cv with
        | C_Total (t, md) ->
            mkConstruct ref_C_Total.fv [] [as_arg (embed e_term cb t);
                                    as_arg (embed (e_option e_term) cb md)]

        | C_Lemma (pre, post) ->
            let post = U.unthunk_lemma_post post in
            mkConstruct ref_C_Lemma.fv [] [as_arg (embed e_term cb pre); as_arg (embed e_term cb post)]

        | C_Unknown ->
            mkConstruct ref_C_Unknown.fv [] []
    in
    let unembed_comp_view cb (t : t) : option<comp_view> =
        match t with
        | Construct (fv, _, [(md, _); (t, _)]) when S.fv_eq_lid fv ref_C_Total.lid ->
            BU.bind_opt (unembed e_term cb t) (fun t ->
            BU.bind_opt (unembed (e_option e_term) cb md) (fun md ->
            Some <| C_Total (t, md)))

        | Construct (fv, _, [(post, _); (pre, _)]) when S.fv_eq_lid fv ref_C_Lemma.lid ->
            BU.bind_opt (unembed e_term cb pre) (fun pre ->
            BU.bind_opt (unembed e_term cb post) (fun post ->
            Some <| C_Lemma (pre, post)))

        | Construct (fv, _, []) when S.fv_eq_lid fv ref_C_Unknown.lid ->
            Some <| C_Unknown

        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded comp_view: %s" (t_to_string t)));
            None
    in
    mk_emb embed_comp_view unembed_comp_view (mkFV fstar_refl_comp_view_fv [] [])


(* TODO: move to, Syntax.Embeddings or somewhere better even *)
let e_order =
    let embed_order cb (o:order) : t =
        match o with
        | Lt -> mkConstruct ord_Lt_fv [] []
        | Eq -> mkConstruct ord_Eq_fv [] []
        | Gt -> mkConstruct ord_Gt_fv [] []
    in
    let unembed_order cb (t:t) : option<order> =
        match t with
        | Construct (fv, _, []) when S.fv_eq_lid fv ord_Lt_lid -> Some Lt
        | Construct (fv, _, []) when S.fv_eq_lid fv ord_Eq_lid -> Some Eq
        | Construct (fv, _, []) when S.fv_eq_lid fv ord_Gt_lid -> Some Gt
        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded order: %s" (t_to_string t)));
            None
    in
    mk_emb embed_order unembed_order (mkFV (lid_as_fv PC.order_lid delta_constant None) [] [])

let e_sigelt =
    let embed_sigelt cb (se:sigelt) : t =
        mk_lazy se fstar_refl_sigelt Lazy_sigelt
    in
    let unembed_sigelt cb (t:t) : option<sigelt> =
        match t with
        | Lazy {blob=b; lkind=Lazy_sigelt} ->
            Some (undyn b)
        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded sigelt: %s" (t_to_string t)));
            None
    in
    mk_emb embed_sigelt unembed_sigelt (mkFV fstar_refl_sigelt_fv [] [])

// TODO: It would be nice to have a
// embed_as : ('a -> 'b) -> ('b -> 'a) -> embedding<'a> -> embedding<'b>
// so we don't write these things
let e_ident : embedding<I.ident> =
    let repr = e_tuple2 e_range e_string in
    let embed_ident cb (i:I.ident) : t =
        embed repr cb (I.range_of_id i, I.text_of_id i)
    in
    let unembed_ident cb (t:t) : option<I.ident> =
        match unembed repr cb t with
        | Some (rng, s) -> Some (I.mk_ident (s, rng))
        | None -> None
    in
    mk_emb embed_ident unembed_ident (mkFV (lid_as_fv PC.lid_tuple2 delta_constant None)
                                           [U_zero;U_zero]
                                           [as_arg (mkFV (lid_as_fv PC.range_lid  delta_constant None) [] []);
                                            as_arg (mkFV (lid_as_fv PC.string_lid delta_constant None) [] [])])
    // TODO: again a delta depth issue, should be this
    (* fstar_refl_ident *)

let e_univ_name =
    (* TODO: Should be this, but there's a delta depth issue *)
    (* set_type fstar_refl_univ_name e_ident *)
    e_ident

let e_univ_names = e_list e_univ_name
let e_string_list = e_list e_string

let e_sigelt_view =
    let embed_sigelt_view cb (sev:sigelt_view) : t =
        match sev with
        | Sg_Let (r, fv, univs, ty, t) ->
            mkConstruct ref_Sg_Let.fv [] [as_arg (embed e_bool cb r);
                                   as_arg (embed e_fv cb fv);
                                   as_arg (embed e_univ_names cb univs);
                                   as_arg (embed e_term cb ty);
                                   as_arg (embed e_term cb t)]

        | Sg_Constructor (nm, ty) ->
            mkConstruct ref_Sg_Constructor.fv [] [as_arg (embed e_string_list cb nm);
                                           as_arg (embed e_term cb ty)]

        | Sg_Inductive (nm, univs, bs, t, dcs) ->
            mkConstruct ref_Sg_Inductive.fv [] [as_arg (embed e_string_list cb nm);
                                         as_arg (embed e_univ_names cb univs);
                                         as_arg (embed e_binders cb bs);
                                         as_arg (embed e_term cb t);
                                         as_arg (embed (e_list e_string_list) cb dcs)]

        | Unk ->
            mkConstruct ref_Unk.fv [] []
    in
    let unembed_sigelt_view cb (t:t) : option<sigelt_view> =
        match t with
        | Construct (fv, _, [(dcs, _); (t, _); (bs, _); (us, _); (nm, _)]) when S.fv_eq_lid fv ref_Sg_Inductive.lid ->
            BU.bind_opt (unembed e_string_list cb nm) (fun nm ->
            BU.bind_opt (unembed e_univ_names cb us) (fun us ->
            BU.bind_opt (unembed e_binders cb bs) (fun bs ->
            BU.bind_opt (unembed e_term cb t) (fun t ->
            BU.bind_opt (unembed (e_list e_string_list) cb dcs) (fun dcs ->
            Some <| Sg_Inductive (nm, us, bs, t, dcs))))))

        | Construct (fv, _, [(t, _); (ty, _); (univs, _); (fvar, _); (r, _)]) when S.fv_eq_lid fv ref_Sg_Let.lid ->
            BU.bind_opt (unembed e_bool cb r) (fun r ->
            BU.bind_opt (unembed e_fv cb fvar) (fun fvar ->
            BU.bind_opt (unembed e_univ_names cb univs) (fun univs ->
            BU.bind_opt (unembed e_term cb ty) (fun ty ->
            BU.bind_opt (unembed e_term cb t) (fun t ->
            Some <| Sg_Let (r, fvar, univs, ty, t))))))

        | Construct (fv, _, []) when S.fv_eq_lid fv ref_Unk.lid ->
            Some Unk

        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded sigelt_view: %s" (t_to_string t)));
            None
    in
    mk_emb embed_sigelt_view unembed_sigelt_view (mkFV fstar_refl_sigelt_view_fv [] [])

let e_exp =
    let rec embed_exp cb (e:exp) : t =
        match e with
        | Data.Unit  ->         mkConstruct ref_E_Unit.fv [] []
        | Data.Var i ->         mkConstruct ref_E_Var.fv  [] [as_arg (Constant (Int i))]
        | Data.Mult (e1, e2) -> mkConstruct ref_E_Mult.fv [] [as_arg (embed_exp cb e1); as_arg (embed_exp cb e2)]
    in
    let rec unembed_exp cb (t: t) : option<exp> =
        match t with
        | Construct (fv, _, []) when S.fv_eq_lid fv ref_E_Unit.lid ->
            Some Data.Unit

        | Construct (fv, _, [(i, _)]) when S.fv_eq_lid fv ref_E_Var.lid ->
            BU.bind_opt (unembed e_int cb i) (fun i ->
            Some <| Data.Var i)

        | Construct (fv, _, [(e2, _); (e1, _)]) when S.fv_eq_lid fv ref_E_Mult.lid ->
            BU.bind_opt (unembed_exp cb e1) (fun e1 ->
            BU.bind_opt (unembed_exp cb e2) (fun e2 ->
            Some <| Data.Mult (e1, e2)))
        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded exp: %s" (t_to_string t)));
            None
    in
    mk_emb embed_exp unembed_exp (mkFV fstar_refl_exp_fv [] [])

let e_binder_view = e_tuple2 e_bv e_aqualv

let e_attribute  = e_term
let e_attributes = e_list e_attribute
