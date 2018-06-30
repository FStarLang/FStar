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

let mk_lazy obj ty kind =
    let li = {
          blob = FStar.Dyn.mkdyn obj
        ; lkind = kind
        ; typ = ty
        ; rng = Range.dummyRange
    }
    in Lazy li

let mk_emb em un typ =
    { em = em ; un = un ; typ = typ }

let e_bv =
    let embed_bv (bv:bv) : t =
        mk_lazy bv fstar_refl_bv Lazy_bv
    in
    let unembed_bv (t:t) : option<bv> =
        match t with
        | Lazy li when li.lkind = Lazy_bv ->
            Some <| FStar.Dyn.undyn li.blob
        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded bv: %s" (t_to_string t)));
            None
    in
    mk_emb embed_bv unembed_bv (mkFV fstar_refl_bv_fv [] [])

let e_binder =
    let embed_binder (b:binder) : t =
        mk_lazy b fstar_refl_binder Lazy_binder
    in
    let unembed_binder (t:t) : option<binder> =
        match t with
        | Lazy li when li.lkind = Lazy_binder ->
            Some (undyn li.blob)
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
    let embed_term (t:term) : NBETerm.t =
        let qi = { qkind = Quote_static; antiquotes = aq } in
        NBETerm.Quote (t, qi)
    in
    let rec unembed_term (t:NBETerm.t) : option<term> =
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
    let embed_aqualv (q : aqualv) : t =
        match q with
        | Data.Q_Explicit -> mkFV ref_Q_Explicit.fv [] []
        | Data.Q_Implicit -> mkFV ref_Q_Implicit.fv [] []
        | Data.Q_Meta t   -> mkFV ref_Q_Meta.fv [] [as_arg (embed e_term t)]
    in
    let unembed_aqualv (t : t) : option<aqualv> =
        match t with
        | FV (fv, [], []) when S.fv_eq_lid fv ref_Q_Explicit.lid -> Some Data.Q_Explicit
        | FV (fv, [], []) when S.fv_eq_lid fv ref_Q_Implicit.lid -> Some Data.Q_Implicit
        | FV (fv, [], [(t, _)]) when S.fv_eq_lid fv ref_Q_Meta.lid ->
            BU.bind_opt (unembed e_term t) (fun t ->
            Some (Data.Q_Meta t))

        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded aqualv: %s" (t_to_string t)));
            None
    in
    mk_emb embed_aqualv unembed_aqualv (mkFV fstar_refl_aqualv_fv [] [])

let e_binders = e_list e_binder

let e_fv =
    let embed_fv (fv:fv) : t =
        mk_lazy fv fstar_refl_fv Lazy_fvar
    in
    let unembed_fv (t:t) : option<fv> =
        match t with
        | Lazy i when i.lkind = Lazy_fvar ->
            Some (undyn i.blob)
        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded fvar: %s" (t_to_string t)));
            None
    in
    mk_emb embed_fv unembed_fv (mkFV fstar_refl_fv_fv [] [])

let e_comp =
    let embed_comp (c:S.comp) : t =
        mk_lazy c fstar_refl_comp Lazy_comp
    in
    let unembed_comp (t:t) : option<S.comp> =
        match t with
        | Lazy i when i.lkind = Lazy_comp ->
            Some (undyn i.blob)
        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded comp: %s" (t_to_string t)));
            None
    in
    mk_emb embed_comp unembed_comp (mkFV fstar_refl_comp_fv [] [])

let e_env =
    let embed_env (e:Env.env) : t =
        mk_lazy e fstar_refl_env Lazy_env
    in
    let unembed_env (t:t) : option<Env.env> =
        match t with
        | Lazy i when i.lkind = Lazy_env ->
            Some (undyn i.blob)
        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded env: %s" (t_to_string t)));
            None
    in
    mk_emb embed_env unembed_env (mkFV fstar_refl_env_fv [] [])

let e_const =
    let embed_const (c:vconst) : t =
        match c with
        | C_Unit     -> mkFV ref_C_Unit.fv    [] []
        | C_True     -> mkFV ref_C_True.fv    [] []
        | C_False    -> mkFV ref_C_False.fv   [] []
        | C_Int i    -> mkFV ref_C_Int.fv     [] [as_arg (Constant (Int i))]
        | C_String s -> mkFV ref_C_String.fv  [] [as_arg (embed e_string s)]
    in
    let unembed_const (t:t) : option<vconst> =
        match t with
        | FV (fv, [], []) when S.fv_eq_lid fv ref_C_Unit.lid ->
            Some C_Unit

        | FV (fv, [], []) when S.fv_eq_lid fv ref_C_True.lid ->
            Some C_True

        | FV (fv, [], []) when S.fv_eq_lid fv ref_C_False.lid ->
            Some C_False

        | FV (fv, [], [(i, _)]) when S.fv_eq_lid fv ref_C_Int.lid ->
            BU.bind_opt (unembed e_int i) (fun i ->
            Some <| C_Int i)

        | FV (fv, [], [(s, _)]) when S.fv_eq_lid fv ref_C_String.lid ->
            BU.bind_opt (unembed e_string s) (fun s ->
            Some <| C_String s)

        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded vconst: %s" (t_to_string t)));
            None
    in
    mk_emb embed_const unembed_const (mkFV fstar_refl_vconst_fv [] [])

let rec e_pattern' () =
    let rec embed_pattern (p : pattern) : t =
        match p with
        | Pat_Constant c ->
            mkFV ref_Pat_Constant.fv [] [as_arg (embed e_const c)]
        | Pat_Cons (fv, ps) ->
            mkFV ref_Pat_Cons.fv [] [as_arg (embed e_fv fv); as_arg (embed (e_list (e_pattern' ())) ps)]
        | Pat_Var bv ->
            mkFV ref_Pat_Var.fv [] [as_arg (embed e_bv bv)]
        | Pat_Wild bv ->
            mkFV ref_Pat_Wild.fv [] [as_arg (embed e_bv bv)]
        | Pat_Dot_Term (bv, t) ->
            mkFV ref_Pat_Dot_Term.fv [] [as_arg (embed e_bv bv); as_arg (embed e_term t)]
    in
    let rec unembed_pattern (t : t) : option<pattern> =
        match t with
        | FV (fv, [], [(c, _)]) when S.fv_eq_lid fv ref_Pat_Constant.lid ->
            BU.bind_opt (unembed e_const c) (fun c ->
            Some <| Pat_Constant c)

        | FV (fv, [], [(f, _); (ps, _)])when S.fv_eq_lid fv ref_Pat_Cons.lid ->
            BU.bind_opt (unembed e_fv f) (fun f ->
            BU.bind_opt (unembed (e_list (e_pattern' ())) ps) (fun ps ->
            Some <| Pat_Cons (f, ps)))

        | FV (fv, [], [(bv, _)]) when S.fv_eq_lid fv ref_Pat_Var.lid ->
            BU.bind_opt (unembed e_bv bv) (fun bv ->
            Some <| Pat_Var bv)

        | FV (fv, [], [(bv, _)]) when S.fv_eq_lid fv ref_Pat_Wild.lid ->
            BU.bind_opt (unembed e_bv bv) (fun bv ->
            Some <| Pat_Wild bv)

        | FV (fv, [], [(bv, _); (t, _)]) when S.fv_eq_lid fv ref_Pat_Dot_Term.lid ->
            BU.bind_opt (unembed e_bv bv) (fun bv ->
            BU.bind_opt (unembed e_term t) (fun t ->
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
        when k=k' ->
      FStar.Dyn.undyn v
    | _ ->
      failwith "Not a Lazy of the expected kind (NBE)"

let e_term_view_aq aq =
    let embed_term_view (t:term_view) : t =
        match t with
        | Tv_FVar fv ->
            mkFV ref_Tv_Var.fv [] [as_arg (embed e_fv fv)]

        | Tv_BVar bv ->
            mkFV ref_Tv_BVar.fv [] [as_arg (embed e_bv bv)]

        | Tv_Var bv ->
            mkFV ref_Tv_Var.fv [] [as_arg (embed e_bv bv)]

        | Tv_App (hd, a) ->
            mkFV ref_Tv_App.fv [] [as_arg (embed (e_term_aq aq) hd); as_arg (embed (e_argv_aq aq) a)]

        | Tv_Abs (b, t) ->
            mkFV ref_Tv_Abs.fv [] [as_arg (embed e_binder b); as_arg (embed (e_term_aq aq) t)]

        | Tv_Arrow (b, c) ->
            mkFV ref_Tv_Arrow.fv [] [as_arg (embed e_binder b); as_arg (embed e_comp c)]

        | Tv_Type u ->
            mkFV ref_Tv_Type.fv [] [as_arg (embed e_unit ())]

        | Tv_Refine (bv, t) ->
            mkFV ref_Tv_Refine.fv [] [as_arg (embed e_bv bv); as_arg (embed (e_term_aq aq) t)]

        | Tv_Const c ->
            mkFV ref_Tv_Const.fv [] [as_arg (embed e_const c)]

        | Tv_Uvar (u, d) ->
            mkFV ref_Tv_Uvar.fv [] [as_arg (embed e_int u); as_arg (mk_lazy (u,d) U.t_ctx_uvar_and_sust Lazy_uvar)]

        | Tv_Let (r, b, t1, t2) ->
            mkFV ref_Tv_Let.fv [] [as_arg (embed e_bool r);
                                   as_arg (embed e_bv b);
                                   as_arg (embed (e_term_aq aq) t1);
                                   as_arg (embed (e_term_aq aq) t2)]

        | Tv_Match (t, brs) ->
            mkFV ref_Tv_Match.fv [] [as_arg (embed (e_term_aq aq) t);
                                     as_arg (embed (e_list (e_branch_aq aq)) brs)]

        | Tv_AscribedT (e, t, tacopt) ->
            mkFV ref_Tv_AscT.fv []
                        [as_arg (embed (e_term_aq aq) e);
                         as_arg (embed (e_term_aq aq) t);
                         as_arg (embed (e_option (e_term_aq aq)) tacopt)]

        | Tv_AscribedC (e, c, tacopt) ->
            mkFV ref_Tv_AscT.fv []
                        [as_arg (embed (e_term_aq aq) e);
                         as_arg (embed e_comp c);
                         as_arg (embed (e_option (e_term_aq aq)) tacopt)]

        | Tv_Unknown ->
            mkFV ref_Tv_Unknown.fv [] []
    in
    let unembed_term_view (t:t) : option<term_view> =
        match t with
        | FV (fv, _, [(b, _)]) when S.fv_eq_lid fv ref_Tv_Var.lid ->
            BU.bind_opt (unembed e_bv b) (fun b ->
            Some <| Tv_Var b)

        | FV (fv, _, [(b, _)]) when S.fv_eq_lid fv ref_Tv_BVar.lid ->
            BU.bind_opt (unembed e_bv b) (fun b ->
            Some <| Tv_BVar b)

        | FV (fv, _, [(f, _)]) when S.fv_eq_lid fv ref_Tv_FVar.lid ->
            BU.bind_opt (unembed e_fv f) (fun f ->
            Some <| Tv_FVar f)

        | FV (fv, _, [(l, _); (r, _)]) when S.fv_eq_lid fv ref_Tv_App.lid ->
            BU.bind_opt (unembed e_term l) (fun l ->
            BU.bind_opt (unembed e_argv r) (fun r ->
            Some <| Tv_App (l, r)))

        | FV (fv, _, [(b, _); (t, _)]) when S.fv_eq_lid fv ref_Tv_Abs.lid ->
            BU.bind_opt (unembed e_binder b) (fun b ->
            BU.bind_opt (unembed e_term t) (fun t ->
            Some <| Tv_Abs (b, t)))

        | FV (fv, _, [(b, _); (t, _)]) when S.fv_eq_lid fv ref_Tv_Arrow.lid ->
            BU.bind_opt (unembed e_binder b) (fun b ->
            BU.bind_opt (unembed e_comp t) (fun c ->
            Some <| Tv_Arrow (b, c)))

        | FV (fv, _, [(u, _)]) when S.fv_eq_lid fv ref_Tv_Type.lid ->
            BU.bind_opt (unembed e_unit u) (fun u ->
            Some <| Tv_Type u)

        | FV (fv, _, [(b, _); (t, _)]) when S.fv_eq_lid fv ref_Tv_Refine.lid ->
            BU.bind_opt (unembed e_bv b) (fun b ->
            BU.bind_opt (unembed e_term t) (fun t ->
            Some <| Tv_Refine (b, t)))

        | FV (fv, _, [(c, _)]) when S.fv_eq_lid fv ref_Tv_Const.lid ->
            BU.bind_opt (unembed e_const c) (fun c ->
            Some <| Tv_Const c)

        | FV (fv, _, [(u, _); (l, _)]) when S.fv_eq_lid fv ref_Tv_Uvar.lid ->
            BU.bind_opt (unembed e_int u) (fun u ->
            let ctx_u_s : ctx_uvar_and_subst = unlazy_as_t Lazy_uvar l in
            Some <| Tv_Uvar (u, ctx_u_s))

        | FV (fv, _, [(r, _); (b, _); (t1, _); (t2, _)]) when S.fv_eq_lid fv ref_Tv_Let.lid ->
            BU.bind_opt (unembed e_bool r) (fun r ->
            BU.bind_opt (unembed e_bv b) (fun b ->
            BU.bind_opt (unembed e_term t1) (fun t1 ->
            BU.bind_opt (unembed e_term t2) (fun t2 ->
            Some <| Tv_Let (r, b, t1, t2)))))

        | FV (fv, _, [(t, _); (brs, _)]) when S.fv_eq_lid fv ref_Tv_Match.lid ->
            BU.bind_opt (unembed e_term t) (fun t ->
            BU.bind_opt (unembed (e_list e_branch) brs) (fun brs ->
            Some <| Tv_Match (t, brs)))

        | FV (fv, _, [(e, _); (t, _); (tacopt, _)]) when S.fv_eq_lid fv ref_Tv_AscT.lid ->
            BU.bind_opt (unembed e_term e) (fun e ->
            BU.bind_opt (unembed e_term t) (fun t ->
            BU.bind_opt (unembed (e_option e_term) tacopt) (fun tacopt ->
            Some <| Tv_AscribedT (e, t, tacopt))))

        | FV (fv, _, [(e, _); (c, _); (tacopt, _)]) when S.fv_eq_lid fv ref_Tv_AscC.lid ->
            BU.bind_opt (unembed e_term e) (fun e ->
            BU.bind_opt (unembed e_comp c) (fun c ->
            BU.bind_opt (unembed (e_option e_term) tacopt) (fun tacopt ->
            Some <| Tv_AscribedC (e, c, tacopt))))

        | FV (fv, _, []) when S.fv_eq_lid fv ref_Tv_Unknown.lid ->
            Some <| Tv_Unknown

        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded term_view: %s" (t_to_string t)));
            None
    in
    mk_emb embed_term_view unembed_term_view (mkFV fstar_refl_term_view_fv [] [])


let e_term_view = e_term_view_aq []

let e_bv_view =
    let embed_bv_view (bvv:bv_view) : t =
        mkFV ref_Mk_bv.fv [] [as_arg (embed e_string bvv.bv_ppname);
                              as_arg (embed e_int    bvv.bv_index);
                              as_arg (embed e_term   bvv.bv_sort)]
    in
    let unembed_bv_view (t : t) : option<bv_view> =
        match t with
        | FV (fv, _, [(nm, _); (idx, _); (s, _)]) when S.fv_eq_lid fv ref_Mk_bv.lid ->
            BU.bind_opt (unembed e_string nm) (fun nm ->
            BU.bind_opt (unembed e_int idx) (fun idx ->
            BU.bind_opt (unembed e_term s) (fun s ->
            Some <| { bv_ppname = nm ; bv_index = idx ; bv_sort = s })))

        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded bv_view: %s" (t_to_string t)));
            None
    in
    mk_emb embed_bv_view unembed_bv_view (mkFV fstar_refl_bv_view_fv [] [])

let e_comp_view =
    let embed_comp_view (cv : comp_view) : t =
        match cv with
        | C_Total (t, md) ->
            mkFV ref_C_Total.fv [] [as_arg (embed e_term t);
                                    as_arg (embed (e_option e_term) md)]

        | C_Lemma (pre, post) ->
            let post = U.unthunk_lemma_post post in
            mkFV ref_C_Lemma.fv [] [as_arg (embed e_term pre); as_arg (embed e_term post)]

        | C_Unknown ->
            mkFV ref_C_Unknown.fv [] []
    in
    let unembed_comp_view (t : t) : option<comp_view> =
        match t with
        | FV (fv, _, [(t, _); (md, _)]) when S.fv_eq_lid fv ref_C_Total.lid ->
            BU.bind_opt (unembed e_term t) (fun t ->
            BU.bind_opt (unembed (e_option e_term) md) (fun md ->
            Some <| C_Total (t, md)))

        | FV (fv, _, [(pre, _); (post, _)]) when S.fv_eq_lid fv ref_C_Lemma.lid ->
            BU.bind_opt (unembed e_term pre) (fun pre ->
            BU.bind_opt (unembed e_term post) (fun post ->
            Some <| C_Lemma (pre, post)))

        | FV (fv, _, []) when S.fv_eq_lid fv ref_C_Unknown.lid ->
            Some <| C_Unknown

        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded comp_view: %s" (t_to_string t)));
            None
    in
    mk_emb embed_comp_view unembed_comp_view (mkFV fstar_refl_comp_view_fv [] [])


(* TODO: move to, Syntax.Embeddings or somewhere better even *)
let e_order =
    let embed_order (o:order) : t =
        match o with
        | Lt -> mkFV ord_Lt_fv [] []
        | Eq -> mkFV ord_Eq_fv [] []
        | Gt -> mkFV ord_Gt_fv [] []
    in
    let unembed_order (t:t) : option<order> =
        match t with
        | FV (fv, _, []) when S.fv_eq_lid fv ord_Lt_lid -> Some Lt
        | FV (fv, _, []) when S.fv_eq_lid fv ord_Eq_lid -> Some Eq
        | FV (fv, _, []) when S.fv_eq_lid fv ord_Gt_lid -> Some Gt
        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded order: %s" (t_to_string t)));
            None
    in
    mk_emb embed_order unembed_order (mkFV (lid_as_fv PC.order_lid delta_constant None) [] [])

let e_sigelt =
    let embed_sigelt (se:sigelt) : t =
        mk_lazy se fstar_refl_sigelt Lazy_sigelt
    in
    let unembed_sigelt (t:t) : option<sigelt> =
        match t with
        | Lazy i when i.lkind = Lazy_sigelt ->
            Some (undyn i.blob)
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
    let embed_ident (i:I.ident) : t =
        embed repr (I.range_of_id i, I.text_of_id i)
    in
    let unembed_ident (t:t) : option<I.ident> =
        match unembed repr t with
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
    let embed_sigelt_view (sev:sigelt_view) : t =
        match sev with
        | Sg_Let (r, fv, univs, ty, t) ->
            mkFV ref_Sg_Let.fv [] [as_arg (embed e_bool r);
                                   as_arg (embed e_fv fv);
                                   as_arg (embed e_univ_names univs);
                                   as_arg (embed e_term ty);
                                   as_arg (embed e_term t)]

        | Sg_Constructor (nm, ty) ->
            mkFV ref_Sg_Constructor.fv [] [as_arg (embed e_string_list nm);
                                           as_arg (embed e_term ty)]

        | Sg_Inductive (nm, univs, bs, t, dcs) ->
            mkFV ref_Sg_Inductive.fv [] [as_arg (embed e_string_list nm);
                                         as_arg (embed e_univ_names univs);
                                         as_arg (embed e_binders bs);
                                         as_arg (embed e_term t);
                                         as_arg (embed (e_list e_string_list) dcs)]

        | Unk ->
            mkFV ref_Unk.fv [] []
    in
    let unembed_sigelt_view (t:t) : option<sigelt_view> =
        match t with
        | FV (fv, _, [(nm, _); (us, _); (bs, _); (t, _); (dcs, _)]) when S.fv_eq_lid fv ref_Sg_Inductive.lid ->
            BU.bind_opt (unembed e_string_list nm) (fun nm ->
            BU.bind_opt (unembed e_univ_names us) (fun us ->
            BU.bind_opt (unembed e_binders bs) (fun bs ->
            BU.bind_opt (unembed e_term t) (fun t ->
            BU.bind_opt (unembed (e_list e_string_list) dcs) (fun dcs ->
            Some <| Sg_Inductive (nm, us, bs, t, dcs))))))

        | FV (fv, _, [(r, _); (fvar, _); (univs, _); (ty, _); (t, _)]) when S.fv_eq_lid fv ref_Sg_Let.lid ->
            BU.bind_opt (unembed e_bool r) (fun r ->
            BU.bind_opt (unembed e_fv fvar) (fun fvar ->
            BU.bind_opt (unembed e_univ_names univs) (fun univs ->
            BU.bind_opt (unembed e_term ty) (fun ty ->
            BU.bind_opt (unembed e_term t) (fun t ->
            Some <| Sg_Let (r, fvar, univs, ty, t))))))

        | FV (fv, _, []) when S.fv_eq_lid fv ref_Unk.lid ->
            Some Unk

        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded sigelt_view: %s" (t_to_string t)));
            None
    in
    mk_emb embed_sigelt_view unembed_sigelt_view (mkFV fstar_refl_sigelt_view_fv [] [])

let e_exp =
    let rec embed_exp (e:exp) : t =
        match e with
        | Data.Unit  ->         mkFV ref_E_Unit.fv [] []
        | Data.Var i ->         mkFV ref_E_Var.fv  [] [as_arg (Constant (Int i))]
        | Data.Mult (e1, e2) -> mkFV ref_E_Mult.fv [] [as_arg (embed_exp e1); as_arg (embed_exp e2)]
    in
    let rec unembed_exp (t: t) : option<exp> =
        match t with
        | FV (fv, _, []) when S.fv_eq_lid fv ref_E_Unit.lid ->
            Some Data.Unit

        | FV (fv, _, [(i, _)]) when S.fv_eq_lid fv ref_E_Var.lid ->
            BU.bind_opt (unembed e_int i) (fun i ->
            Some <| Data.Var i)

        | FV (fv, _, [(e1, _); (e2, _)]) when S.fv_eq_lid fv ref_E_Mult.lid ->
            BU.bind_opt (unembed_exp e1) (fun e1 ->
            BU.bind_opt (unembed_exp e2) (fun e2 ->
            Some <| Data.Mult (e1, e2)))
        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded exp: %s" (t_to_string t)));
            None
    in
    mk_emb embed_exp unembed_exp (mkFV fstar_refl_exp_fv [] [])

let e_binder_view = e_tuple2 e_bv e_aqualv

let e_attribute  = e_term
let e_attributes = e_list e_attribute
