#light "off"
module FStar.Reflection.Embeddings

open FStar.All
open FStar.Reflection.Data
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
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
module EMB = FStar.Syntax.Embeddings
open FStar.Reflection.Basic //needed for inspect_fv, but that feels wrong
module NBETerm = FStar.TypeChecker.NBETerm
module PC = FStar.Parser.Const
module O = FStar.Options
module RD = FStar.Reflection.Data

open FStar.Dyn

(*
 * embed   : from compiler to user
 * unembed : from user to compiler
 *)

(* -------------------------------------------------------------------------------------- *)
(* ------------------------------------- EMBEDDINGS ------------------------------------- *)
(* -------------------------------------------------------------------------------------- *)
let mk_emb f g t =
    mk_emb (fun x r _topt _norm -> f r x)
           (fun x w _norm -> g w x)
           (EMB.term_as_fv t)
let embed e r x = embed e x r None id_norm_cb
let unembed' w e x = unembed e x w id_norm_cb

let e_bv =
    let embed_bv (rng:Range.range) (bv:bv) : term =
        U.mk_lazy bv fstar_refl_bv Lazy_bv (Some rng)
    in
    let unembed_bv w (t:term) : option<bv> =
        match (SS.compress t).n with
        | Tm_lazy {blob=b; lkind=Lazy_bv} ->
            Some (undyn b)
        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded bv: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_bv unembed_bv fstar_refl_bv

let e_binder =
    let embed_binder (rng:Range.range) (b:binder) : term =
        U.mk_lazy b fstar_refl_binder Lazy_binder (Some rng)
    in
    let unembed_binder w (t:term) : option<binder> =
        match (SS.compress t).n with
        | Tm_lazy {blob=b; lkind=Lazy_binder} ->
            Some (undyn b)
        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded binder: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_binder unembed_binder fstar_refl_binder

let e_optionstate =
    let embed_optionstate (rng:Range.range) (b:O.optionstate) : term =
        U.mk_lazy b fstar_refl_optionstate Lazy_optionstate (Some rng)
    in
    let unembed_optionstate w (t:term) : option<O.optionstate> =
        match (SS.compress t).n with
        | Tm_lazy {blob=b; lkind=Lazy_optionstate} ->
            Some (undyn b)
        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded optionstate: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_optionstate unembed_optionstate fstar_refl_optionstate

let _ = FStar.Reflection.Basic.e_optionstate_hook := Some e_optionstate

let rec mapM_opt (f : ('a -> option<'b>)) (l : list<'a>) : option<list<'b>> =
    match l with
    | [] -> Some []
    | x::xs ->
        BU.bind_opt (f x) (fun x ->
        BU.bind_opt (mapM_opt f xs) (fun xs ->
        Some (x :: xs)))

let e_term_aq aq =
    let embed_term (rng:Range.range) (t:term) : term =
        let qi = { qkind = Quote_static; antiquotes = aq } in
        S.mk (Tm_quoted (t, qi)) rng
    in
    let rec unembed_term w (t:term) : option<term> =
        let apply_antiquotes (t:term) (aq:antiquotations) : option<term> =
            BU.bind_opt (mapM_opt (fun (bv, e) -> BU.bind_opt (unembed_term w e) (fun e -> Some (NT (bv, e))))
                                   aq) (fun s ->
            Some (SS.subst s t))
        in
        let t = U.unmeta t in
        match (SS.compress t).n with
        | Tm_quoted (tm, qi) ->
            apply_antiquotes tm qi.antiquotes
        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded term: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_term unembed_term S.t_term

let e_term = e_term_aq []

let e_aqualv =
    let embed_aqualv (rng:Range.range) (q : aqualv) : term =
        let r =
        match q with
        | Data.Q_Explicit -> ref_Q_Explicit.t
        | Data.Q_Implicit -> ref_Q_Implicit.t
        | Data.Q_Meta t   ->
            S.mk_Tm_app ref_Q_Meta.t [S.as_arg (embed e_term rng t)]
                        Range.dummyRange
        in { r with pos = rng }
    in
    let unembed_aqualv w (t : term) : option<aqualv> =
        let t = U.unascribe t in
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_Q_Explicit.lid -> Some Data.Q_Explicit
        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_Q_Implicit.lid -> Some Data.Q_Implicit
        | Tm_fvar fv, [(t, _)] when S.fv_eq_lid fv ref_Q_Meta.lid ->
            BU.bind_opt (unembed' w e_term t) (fun t ->
            Some (Data.Q_Meta t))

        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded aqualv: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_aqualv unembed_aqualv  fstar_refl_aqualv

let e_binders = e_list e_binder

let e_fv =
    let embed_fv (rng:Range.range) (fv:fv) : term =
        U.mk_lazy fv fstar_refl_fv Lazy_fvar (Some rng)
    in
    let unembed_fv w (t:term) : option<fv> =
        match (SS.compress t).n with
        | Tm_lazy {blob=b; lkind=Lazy_fvar} ->
            Some (undyn b)
        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded fvar: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_fv unembed_fv fstar_refl_fv

let e_comp =
    let embed_comp (rng:Range.range) (c:comp) : term =
        U.mk_lazy c fstar_refl_comp Lazy_comp (Some rng)
    in
    let unembed_comp w (t:term) : option<comp> =
        match (SS.compress t).n with
        | Tm_lazy {blob=b; lkind=Lazy_comp} ->
            Some (undyn b)
        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded comp: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_comp unembed_comp fstar_refl_comp

let e_env =
    let embed_env (rng:Range.range) (e:Env.env) : term =
        U.mk_lazy e fstar_refl_env Lazy_env (Some rng)
    in
    let unembed_env w (t:term) : option<Env.env> =
        match (SS.compress t).n with
        | Tm_lazy {blob=b; lkind=Lazy_env} ->
            Some (undyn b)
        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded env: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_env unembed_env fstar_refl_env

let e_const =
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
            S.mk_Tm_app ref_C_String.t [S.as_arg (embed e_string rng s)]
                        Range.dummyRange

        | C_Range r ->
            S.mk_Tm_app ref_C_Range.t [S.as_arg (embed e_range rng r)]
                        Range.dummyRange

        | C_Reify -> ref_C_Reify.t

        | C_Reflect ns ->
            S.mk_Tm_app ref_C_Reflect.t [S.as_arg (embed e_string_list rng ns)]
                        Range.dummyRange

        in { r with pos = rng }
    in
    let unembed_const w (t:term) : option<vconst> =
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
            BU.bind_opt (unembed' w e_int i) (fun i ->
            Some <| C_Int i)

        | Tm_fvar fv, [(s, _)] when S.fv_eq_lid fv ref_C_String.lid ->
            BU.bind_opt (unembed' w e_string s) (fun s ->
            Some <| C_String s)

        | Tm_fvar fv, [(r, _)] when S.fv_eq_lid fv ref_C_Range.lid ->
            BU.bind_opt (unembed' w e_range r) (fun r ->
            Some <| C_Range r)

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_C_Reify.lid ->
            Some <| C_Reify

        | Tm_fvar fv, [(ns, _)] when S.fv_eq_lid fv ref_C_Reflect.lid ->
            BU.bind_opt (unembed' w e_string_list ns) (fun ns ->
            Some <| C_Reflect ns)

        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded vconst: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_const unembed_const fstar_refl_vconst

let rec e_pattern' () =
    let rec embed_pattern (rng:Range.range) (p : pattern) : term =
        match p with
        | Pat_Constant c ->
            S.mk_Tm_app ref_Pat_Constant.t [S.as_arg (embed e_const rng c)] rng
        | Pat_Cons (fv, ps) ->
            S.mk_Tm_app ref_Pat_Cons.t [S.as_arg (embed e_fv rng fv); S.as_arg (embed (e_list (e_tuple2 (e_pattern' ()) e_bool)) rng ps)] rng
        | Pat_Var bv ->
            S.mk_Tm_app ref_Pat_Var.t [S.as_arg (embed e_bv rng bv)] rng
        | Pat_Wild bv ->
            S.mk_Tm_app ref_Pat_Wild.t [S.as_arg (embed e_bv rng bv)] rng
        | Pat_Dot_Term (bv, t) ->
            S.mk_Tm_app ref_Pat_Dot_Term.t [S.as_arg (embed e_bv rng bv);
                                            S.as_arg (embed e_term rng t)]
                        rng
    in
    let rec unembed_pattern w (t : term) : option<pattern> =
        let t = U.unascribe t in
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [(c, _)] when S.fv_eq_lid fv ref_Pat_Constant.lid ->
            BU.bind_opt (unembed' w e_const c) (fun c ->
            Some <| Pat_Constant c)

        | Tm_fvar fv, [(f, _); (ps, _)] when S.fv_eq_lid fv ref_Pat_Cons.lid ->
            BU.bind_opt (unembed' w e_fv f) (fun f ->
            BU.bind_opt (unembed' w (e_list (e_tuple2 (e_pattern' ()) e_bool)) ps) (fun ps ->
            Some <| Pat_Cons (f, ps)))

        | Tm_fvar fv, [(bv, _)] when S.fv_eq_lid fv ref_Pat_Var.lid ->
            BU.bind_opt (unembed' w e_bv bv) (fun bv ->
            Some <| Pat_Var bv)

        | Tm_fvar fv, [(bv, _)] when S.fv_eq_lid fv ref_Pat_Wild.lid ->
            BU.bind_opt (unembed' w e_bv bv) (fun bv ->
            Some <| Pat_Wild bv)

        | Tm_fvar fv, [(bv, _); (t, _)] when S.fv_eq_lid fv ref_Pat_Dot_Term.lid ->
            BU.bind_opt (unembed' w e_bv bv) (fun bv ->
            BU.bind_opt (unembed' w e_term t) (fun t ->
            Some <| Pat_Dot_Term (bv, t)))

        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded pattern: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_pattern unembed_pattern fstar_refl_pattern

let e_pattern = e_pattern' ()

let e_branch = e_tuple2 e_pattern e_term
let e_argv   = e_tuple2 e_term    e_aqualv

let e_args   = e_list e_argv

let e_branch_aq aq = e_tuple2 e_pattern      (e_term_aq aq)
let e_argv_aq   aq = e_tuple2 (e_term_aq aq) e_aqualv

let e_term_view_aq aq =
    let embed_term_view (rng:Range.range) (t:term_view) : term =
        match t with
        | Tv_FVar fv ->
            S.mk_Tm_app ref_Tv_FVar.t [S.as_arg (embed e_fv rng fv)]
                        rng

        | Tv_BVar fv ->
            S.mk_Tm_app ref_Tv_BVar.t [S.as_arg (embed e_bv rng fv)]
                        rng

        | Tv_Var bv ->
            S.mk_Tm_app ref_Tv_Var.t [S.as_arg (embed e_bv rng bv)]
                        rng

        | Tv_App (hd, a) ->
            S.mk_Tm_app ref_Tv_App.t [S.as_arg (embed (e_term_aq aq) rng hd); S.as_arg (embed (e_argv_aq aq) rng a)]
                        rng

        | Tv_Abs (b, t) ->
            S.mk_Tm_app ref_Tv_Abs.t [S.as_arg (embed e_binder rng b); S.as_arg (embed (e_term_aq aq) rng t)]
                        rng

        | Tv_Arrow (b, c) ->
            S.mk_Tm_app ref_Tv_Arrow.t [S.as_arg (embed e_binder rng b); S.as_arg (embed e_comp rng c)]
                        rng

        | Tv_Type u ->
            S.mk_Tm_app ref_Tv_Type.t [S.as_arg (embed e_unit rng ())]
                        rng

        | Tv_Refine (bv, t) ->
            S.mk_Tm_app ref_Tv_Refine.t [S.as_arg (embed e_bv rng bv); S.as_arg (embed (e_term_aq aq) rng t)]
                        rng

        | Tv_Const c ->
            S.mk_Tm_app ref_Tv_Const.t [S.as_arg (embed e_const rng c)]
                        rng

        | Tv_Uvar (u, d) ->
            S.mk_Tm_app ref_Tv_Uvar.t
                        [S.as_arg (embed e_int rng u);
                         S.as_arg (U.mk_lazy (u,d) U.t_ctx_uvar_and_sust Lazy_uvar None)]
                        rng

        | Tv_Let (r, attrs, b, t1, t2) ->
            S.mk_Tm_app ref_Tv_Let.t [S.as_arg (embed e_bool rng r);
                                      S.as_arg (embed (e_list e_term) rng attrs);
                                      S.as_arg (embed e_bv rng b);
                                      S.as_arg (embed (e_term_aq aq) rng t1);
                                      S.as_arg (embed (e_term_aq aq) rng t2)]
                        rng

        | Tv_Match (t, brs) ->
            S.mk_Tm_app ref_Tv_Match.t [S.as_arg (embed (e_term_aq aq) rng t);
                                        S.as_arg (embed (e_list (e_branch_aq aq)) rng brs)]
                        rng

        | Tv_AscribedT (e, t, tacopt) ->
            S.mk_Tm_app ref_Tv_AscT.t
                        [S.as_arg (embed (e_term_aq aq) rng e);
                         S.as_arg (embed (e_term_aq aq) rng t);
                         S.as_arg (embed (e_option (e_term_aq aq)) rng tacopt)]
                        rng

        | Tv_AscribedC (e, c, tacopt) ->
            S.mk_Tm_app ref_Tv_AscC.t
                        [S.as_arg (embed (e_term_aq aq) rng e);
                         S.as_arg (embed e_comp rng c);
                         S.as_arg (embed (e_option (e_term_aq aq)) rng tacopt)]
                        rng

        | Tv_Unknown ->
            { ref_Tv_Unknown.t with pos = rng }
    in
    let unembed_term_view w (t:term) : option<term_view> =
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [(b, _)] when S.fv_eq_lid fv ref_Tv_Var.lid ->
            BU.bind_opt (unembed' w e_bv b) (fun b ->
            Some <| Tv_Var b)

        | Tm_fvar fv, [(b, _)] when S.fv_eq_lid fv ref_Tv_BVar.lid ->
            BU.bind_opt (unembed' w e_bv b) (fun b ->
            Some <| Tv_BVar b)

        | Tm_fvar fv, [(f, _)] when S.fv_eq_lid fv ref_Tv_FVar.lid ->
            BU.bind_opt (unembed' w e_fv f) (fun f ->
            Some <| Tv_FVar f)

        | Tm_fvar fv, [(l, _); (r, _)] when S.fv_eq_lid fv ref_Tv_App.lid ->
            BU.bind_opt (unembed' w e_term l) (fun l ->
            BU.bind_opt (unembed' w e_argv r) (fun r ->
            Some <| Tv_App (l, r)))

        | Tm_fvar fv, [(b, _); (t, _)] when S.fv_eq_lid fv ref_Tv_Abs.lid ->
            BU.bind_opt (unembed' w e_binder b) (fun b ->
            BU.bind_opt (unembed' w e_term t) (fun t ->
            Some <| Tv_Abs (b, t)))

        | Tm_fvar fv, [(b, _); (t, _)] when S.fv_eq_lid fv ref_Tv_Arrow.lid ->
            BU.bind_opt (unembed' w e_binder b) (fun b ->
            BU.bind_opt (unembed' w e_comp t) (fun c ->
            Some <| Tv_Arrow (b, c)))

        | Tm_fvar fv, [(u, _)] when S.fv_eq_lid fv ref_Tv_Type.lid ->
            BU.bind_opt (unembed' w e_unit u) (fun u ->
            Some <| Tv_Type u)

        | Tm_fvar fv, [(b, _); (t, _)] when S.fv_eq_lid fv ref_Tv_Refine.lid ->
            BU.bind_opt (unembed' w e_bv b) (fun b ->
            BU.bind_opt (unembed' w e_term t) (fun t ->
            Some <| Tv_Refine (b, t)))

        | Tm_fvar fv, [(c, _)] when S.fv_eq_lid fv ref_Tv_Const.lid ->
            BU.bind_opt (unembed' w e_const c) (fun c ->
            Some <| Tv_Const c)

        | Tm_fvar fv, [(u, _); (l, _)] when S.fv_eq_lid fv ref_Tv_Uvar.lid ->
            BU.bind_opt (unembed' w e_int u) (fun u ->
            let ctx_u_s : ctx_uvar_and_subst = U.unlazy_as_t Lazy_uvar l in
            Some <| Tv_Uvar (u, ctx_u_s))

        | Tm_fvar fv, [(r, _); (attrs, _); (b, _); (t1, _); (t2, _)] when S.fv_eq_lid fv ref_Tv_Let.lid ->
            BU.bind_opt (unembed' w e_bool r) (fun r ->
            BU.bind_opt (unembed' w (e_list e_term) attrs) (fun attrs ->
            BU.bind_opt (unembed' w e_bv b) (fun b ->
            BU.bind_opt (unembed' w e_term t1) (fun t1 ->
            BU.bind_opt (unembed' w e_term t2) (fun t2 ->
            Some <| Tv_Let (r, attrs, b, t1, t2))))))

        | Tm_fvar fv, [(t, _); (brs, _)] when S.fv_eq_lid fv ref_Tv_Match.lid ->
            BU.bind_opt (unembed' w e_term t) (fun t ->
            BU.bind_opt (unembed' w (e_list e_branch) brs) (fun brs ->
            Some <| Tv_Match (t, brs)))

        | Tm_fvar fv, [(e, _); (t, _); (tacopt, _)] when S.fv_eq_lid fv ref_Tv_AscT.lid ->
            BU.bind_opt (unembed' w e_term e) (fun e ->
            BU.bind_opt (unembed' w e_term t) (fun t ->
            BU.bind_opt (unembed' w (e_option e_term) tacopt) (fun tacopt ->
            Some <| Tv_AscribedT (e, t, tacopt))))

        | Tm_fvar fv, [(e, _); (c, _); (tacopt, _)] when S.fv_eq_lid fv ref_Tv_AscC.lid ->
            BU.bind_opt (unembed' w e_term e) (fun e ->
            BU.bind_opt (unembed' w e_comp c) (fun c ->
            BU.bind_opt (unembed' w (e_option e_term) tacopt) (fun tacopt ->
            Some <| Tv_AscribedC (e, c, tacopt))))

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_Tv_Unknown.lid ->
            Some <| Tv_Unknown

        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded term_view: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_term_view unembed_term_view fstar_refl_term_view


let e_term_view = e_term_view_aq []


(* embeds as a string list *)
let e_lid : embedding<I.lid> =
    let embed rng lid : term =
        embed e_string_list rng (I.path_of_lid lid)
    in
    let unembed w t : option<I.lid> =
        BU.map_opt (unembed' w e_string_list t) (fun p -> I.lid_of_path p t.pos)
    in
    EMB.mk_emb_full (fun x r _ _ -> embed r x)
               (fun x w _ -> unembed w x)
               (t_list_of t_string)
               I.string_of_lid
               ET_abstract


let e_bv_view =
    let embed_bv_view (rng:Range.range) (bvv:bv_view) : term =
        S.mk_Tm_app ref_Mk_bv.t [S.as_arg (embed e_string rng bvv.bv_ppname);
                                 S.as_arg (embed e_int    rng bvv.bv_index);
                                 S.as_arg (embed e_term   rng bvv.bv_sort)]
                    rng
    in
    let unembed_bv_view w (t : term) : option<bv_view> =
        let t = U.unascribe t in
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [(nm, _); (idx, _); (s, _)] when S.fv_eq_lid fv ref_Mk_bv.lid ->
            BU.bind_opt (unembed' w e_string nm) (fun nm ->
            BU.bind_opt (unembed' w e_int idx) (fun idx ->
            BU.bind_opt (unembed' w e_term s) (fun s ->
            Some <| { bv_ppname = nm ; bv_index = idx ; bv_sort = s })))

        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded bv_view: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_bv_view unembed_bv_view fstar_refl_bv_view

let e_comp_view =
    let embed_comp_view (rng:Range.range) (cv : comp_view) : term =
        match cv with
        | C_Total (t, md) ->
            S.mk_Tm_app ref_C_Total.t [S.as_arg (embed e_term rng t);
                                       S.as_arg (embed (e_option e_term) rng md)]
                        rng

        | C_GTotal (t, md) ->
            S.mk_Tm_app ref_C_GTotal.t [S.as_arg (embed e_term rng t);
                                       S.as_arg (embed (e_option e_term) rng md)]
                        rng

        | C_Lemma (pre, post, pats) ->
            S.mk_Tm_app ref_C_Lemma.t [S.as_arg (embed e_term rng pre); S.as_arg (embed e_term rng post); S.as_arg (embed e_term rng pats)]
                        rng

        | C_Eff (us, eff, res, args) ->
            S.mk_Tm_app ref_C_Eff.t
                [ S.as_arg (embed e_unit rng ()) (* TODO *)
                ; S.as_arg (embed e_string_list rng eff)
                ; S.as_arg (embed e_term rng res)
                ; S.as_arg (embed (e_list e_argv) rng args)] rng


    in
    let unembed_comp_view w (t : term) : option<comp_view> =
        let t = U.unascribe t in
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [(t, _); (md, _)] when S.fv_eq_lid fv ref_C_Total.lid ->
            BU.bind_opt (unembed' w e_term t) (fun t ->
            BU.bind_opt (unembed' w (e_option e_term) md) (fun md ->
            Some <| C_Total (t, md)))

        | Tm_fvar fv, [(t, _); (md, _)] when S.fv_eq_lid fv ref_C_GTotal.lid ->
            BU.bind_opt (unembed' w e_term t) (fun t ->
            BU.bind_opt (unembed' w (e_option e_term) md) (fun md ->
            Some <| C_GTotal (t, md)))

        | Tm_fvar fv, [(pre, _); (post, _); (pats, _)] when S.fv_eq_lid fv ref_C_Lemma.lid ->
            BU.bind_opt (unembed' w e_term pre) (fun pre ->
            BU.bind_opt (unembed' w e_term post) (fun post ->
            BU.bind_opt (unembed' w e_term pats) (fun pats ->
            Some <| C_Lemma (pre, post, pats))))

        | Tm_fvar fv, [(us, _); (eff, _); (res, _); (args, _)]
                when S.fv_eq_lid fv ref_C_Eff.lid ->
            BU.bind_opt (unembed' w e_unit us)    (fun us -> (* TODO *)
            BU.bind_opt (unembed' w e_string_list eff)    (fun eff ->
            BU.bind_opt (unembed' w e_term res)   (fun res->
            BU.bind_opt (unembed' w (e_list e_argv) args)  (fun args ->
            Some <| C_Eff ([], eff, res, args)))))

        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded comp_view: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_comp_view unembed_comp_view fstar_refl_comp_view


(* TODO: move to, Syntax.Embeddings or somewhere better even *)
let e_order =
    let embed_order (rng:Range.range) (o:order) : term =
        let r =
        match o with
        | Lt -> ord_Lt
        | Eq -> ord_Eq
        | Gt -> ord_Gt
        in { r with pos = rng }
    in
    let unembed_order w (t:term) : option<order> =
        let t = U.unascribe t in
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [] when S.fv_eq_lid fv ord_Lt_lid -> Some Lt
        | Tm_fvar fv, [] when S.fv_eq_lid fv ord_Eq_lid -> Some Eq
        | Tm_fvar fv, [] when S.fv_eq_lid fv ord_Gt_lid -> Some Gt
        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded order: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_order unembed_order S.t_order

let e_sigelt =
    let embed_sigelt (rng:Range.range) (se:sigelt) : term =
        U.mk_lazy se fstar_refl_sigelt Lazy_sigelt (Some rng)
    in
    let unembed_sigelt w (t:term) : option<sigelt> =
        match (SS.compress t).n with
        | Tm_lazy {blob=b; lkind=Lazy_sigelt} ->
            Some (undyn b)
        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded sigelt: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_sigelt unembed_sigelt fstar_refl_sigelt

let e_ident : embedding<I.ident> =
    let repr = e_tuple2 e_string e_range in
    embed_as repr
             I.mk_ident
             (fun i -> I.string_of_id i, I.range_of_id i)
             (Some fstar_refl_ident)

let e_univ_name =
    set_type fstar_refl_univ_name e_ident

let e_univ_names = e_list e_univ_name

let e_sigelt_view =
    let embed_sigelt_view (rng:Range.range) (sev:sigelt_view) : term =
        match sev with
        | Sg_Let (r, fv, univs, ty, t) ->
            S.mk_Tm_app ref_Sg_Let.t
                        [S.as_arg (embed e_bool rng r);
                            S.as_arg (embed e_fv rng fv);
                            S.as_arg (embed e_univ_names rng univs);
                            S.as_arg (embed e_term rng ty);
                            S.as_arg (embed e_term rng t)]
                        rng

        | Sg_Constructor (nm, ty) ->
            S.mk_Tm_app ref_Sg_Constructor.t
                        [S.as_arg (embed e_string_list rng nm);
                            S.as_arg (embed e_term rng ty)]
                        rng

        | Sg_Inductive (nm, univs, bs, t, dcs) ->
            S.mk_Tm_app ref_Sg_Inductive.t
                        [S.as_arg (embed e_string_list rng nm);
                            S.as_arg (embed e_univ_names rng univs);
                            S.as_arg (embed e_binders rng bs);
                            S.as_arg (embed e_term rng t);
                            S.as_arg (embed (e_list e_string_list)  rng dcs)]
                        rng

        | Unk ->
            { ref_Unk.t with pos = rng }
    in
    let unembed_sigelt_view w (t:term) : option<sigelt_view> =
        let t = U.unascribe t in
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [(nm, _); (us, _); (bs, _); (t, _); (dcs, _)] when S.fv_eq_lid fv ref_Sg_Inductive.lid ->
            BU.bind_opt (unembed' w e_string_list nm) (fun nm ->
            BU.bind_opt (unembed' w e_univ_names us) (fun us ->
            BU.bind_opt (unembed' w e_binders bs) (fun bs ->
            BU.bind_opt (unembed' w e_term t) (fun t ->
            BU.bind_opt (unembed' w (e_list e_string_list) dcs) (fun dcs ->
            Some <| Sg_Inductive (nm, us, bs, t, dcs))))))

        | Tm_fvar fv, [(r, _); (fvar, _); (univs, _); (ty, _); (t, _)] when S.fv_eq_lid fv ref_Sg_Let.lid ->
            BU.bind_opt (unembed' w e_bool r) (fun r ->
            BU.bind_opt (unembed' w e_fv fvar) (fun fvar ->
            BU.bind_opt (unembed' w e_univ_names univs) (fun univs ->
            BU.bind_opt (unembed' w e_term ty) (fun ty ->
            BU.bind_opt (unembed' w e_term t) (fun t ->
            Some <| Sg_Let (r, fvar, univs, ty, t))))))

        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_Unk.lid ->
            Some Unk

        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded sigelt_view: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_sigelt_view unembed_sigelt_view fstar_refl_sigelt_view

let e_exp =
    let rec embed_exp (rng:Range.range) (e:exp) : term =
        let r =
        match e with
        | Unit    -> ref_E_Unit.t
        | Var i ->
            S.mk_Tm_app ref_E_Var.t [S.as_arg (U.exp_int (Z.string_of_big_int i))]
                        Range.dummyRange
        | Mult (e1, e2) ->
            S.mk_Tm_app ref_E_Mult.t [S.as_arg (embed_exp rng e1); S.as_arg (embed_exp rng e2)]
                        Range.dummyRange
        in { r with pos = rng }
    in
    let rec unembed_exp w (t: term) : option<exp> =
        let t = U.unascribe t in
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_E_Unit.lid ->
            Some Unit

        | Tm_fvar fv, [(i, _)] when S.fv_eq_lid fv ref_E_Var.lid ->
            BU.bind_opt (unembed' w e_int i) (fun i ->
            Some <| Var i)

        | Tm_fvar fv, [(e1, _); (e2, _)] when S.fv_eq_lid fv ref_E_Mult.lid ->
            BU.bind_opt (unembed_exp w e1) (fun e1 ->
            BU.bind_opt (unembed_exp w e2) (fun e2 ->
            Some <| Mult (e1, e2)))
        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded exp: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_exp unembed_exp fstar_refl_exp


let e_binder_view = e_tuple2 e_bv e_aqualv

let e_attribute  = e_term
let e_attributes = e_list e_attribute

let e_qualifier =
    let embed (rng:Range.range) (q:RD.qualifier) : term =
        let r =
        match q with
        | RD.Assumption                       -> ref_qual_Assumption.t
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
            S.mk_Tm_app ref_qual_Reflectable.t [S.as_arg (embed e_lid rng l)]
                        Range.dummyRange

        | RD.Discriminator l ->
            S.mk_Tm_app ref_qual_Discriminator.t [S.as_arg (embed e_lid rng l)]
                        Range.dummyRange

        | RD.Action l ->
            S.mk_Tm_app ref_qual_Action.t [S.as_arg (embed e_lid rng l)]
                        Range.dummyRange

        | RD.Projector (l, i) ->
            S.mk_Tm_app ref_qual_Projector.t [S.as_arg (embed e_lid rng l);
                                              S.as_arg (embed e_ident rng i)]
                        Range.dummyRange

        | RD.RecordType (ids1, ids2) ->
            S.mk_Tm_app ref_qual_RecordType.t [S.as_arg (embed (e_list e_ident) rng ids1);
                                               S.as_arg (embed (e_list e_ident) rng ids2)]
                        Range.dummyRange

        | RD.RecordConstructor (ids1, ids2) ->
            S.mk_Tm_app ref_qual_RecordConstructor.t [S.as_arg (embed (e_list e_ident) rng ids1);
                                                      S.as_arg (embed (e_list e_ident) rng ids2)]
                        Range.dummyRange

        in { r with pos = rng }
    in
    let unembed w (t: term) : option<RD.qualifier> =
        let t = U.unascribe t in
        let hd, args = U.head_and_args t in
        match (U.un_uinst hd).n, args with
        | Tm_fvar fv, [] when S.fv_eq_lid fv ref_qual_Assumption.lid ->
             Some RD.Assumption

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
            BU.bind_opt (unembed' w e_lid l) (fun l ->
            Some <| RD.Reflectable l)

        | Tm_fvar fv, [(l, _)] when S.fv_eq_lid fv ref_qual_Discriminator.lid ->
            BU.bind_opt (unembed' w e_lid l) (fun l ->
            Some <| RD.Discriminator l)

        | Tm_fvar fv, [(l, _)] when S.fv_eq_lid fv ref_qual_Action.lid ->
            BU.bind_opt (unembed' w e_lid l) (fun l ->
            Some <| RD.Action l)

        | Tm_fvar fv, [(l, _); (i, _)] when S.fv_eq_lid fv ref_qual_Projector.lid ->
            BU.bind_opt (unembed' w e_lid l) (fun l ->
            BU.bind_opt (unembed' w e_ident i) (fun i ->
            Some <| RD.Projector (l, i)))

        | Tm_fvar fv, [(ids1, _); (ids2, _)] when S.fv_eq_lid fv ref_qual_RecordType.lid ->
            BU.bind_opt (unembed' w (e_list e_ident) ids1) (fun ids1 ->
            BU.bind_opt (unembed' w (e_list e_ident) ids2) (fun ids2 ->
            Some <| RD.RecordType (ids1, ids2)))

        | Tm_fvar fv, [(ids1, _); (ids2, _)] when S.fv_eq_lid fv ref_qual_RecordConstructor.lid ->
            BU.bind_opt (unembed' w (e_list e_ident) ids1) (fun ids1 ->
            BU.bind_opt (unembed' w (e_list e_ident) ids2) (fun ids2 ->
            Some <| RD.RecordConstructor (ids1, ids2)))

        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded qualifier: %s" (Print.term_to_string t)));
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
    S.mk_Tm_app fstar_refl_pack_bv.t [S.as_arg (embed e_bv_view i.rng (inspect_bv bv))]
                i.rng

(* TODO: non-uniform *)
let unfold_lazy_binder (i : lazyinfo) : term =
    let binder : binder = undyn i.blob in
    let bv, aq = inspect_binder binder in
    S.mk_Tm_app fstar_refl_pack_binder.t [S.as_arg (embed e_bv i.rng bv);
                                        S.as_arg (embed e_aqualv i.rng aq)]
                i.rng

let unfold_lazy_fvar (i : lazyinfo) : term =
    let fv : fv = undyn i.blob in
    S.mk_Tm_app fstar_refl_pack_fv.t [S.as_arg (embed (e_list e_string) i.rng (inspect_fv fv))]
                i.rng

let unfold_lazy_comp (i : lazyinfo) : term =
    let comp : comp = undyn i.blob in
    S.mk_Tm_app fstar_refl_pack_comp.t [S.as_arg (embed e_comp_view i.rng (inspect_comp comp))]
                i.rng

let unfold_lazy_env (i : lazyinfo) : term =
    (* Not needed, metaprograms never see concrete environments. *)
    U.exp_unit

let unfold_lazy_optionstate (i : lazyinfo) : term =
    (* Not needed, metaprograms never see concrete optionstates . *)
    U.exp_unit

let unfold_lazy_sigelt (i : lazyinfo) : term =
    let sigelt : sigelt = undyn i.blob in
    S.mk_Tm_app fstar_refl_pack_sigelt.t [S.as_arg (embed e_sigelt_view i.rng (inspect_sigelt sigelt))]
                i.rng
