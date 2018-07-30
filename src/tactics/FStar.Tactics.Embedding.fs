#light "off"
module FStar.Tactics.Embedding
open FStar
open FStar.ST
open FStar.All
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
open FStar.Util

module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module PC = FStar.Parser.Const
module Env = FStar.TypeChecker.Env
module BU = FStar.Util
module C = FStar.Const
module U = FStar.Syntax.Util
module Rel = FStar.TypeChecker.Rel
module Print = FStar.Syntax.Print
module TcUtil = FStar.TypeChecker.Util
module N = FStar.TypeChecker.Normalize
module Err = FStar.Errors
module NBETerm = FStar.TypeChecker.NBETerm
module NBET    = FStar.TypeChecker.NBETerm
module NBE = FStar.TypeChecker.NBE

open FStar.Tactics.Types
open FStar.Tactics.Result
open FStar.Tactics.Basic

open FStar.Reflection.Basic
open FStar.Reflection.Data

type name = bv

let fstar_tactics_lid' s = PC.fstar_tactics_lid' s
let lid_as_tm l = S.lid_as_fv l delta_constant None |> S.fv_to_tm
let mk_tactic_lid_as_term (s:string) = lid_as_tm (fstar_tactics_lid' ["Effect"; s])

let lid_as_data_fv l = S.lid_as_fv l delta_constant (Some Data_ctor)
let lid_as_data_tm l = S.fv_to_tm (lid_as_data_fv l)
let fstar_tactics_lid_as_data_tm s = lid_as_data_tm (fstar_tactics_lid' ["Effect";s])

let fstar_tactics_Failed_lid  = fstar_tactics_lid' ["Result"; "Failed"]
let fstar_tactics_Success_lid = fstar_tactics_lid' ["Result"; "Success"]

let fstar_tactics_Failed_tm  = lid_as_data_tm fstar_tactics_Failed_lid
let fstar_tactics_Success_tm = lid_as_data_tm fstar_tactics_Success_lid
let fstar_tactics_Failed_fv  = lid_as_data_fv fstar_tactics_Failed_lid
let fstar_tactics_Success_fv = lid_as_data_fv fstar_tactics_Success_lid

let fstar_tactics_topdown_lid = fstar_tactics_lid' ["Types"; "TopDown"]
let fstar_tactics_bottomup_lid = fstar_tactics_lid' ["Types"; "BottomUp"]

let fstar_tactics_topdown  = lid_as_data_tm fstar_tactics_topdown_lid
let fstar_tactics_bottomup = lid_as_data_tm fstar_tactics_bottomup_lid
let fstar_tactics_topdown_fv  = lid_as_data_fv fstar_tactics_topdown_lid
let fstar_tactics_bottomup_fv = lid_as_data_fv fstar_tactics_bottomup_lid

let fstar_tactics_SMT_lid   = fstar_tactics_lid' ["Types"; "SMT"]
let fstar_tactics_Goal_lid  = fstar_tactics_lid' ["Types"; "Goal"]
let fstar_tactics_Drop_lid  = fstar_tactics_lid' ["Types"; "Drop"]
let fstar_tactics_Force_lid = fstar_tactics_lid' ["Types"; "Force"]

let fstar_tactics_SMT   = lid_as_data_tm fstar_tactics_SMT_lid
let fstar_tactics_Goal  = lid_as_data_tm fstar_tactics_Goal_lid
let fstar_tactics_Drop  = lid_as_data_tm fstar_tactics_Drop_lid
let fstar_tactics_Force = lid_as_data_tm fstar_tactics_Force_lid
let fstar_tactics_SMT_fv   = lid_as_data_fv fstar_tactics_SMT_lid
let fstar_tactics_Goal_fv  = lid_as_data_fv fstar_tactics_Goal_lid
let fstar_tactics_Drop_fv  = lid_as_data_fv fstar_tactics_Drop_lid
let fstar_tactics_Force_fv = lid_as_data_fv fstar_tactics_Force_lid

let t_proofstate    = S.tconst (fstar_tactics_lid' ["Types"; "proofstate"])
let fv_proofstate   = S.fvconst (fstar_tactics_lid' ["Types"; "proofstate"])
let t_goal          = S.tconst (fstar_tactics_lid' ["Types"; "goal"])
let fv_goal         = S.fvconst (fstar_tactics_lid' ["Types"; "goal"])
let t_result_lid    = fstar_tactics_lid' ["Types"; "result"]
let t_result        = S.tconst t_result_lid
let fv_result       = S.fvconst (fstar_tactics_lid' ["Types"; "result"])
let t_result_of t   = U.mk_app t_result [S.as_arg t] // TODO: uinst on t_result?
let t_guard_policy  = S.tconst (fstar_tactics_lid' ["Types"; "guard_policy"])
let fv_guard_policy = S.fvconst (fstar_tactics_lid' ["Types"; "guard_policy"])
let t_direction     = S.tconst (fstar_tactics_lid' ["Types"; "direction"])
let fv_direction    = S.fvconst (fstar_tactics_lid' ["Types"; "direction"])

let mk_emb (em: Range.range -> 'a -> term)
           (un: bool -> term -> option<'a>)
           (t: term) =
    mk_emb (fun x r _topt _norm -> em r x)
           (fun x w _norm -> un w x)
           (FStar.Syntax.Embeddings.term_as_fv t)
let embed e r x = FStar.Syntax.Embeddings.embed e x r None id_norm_cb
let unembed' w e x = FStar.Syntax.Embeddings.unembed e x w id_norm_cb

let e_proofstate =
    let embed_proofstate (rng:Range.range) (ps:proofstate) : term =
        U.mk_lazy ps t_proofstate Lazy_proofstate (Some rng)
    in
    let unembed_proofstate w (t:term) : option<proofstate> =
        match (SS.compress t).n with
        | Tm_lazy {blob=b; lkind=Lazy_proofstate} ->
            Some <| FStar.Dyn.undyn b
        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded proofstate: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_proofstate unembed_proofstate t_proofstate

let unfold_lazy_proofstate (i : lazyinfo) : term =
    U.exp_string "(((proofstate)))"

(* PLEASE NOTE: Construct and FV accumulate their arguments BACKWARDS. That is,
 * the expression (f 1 2) is stored as FV (f, [], [Constant (Int 2); Constant (Int 1)].
 * So be careful when calling mkFV/mkConstruct and matching on them. *)

(* On that note, we use this (inefficient, FIXME) hack in this module *)
let mkFV fv us ts = NBETerm.mkFV fv (List.rev us) (List.rev ts)
let mkConstruct fv us ts = NBETerm.mkConstruct fv (List.rev us) (List.rev ts)
let fv_as_emb_typ fv = S.ET_app (FStar.Ident.string_of_lid fv.fv_name.v, [])

let e_proofstate_nbe =
    let embed_proofstate _cb (ps:proofstate) : NBETerm.t =
        let li = { lkind = Lazy_proofstate
                 ; blob = FStar.Dyn.mkdyn ps
                 ; ltyp = t_proofstate
                 ; rng = Range.dummyRange }
        in
        let thunk = FStar.Common.mk_thunk (fun () -> NBETerm.Constant (NBETerm.String ("(((proofstate.nbe)))", Range.dummyRange))) in
        NBETerm.Lazy (BU.Inl li, thunk)
    in
    let unembed_proofstate _cb (t:NBETerm.t) : option<proofstate> =
        match t with
        | NBETerm.Lazy (BU.Inl {blob=b; lkind = Lazy_proofstate}, _) ->
            Some <| FStar.Dyn.undyn b
        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded NBE proofstate: %s" (NBETerm.t_to_string t)));
            None
    in
    { NBETerm.em = embed_proofstate
    ; NBETerm.un = unembed_proofstate
    ; NBETerm.typ = mkFV fv_proofstate [] []
    ; NBETerm.emb_typ = fv_as_emb_typ fv_proofstate }

let e_goal =
    let embed_goal (rng:Range.range) (g:goal) : term =
        U.mk_lazy g t_goal Lazy_goal (Some rng)
    in
    let unembed_goal w (t:term) : option<goal> =
        match (SS.compress t).n with
        | Tm_lazy {blob=b; lkind=Lazy_goal} ->
            Some <| FStar.Dyn.undyn b
        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded goal: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_goal unembed_goal t_goal

let unfold_lazy_goal (i : lazyinfo) : term =
    U.exp_string "(((goal)))"

let e_goal_nbe =
    let embed_goal _cb (ps:goal) : NBETerm.t =
        let li = { lkind = Lazy_goal
                 ; blob = FStar.Dyn.mkdyn ps
                 ; ltyp = t_goal
                 ; rng = Range.dummyRange }
        in
        let thunk = FStar.Common.mk_thunk (fun () -> NBETerm.Constant (NBETerm.String ("(((goal.nbe)))", Range.dummyRange))) in
        NBETerm.Lazy (BU.Inl li, thunk)
    in
    let unembed_goal _cb (t:NBETerm.t) : option<goal> =
        match t with
        | NBETerm.Lazy (BU.Inl {blob=b; lkind = Lazy_goal}, _) ->
            Some <| FStar.Dyn.undyn b
        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded NBE goal: %s" (NBETerm.t_to_string t)));
            None
    in
    { NBETerm.em = embed_goal
    ; NBETerm.un = unembed_goal
    ; NBETerm.typ = mkFV fv_goal [] []
    ; NBETerm.emb_typ = fv_as_emb_typ fv_goal }

let e_result (ea : embedding<'a>)  =
    let embed_result (res:__result<'a>) (rng:Range.range) _ _ : term =
        match res with
        | Success (a, ps) ->
          S.mk_Tm_app (S.mk_Tm_uinst fstar_tactics_Success_tm [U_zero])
                 [S.iarg (type_of ea);
                  S.as_arg (embed ea rng a);
                  S.as_arg (embed e_proofstate rng ps)]
                 None rng
        | Failed (msg, ps) ->
          S.mk_Tm_app (S.mk_Tm_uinst fstar_tactics_Failed_tm [U_zero])
                 [S.iarg (type_of ea);
                  S.as_arg (embed e_string rng msg);
                  S.as_arg (embed e_proofstate rng ps)]
                 None rng
    in
    let unembed_result (t:term) w _ : option<__result<'a>> =
        let hd'_and_args tm =
          let tm = U.unascribe tm in
          let hd, args = U.head_and_args tm in
          (U.un_uinst hd).n, args in

        match hd'_and_args t with
        | Tm_fvar fv, [_t; (a, _); (ps, _)] when S.fv_eq_lid fv fstar_tactics_Success_lid ->
            BU.bind_opt (unembed' w ea a) (fun a ->
            BU.bind_opt (unembed' w e_proofstate ps) (fun ps ->
            Some (Success (a, ps))))

        | Tm_fvar fv, [_t; (msg, _); (ps, _)] when S.fv_eq_lid fv fstar_tactics_Failed_lid ->
            BU.bind_opt (unembed' w e_string msg) (fun msg ->
            BU.bind_opt (unembed' w e_proofstate ps) (fun ps ->
            Some (Failed (msg, ps))))

        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded tactic result: %s" (Print.term_to_string t)));
            None
    in
    mk_emb_full
        embed_result
        unembed_result
        (t_result_of (type_of ea))
        (fun _ -> "")
        (ET_app (t_result_lid |> Ident.string_of_lid, [emb_typ_of ea]))

let e_result_nbe (ea : NBET.embedding<'a>)  =
    let embed_result cb (res:__result<'a>) : NBET.t =
        match res with
        | Failed (msg, ps) ->
            mkConstruct fstar_tactics_Failed_fv
              [U_zero]
              [ NBETerm.as_iarg (NBETerm.type_of ea)
              ; NBETerm.as_arg (NBETerm.embed NBETerm.e_string cb msg)
              ; NBETerm.as_arg (NBETerm.embed e_proofstate_nbe cb ps) ]
        | Success (a, ps) ->
            mkConstruct fstar_tactics_Success_fv
              [U_zero]
              [ NBETerm.as_iarg (NBETerm.type_of ea)
              ; NBETerm.as_arg (NBETerm.embed ea cb a)
              ; NBETerm.as_arg (NBETerm.embed e_proofstate_nbe cb ps) ]
    in
    let unembed_result cb (t:NBET.t) : option<__result<'a>> =
        match t with
        | NBETerm.Construct (fv, _, [(ps, _); (a, _); _t]) when S.fv_eq_lid fv fstar_tactics_Success_lid ->
            BU.bind_opt (NBETerm.unembed ea cb a) (fun a ->
            BU.bind_opt (NBETerm.unembed e_proofstate_nbe cb ps) (fun ps ->
            Some (Success (a, ps))))

        | NBETerm.Construct (fv, _, [(ps, _); (msg, _); _t]) when S.fv_eq_lid fv fstar_tactics_Failed_lid ->
            BU.bind_opt (NBETerm.unembed NBETerm.e_string cb msg) (fun msg ->
            BU.bind_opt (NBETerm.unembed e_proofstate_nbe cb ps) (fun ps ->
            Some (Failed (msg, ps))))
        | _ ->
            None
    in
    { NBETerm.em = embed_result
    ; NBETerm.un = unembed_result
    ; NBETerm.typ = mkFV fv_result [] []
    ; NBETerm.emb_typ = fv_as_emb_typ fv_result }


let e_direction =
    let embed_direction (rng:Range.range) (d : direction) : term =
        match d with
        | TopDown -> fstar_tactics_topdown
        | BottomUp -> fstar_tactics_bottomup
    in
    let unembed_direction w (t : term) : option<direction> =
        match (SS.compress t).n with
        | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_topdown_lid -> Some TopDown
        | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_bottomup_lid -> Some BottomUp
        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded direction: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_direction unembed_direction t_direction

let e_direction_nbe  =
    let embed_direction cb (res:direction) : NBET.t =
        match res with
        | TopDown  -> mkConstruct fstar_tactics_topdown_fv [] []
        | BottomUp -> mkConstruct fstar_tactics_bottomup_fv [] []
    in
    let unembed_direction cb (t:NBET.t) : option<direction> =
        match t with
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_topdown_lid -> Some TopDown
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_bottomup_lid -> Some BottomUp
        | _ ->
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded direction: %s" (NBETerm.t_to_string t)));
            None
    in
    { NBETerm.em = embed_direction
    ; NBETerm.un = unembed_direction
    ; NBETerm.typ = mkFV fv_direction [] []
    ; NBETerm.emb_typ = fv_as_emb_typ fv_direction}

let e_guard_policy =
    let embed_guard_policy (rng:Range.range) (p : guard_policy) : term =
        match p with
        | SMT   -> fstar_tactics_SMT
        | Goal  -> fstar_tactics_Goal
        | Force -> fstar_tactics_Force
        | Drop  -> fstar_tactics_Drop
    in
    let unembed_guard_policy w (t : term) : option<guard_policy> =
        match (SS.compress t).n with
        | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_SMT_lid   -> Some SMT
        | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_Goal_lid  -> Some Goal
        | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_Force_lid -> Some Force
        | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_Drop_lid  -> Some Drop
        | _ ->
            if w then
                Err.log_issue t.pos (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded guard_policy: %s" (Print.term_to_string t)));
            None
    in
    mk_emb embed_guard_policy unembed_guard_policy t_guard_policy

let e_guard_policy_nbe  =
    let embed_guard_policy cb (p:guard_policy) : NBET.t =
        match p with
        | SMT   -> mkConstruct fstar_tactics_SMT_fv [] []
        | Goal  -> mkConstruct fstar_tactics_Goal_fv [] []
        | Force -> mkConstruct fstar_tactics_Force_fv [] []
        | Drop  -> mkConstruct fstar_tactics_Drop_fv [] []
    in
    let unembed_guard_policy cb (t:NBET.t) : option<guard_policy> =
        match t with
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_SMT_lid   -> Some SMT
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_Goal_lid  -> Some Goal
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_Force_lid -> Some Force
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_Drop_lid  -> Some Drop
        | _ -> None
    in
    { NBETerm.em = embed_guard_policy
    ; NBETerm.un = unembed_guard_policy
    ; NBETerm.typ = mkFV fv_guard_policy [] []
    ; NBETerm.emb_typ = fv_as_emb_typ fv_guard_policy }
