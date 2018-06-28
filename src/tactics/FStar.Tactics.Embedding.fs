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

open FStar.Tactics.Types
open FStar.Tactics.Result
open FStar.Tactics.Basic

open FStar.Reflection.Basic
open FStar.Reflection.Data

type name = bv

let fstar_tactics_lid' s = PC.fstar_tactics_lid' s
let lid_as_tm l = S.lid_as_fv l delta_constant None |> S.fv_to_tm
let mk_tactic_lid_as_term (s:string) = lid_as_tm (fstar_tactics_lid' ["Effect"; s])

let lid_as_data_tm l = S.fv_to_tm (S.lid_as_fv l delta_constant (Some Data_ctor))
let fstar_tactics_lid_as_data_tm s = lid_as_data_tm (fstar_tactics_lid' ["Effect";s])

let fstar_tactics_Failed_lid  = fstar_tactics_lid' ["Result"; "Failed"]
let fstar_tactics_Success_lid = fstar_tactics_lid' ["Result"; "Success"]

let fstar_tactics_Failed_tm  = lid_as_data_tm fstar_tactics_Failed_lid
let fstar_tactics_Success_tm = lid_as_data_tm fstar_tactics_Success_lid

let fstar_tactics_topdown_lid = fstar_tactics_lid' ["Types"; "TopDown"]
let fstar_tactics_bottomup_lid = fstar_tactics_lid' ["Types"; "BottomUp"]

let fstar_tactics_topdown = lid_as_data_tm fstar_tactics_topdown_lid
let fstar_tactics_bottomup = lid_as_data_tm fstar_tactics_bottomup_lid

let fstar_tactics_SMT_lid   = fstar_tactics_lid' ["Types"; "SMT"]
let fstar_tactics_Goal_lid  = fstar_tactics_lid' ["Types"; "Goal"]
let fstar_tactics_Drop_lid  = fstar_tactics_lid' ["Types"; "Drop"]
let fstar_tactics_Force_lid = fstar_tactics_lid' ["Types"; "Force"]

let fstar_tactics_SMT   = lid_as_data_tm fstar_tactics_SMT_lid
let fstar_tactics_Goal  = lid_as_data_tm fstar_tactics_Goal_lid
let fstar_tactics_Drop  = lid_as_data_tm fstar_tactics_Drop_lid
let fstar_tactics_Force = lid_as_data_tm fstar_tactics_Force_lid

let t_proofstate   = S.tconst (fstar_tactics_lid' ["Types"; "proofstate"])
let t_result       = S.tconst (fstar_tactics_lid' ["Types"; "result"])
let t_result_of t  = U.mk_app t_result [S.as_arg t] // TODO: uinst on t_result?
let t_guard_policy = S.tconst (fstar_tactics_lid' ["Types"; "guard_policy"])
let t_direction    = S.tconst (fstar_tactics_lid' ["Types"; "direction"])

let mk_emb f g t =
    mk_emb (fun x r _topt _norm -> f r x)
           (fun x w _norm -> g w x) t
let embed e r x = FStar.Syntax.Embeddings.embed e x r None (fun x -> x)
let unembed' w e x = FStar.Syntax.Embeddings.unembed e x w (fun x -> x)

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

let e_result (ea : embedding<'a>)  =
    let embed_result (rng:Range.range) (res:__result<'a>) : term =
        match res with
        | Failed (msg, ps) ->
          S.mk_Tm_app (S.mk_Tm_uinst fstar_tactics_Failed_tm [U_zero])
                 [S.iarg (type_of ea);
                  S.as_arg (embed e_string rng msg);
                  S.as_arg (embed e_proofstate rng ps)]
                 None rng
        | Success (a, ps) ->
          S.mk_Tm_app (S.mk_Tm_uinst fstar_tactics_Success_tm [U_zero])
                 [S.iarg (type_of ea);
                  S.as_arg (embed ea rng a);
                  S.as_arg (embed e_proofstate rng ps)]
                 None rng
    in
    let unembed_result w (t:term) : option<__result<'a>> =
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
    mk_emb embed_result unembed_result (t_result_of (type_of ea))

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
