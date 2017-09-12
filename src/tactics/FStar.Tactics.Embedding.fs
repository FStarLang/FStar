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
open FStar.Tactics.Basic
module Core = FStar.Tactics.Basic

open FStar.Reflection.Basic
open FStar.Reflection.Data

type name = bv

let fstar_tactics_lid' s = PC.fstar_tactics_lid' s
let lid_as_tm l = S.lid_as_fv l Delta_constant None |> S.fv_to_tm
let mk_tactic_lid_as_term (s:string) = lid_as_tm (fstar_tactics_lid' ["Effect"; s])

let lid_as_data_tm l = S.fv_to_tm (S.lid_as_fv l Delta_constant (Some Data_ctor))
let fstar_tactics_lid_as_data_tm s = lid_as_data_tm (fstar_tactics_lid' ["Effect";s])

let fstar_tactics_Failed  = fstar_tactics_lid_as_data_tm "Failed"
let fstar_tactics_Success = fstar_tactics_lid_as_data_tm "Success"
let pair_typ t s = S.mk_Tm_app (S.mk_Tm_uinst (lid_as_tm PC.lid_tuple2) [U_zero;U_zero])
                                      [S.as_arg t;
                                       S.as_arg s]
                                      None
                                      Range.dummyRange

let embed_proofstate (ps:proofstate) : term =
    U.mk_alien ps "tactics.embed_proofstate" None

let unembed_proofstate (ps:proofstate) (t:term) : proofstate =
    U.un_alien t |> FStar.Dyn.undyn

let embed_result (ps:proofstate) (res:result<'a>) (embed_a:'a -> term) (t_a:typ) : term =
    match res with
    | Failed (msg, ps) ->
      S.mk_Tm_app (S.mk_Tm_uinst fstar_tactics_Failed [U_zero])
                  [S.iarg t_a;
                   S.as_arg (embed_string msg);
                   S.as_arg (embed_proofstate ps)]
                  None
                  Range.dummyRange
    | Success (a, ps) ->
      S.mk_Tm_app (S.mk_Tm_uinst fstar_tactics_Success [U_zero])
                  [S.iarg t_a;
                   S.as_arg (embed_a a);
                   S.as_arg (embed_proofstate ps)]
                  None
                  Range.dummyRange

let unembed_result (ps:proofstate) (res:term) (unembed_a:term -> 'a) : either<('a * proofstate), (string * proofstate)> =
    let res = U.unascribe res in
    let hd, args = U.head_and_args res in
    match (U.un_uinst hd).n, args with
    | Tm_fvar fv, [_t; (a, _); (embedded_state, _)]
        when S.fv_eq_lid fv (fstar_tactics_lid' ["Effect";"Success"]) ->
      Inl (unembed_a a, unembed_proofstate ps embedded_state)

    | Tm_fvar fv, [_t; (embedded_string, _); (embedded_state, _)]
        when S.fv_eq_lid fv (fstar_tactics_lid' ["Effect";"Failed"]) ->
      Inr (unembed_string embedded_string, unembed_proofstate ps embedded_state)

    | _ -> failwith (BU.format1 "Not an embedded result: %s" (Print.term_to_string res))
