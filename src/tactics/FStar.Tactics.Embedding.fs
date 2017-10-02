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

open FStar.Tactics.Types
open FStar.Tactics.Result
open FStar.Tactics.Basic

open FStar.Reflection.Basic
open FStar.Reflection.Data

type name = bv

let fstar_tactics_lid' s = PC.fstar_tactics_lid' s
let lid_as_tm l = S.lid_as_fv l Delta_constant None |> S.fv_to_tm
let mk_tactic_lid_as_term (s:string) = lid_as_tm (fstar_tactics_lid' ["Effect"; s])

let lid_as_data_tm l = S.fv_to_tm (S.lid_as_fv l Delta_constant (Some Data_ctor))
let fstar_tactics_lid_as_data_tm s = lid_as_data_tm (fstar_tactics_lid' ["Effect";s])

let fstar_tactics_Failed_lid  = fstar_tactics_lid' ["Result"; "Failed"]
let fstar_tactics_Success_lid = fstar_tactics_lid' ["Result"; "Success"]

let fstar_tactics_Failed_tm  = lid_as_data_tm fstar_tactics_Failed_lid
let fstar_tactics_Success_tm = lid_as_data_tm fstar_tactics_Success_lid

let pair_typ t s = S.mk_Tm_app (S.mk_Tm_uinst (lid_as_tm PC.lid_tuple2) [U_zero;U_zero])
                                      [S.as_arg t;
                                       S.as_arg s]
                                      None
                                      Range.dummyRange

let embed_proofstate (ps:proofstate) : term =
    U.mk_alien ps "tactics.embed_proofstate" None

let unembed_proofstate (t:term) : proofstate =
    U.un_alien t |> FStar.Dyn.undyn

let mk_app hd args =
  S.mk_Tm_app hd args None Range.dummyRange

let mktuple2_tm = lid_as_data_tm (PC.lid_Mktuple2)

let t_proofstate = S.tconst (fstar_tactics_lid' ["Types"; "proofstate"])

let embed_result (ps:proofstate) (res:__result<'a>) (embed_a:'a -> term) (t_a:typ) : term =
    match res with
    | Failed (msg, ps) ->
      mk_app (S.mk_Tm_uinst fstar_tactics_Failed_tm [U_zero])
             [S.iarg t_a;
              S.as_arg (mk_app (S.mk_Tm_uinst mktuple2_tm [U_zero; U_zero])
                               [S.iarg S.t_string;
                                S.iarg t_proofstate;
                                S.as_arg (embed_string msg);
                                S.as_arg (embed_proofstate ps)])]
    | Success (a, ps) ->
      mk_app (S.mk_Tm_uinst fstar_tactics_Success_tm [U_zero])
             [S.iarg t_a;
              S.as_arg (mk_app (S.mk_Tm_uinst mktuple2_tm [U_zero; U_zero])
                               [S.iarg t_a;
                                S.iarg t_proofstate;
                                S.as_arg (embed_a a);
                                S.as_arg (embed_proofstate ps)])]

let unembed_result (ps:proofstate) (res:term) (unembed_a:term -> 'a) : either<('a * proofstate), (string * proofstate)> =
    let hd'_and_args tm =
      let tm = U.unascribe tm in
      let hd, args = U.head_and_args tm in
      (U.un_uinst hd).n, args in
    let tuple2_elements tm =
      match hd'_and_args tm with
      | Tm_fvar fv, [_t1; _t2; (arg1, _); (arg2, _)]
          when S.fv_eq_lid fv PC.lid_Mktuple2 -> (arg1, arg2)
      | _ -> failwith (BU.format1 "Expected a two-elements tuple, got %s" (Print.term_to_string tm)) in
    match hd'_and_args res with
    | Tm_fvar fv, [_t; (tuple2, _)] when S.fv_eq_lid fv fstar_tactics_Success_lid ->
      let embedded_a, embedded_ps = tuple2_elements tuple2 in
      Inl (unembed_a embedded_a, unembed_proofstate embedded_ps)
    | Tm_fvar fv, [_t; (tuple2, _)] when S.fv_eq_lid fv fstar_tactics_Failed_lid ->
      let embedded_msg, embedded_ps = tuple2_elements tuple2 in
      Inr (unembed_string embedded_msg, unembed_proofstate embedded_ps)
    | _ ->
      failwith (BU.format1 "Expected Result.Success or Result.Failed applied to a single argument, got %s"
                           (Print.term_to_string res))
