﻿(*
   Copyright 2008-2016 Microsoft Research

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

module FStar.Tactics.Embedding

open FStar
open FStar.Compiler
open FStar.Pervasives
open FStar.Compiler.Effect
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
open FStar.Compiler.Util

open FStar.Tactics.Common
open FStar.Tactics.Types
open FStar.Tactics.Result

module BU      = FStar.Compiler.Util
module Err     = FStar.Errors
module NBE     = FStar.TypeChecker.NBE
module NBETerm = FStar.TypeChecker.NBETerm
module NBET    = FStar.TypeChecker.NBETerm
module PC      = FStar.Parser.Const
module S       = FStar.Syntax.Syntax
module SS      = FStar.Syntax.Subst
module U       = FStar.Syntax.Util

type name = bv

let fstar_tactics_lid' s = PC.fstar_tactics_lid' s
let lid_as_tm l = S.lid_as_fv l None |> S.fv_to_tm
let mk_tactic_lid_as_term (s:string) = lid_as_tm (fstar_tactics_lid' ["Effect"; s])


type tac_constant = {
  lid : Ident.lid;
  fv  : fv;
  t   : term;
}

let lid_as_data_fv l = S.lid_as_fv l (Some Data_ctor)
let lid_as_data_tm l = S.fv_to_tm (lid_as_data_fv l)

let fstar_tactics_data ns =
    let lid = fstar_tactics_lid' ns in
    { lid = lid;
      fv  = lid_as_data_fv lid;
      t   = lid_as_data_tm lid }

let fstar_tactics_const ns =
    let lid = fstar_tactics_lid' ns in
    { lid = lid;
      fv  = S.fvconst lid;
      t   = S.tconst lid }



let fstar_tactics_proofstate    = fstar_tactics_const ["Types"; "proofstate"]
let fstar_tactics_goal          = fstar_tactics_const ["Types"; "goal"]

let fstar_tactics_TacticFailure = fstar_tactics_data  ["Common"; "TacticFailure"]

let fstar_tactics_result        = fstar_tactics_const ["Types"; "result"]
let fstar_tactics_Success       = fstar_tactics_data  ["Result"; "Success"]
let fstar_tactics_Failed        = fstar_tactics_data  ["Result"; "Failed"]

let fstar_tactics_direction     = fstar_tactics_const ["Types"; "direction"]
let fstar_tactics_topdown       = fstar_tactics_data  ["Types"; "TopDown"]
let fstar_tactics_bottomup      = fstar_tactics_data  ["Types"; "BottomUp"]

let fstar_tactics_ctrl_flag     = fstar_tactics_const ["Types"; "ctrl_flag"]
let fstar_tactics_Continue      = fstar_tactics_data  ["Types"; "Continue"]
let fstar_tactics_Skip          = fstar_tactics_data  ["Types"; "Skip"]
let fstar_tactics_Abort         = fstar_tactics_data  ["Types"; "Abort"]

let fstar_tactics_unfold_side         = fstar_tactics_const ["Types"; "unfold_side"]
let fstar_tactics_unfold_side_Left    = fstar_tactics_data  ["Types"; "Left"]
let fstar_tactics_unfold_side_Right   = fstar_tactics_data  ["Types"; "Right"]
let fstar_tactics_unfold_side_Both    = fstar_tactics_data  ["Types"; "Both"]
let fstar_tactics_unfold_side_Neither = fstar_tactics_data  ["Types"; "Neither"]

let fstar_tactics_tot_or_ghost        = fstar_tactics_const ["Types"; "tot_or_ghost"]
let fstar_tactics_tot_or_ghost_ETotal = fstar_tactics_data ["Types"; "E_Total"]
let fstar_tactics_tot_or_ghost_EGhost = fstar_tactics_data ["Types"; "E_Ghost"]

let fstar_tactics_guard_policy  = fstar_tactics_const ["Types"; "guard_policy"]
let fstar_tactics_SMT           = fstar_tactics_data  ["Types"; "SMT"]
let fstar_tactics_Goal          = fstar_tactics_data  ["Types"; "Goal"]
let fstar_tactics_Drop          = fstar_tactics_data  ["Types"; "Drop"]
let fstar_tactics_Force         = fstar_tactics_data  ["Types"; "Force"]


let mk_emb (em: Range.range -> 'a -> term)
           (un: term -> option 'a)
           (t: term) =
    mk_emb (fun x r _topt _norm -> em r x)
           (fun x _norm -> un x)
           (FStar.Syntax.Embeddings.term_as_fv t)
let embed e r x = FStar.Syntax.Embeddings.embed e x r None id_norm_cb
let unembed' e x = FStar.Syntax.Embeddings.unembed e x id_norm_cb

let t_result_of t   = U.mk_app fstar_tactics_result.t [S.as_arg t] // TODO: uinst on t_result?

let hd'_and_args tm =
  let tm = U.unascribe tm in
  let hd, args = U.head_and_args tm in
  (U.un_uinst hd).n, args

let e_proofstate : embedding proofstate = e_lazy Lazy_proofstate fstar_tactics_proofstate.t
let e_goal       : embedding goal       = e_lazy Lazy_goal fstar_tactics_goal.t

let unfold_lazy_proofstate (i : lazyinfo) : term =
    U.exp_string "(((proofstate)))"

let unfold_lazy_goal (i : lazyinfo) : term =
    U.exp_string "(((goal)))"

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
                 ; blob = FStar.Compiler.Dyn.mkdyn ps
                 ; ltyp = fstar_tactics_proofstate.t
                 ; rng = Range.dummyRange }
        in
        let thunk = Thunk.mk (fun () -> NBETerm.mk_t <| NBETerm.Constant (NBETerm.String ("(((proofstate.nbe)))", Range.dummyRange))) in
        NBETerm.mk_t (NBETerm.Lazy (Inl li, thunk))
    in
    let unembed_proofstate _cb (t:NBETerm.t) : option proofstate =
        match NBETerm.nbe_t_of_t t with
        | NBETerm.Lazy (Inl {blob=b; lkind = Lazy_proofstate}, _) ->
            Some <| FStar.Compiler.Dyn.undyn b
        | _ ->
          if !Options.debug_embedding then
            Err.log_issue Range.dummyRange
              (Err.Warning_NotEmbedded,
               BU.format1 "Not an embedded NBE proofstate: %s\n"
                 (NBETerm.t_to_string t));
            None
    in
    { NBETerm.em = embed_proofstate
    ; NBETerm.un = unembed_proofstate
    ; NBETerm.typ = mkFV fstar_tactics_proofstate.fv [] []
    ; NBETerm.emb_typ = fv_as_emb_typ fstar_tactics_proofstate.fv }

let e_goal_nbe =
    let embed_goal _cb (ps:goal) : NBETerm.t =
        let li = { lkind = Lazy_goal
                 ; blob = FStar.Compiler.Dyn.mkdyn ps
                 ; ltyp = fstar_tactics_goal.t
                 ; rng = Range.dummyRange }
        in
        let thunk = Thunk.mk (fun () -> NBETerm.mk_t <| NBETerm.Constant (NBETerm.String ("(((goal.nbe)))", Range.dummyRange))) in
        NBETerm.mk_t <| NBETerm.Lazy (Inl li, thunk)
    in
    let unembed_goal _cb (t:NBETerm.t) : option goal =
        match NBETerm.nbe_t_of_t t with
        | NBETerm.Lazy (Inl {blob=b; lkind = Lazy_goal}, _) ->
            Some <| FStar.Compiler.Dyn.undyn b
        | _ ->
            if !Options.debug_embedding then
              Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded NBE goal: %s" (NBETerm.t_to_string t)));
            None
    in
    { NBETerm.em = embed_goal
    ; NBETerm.un = unembed_goal
    ; NBETerm.typ = mkFV fstar_tactics_goal.fv [] []
    ; NBETerm.emb_typ = fv_as_emb_typ fstar_tactics_goal.fv }

let e_exn : embedding exn =
    let embed_exn (e:exn) (rng:Range.range) _ _ : term =
        match e with
        | TacticFailure s ->
            S.mk_Tm_app fstar_tactics_TacticFailure.t
                [S.as_arg (embed e_string rng s)]
                rng
        | EExn t ->
            { t with pos = rng }
        | e ->
            let s = "uncaught exception: " ^ (BU.message_of_exn e) in
            S.mk_Tm_app fstar_tactics_TacticFailure.t
                [S.as_arg (embed e_string rng s)]
                rng
    in
    let unembed_exn (t:term) _ : option exn =
        match hd'_and_args t with
        | Tm_fvar fv, [(s, _)] when S.fv_eq_lid fv fstar_tactics_TacticFailure.lid ->
            BU.bind_opt (unembed' e_string s) (fun s ->
            Some (TacticFailure s))

        | _ ->
            (* Anything else, we just pass-through *)
            Some (EExn t)
    in
    mk_emb_full
        embed_exn
        unembed_exn
        t_exn
        (fun _ -> "(exn)")
        (ET_app (PC.exn_lid |> Ident.string_of_lid, []))

let e_exn_nbe =
    let embed_exn cb (e:exn) : NBET.t =
        match e with
        | TacticFailure s ->
            mkConstruct fstar_tactics_TacticFailure.fv
              []
              [ NBETerm.as_arg (NBETerm.embed NBETerm.e_string cb s) ]

        | _ ->
            failwith (BU.format1 "cannot embed exn (NBE) : %s" (BU.message_of_exn e))
    in
    let unembed_exn cb (t:NBET.t) : option exn =
        match NBETerm.nbe_t_of_t t with
        | NBETerm.Construct (fv, _, [(s, _)]) when S.fv_eq_lid fv fstar_tactics_TacticFailure.lid ->
            BU.bind_opt (NBETerm.unembed NBETerm.e_string cb s) (fun s ->
            Some (TacticFailure s))

        | _ ->
            None
    in
    let fv_exn = S.fvconst PC.exn_lid in
    { NBETerm.em = embed_exn
    ; NBETerm.un = unembed_exn
    ; NBETerm.typ = mkFV fv_exn [] []
    ; NBETerm.emb_typ = fv_as_emb_typ fv_exn }

let e_result (ea : embedding 'a)  =
    let embed_result (res:__result 'a) (rng:Range.range) _ _ : term =
        match res with
        | Success (a, ps) ->
          S.mk_Tm_app (S.mk_Tm_uinst fstar_tactics_Success.t [U_zero])
                 [S.iarg (type_of ea);
                  S.as_arg (embed ea rng a);
                  S.as_arg (embed e_proofstate rng ps)]
                 rng
        | Failed (e, ps) ->
          S.mk_Tm_app (S.mk_Tm_uinst fstar_tactics_Failed.t [U_zero])
                 [S.iarg (type_of ea);
                  S.as_arg (embed e_exn rng e);
                  S.as_arg (embed e_proofstate rng ps)]
                 rng
    in
    let unembed_result (t:term) _ : option (__result 'a) =
        match hd'_and_args t with
        | Tm_fvar fv, [_t; (a, _); (ps, _)] when S.fv_eq_lid fv fstar_tactics_Success.lid ->
            BU.bind_opt (unembed' ea a) (fun a ->
            BU.bind_opt (unembed' e_proofstate ps) (fun ps ->
            Some (Success (a, ps))))

        | Tm_fvar fv, [_t; (e, _); (ps, _)] when S.fv_eq_lid fv fstar_tactics_Failed.lid ->
            BU.bind_opt (unembed' e_exn e) (fun e ->
            BU.bind_opt (unembed' e_proofstate ps) (fun ps ->
            Some (Failed (e, ps))))

        | _ -> None
    in
    mk_emb_full
        embed_result
        unembed_result
        (t_result_of (type_of ea))
        (fun _ -> "")
        (ET_app (fstar_tactics_result.lid |> Ident.string_of_lid, [emb_typ_of ea]))

let e_result_nbe (ea : NBET.embedding 'a)  =
    let embed_result cb (res:__result 'a) : NBET.t =
        match res with
        | Failed (e, ps) ->
            mkConstruct fstar_tactics_Failed.fv
              [U_zero]
              [ NBETerm.as_iarg (NBETerm.type_of ea)
              ; NBETerm.as_arg (NBETerm.embed e_exn_nbe cb e)
              ; NBETerm.as_arg (NBETerm.embed e_proofstate_nbe cb ps) ]
        | Success (a, ps) ->
            mkConstruct fstar_tactics_Success.fv
              [U_zero]
              [ NBETerm.as_iarg (NBETerm.type_of ea)
              ; NBETerm.as_arg (NBETerm.embed ea cb a)
              ; NBETerm.as_arg (NBETerm.embed e_proofstate_nbe cb ps) ]
    in
    let unembed_result cb (t:NBET.t) : option (__result 'a) =
        match NBETerm.nbe_t_of_t t with
        | NBETerm.Construct (fv, _, [(ps, _); (a, _); _t]) when S.fv_eq_lid fv fstar_tactics_Success.lid ->
            BU.bind_opt (NBETerm.unembed ea cb a) (fun a ->
            BU.bind_opt (NBETerm.unembed e_proofstate_nbe cb ps) (fun ps ->
            Some (Success (a, ps))))

        | NBETerm.Construct (fv, _, [(ps, _); (e, _); _t]) when S.fv_eq_lid fv fstar_tactics_Failed.lid ->
            BU.bind_opt (NBETerm.unembed e_exn_nbe cb e) (fun e ->
            BU.bind_opt (NBETerm.unembed e_proofstate_nbe cb ps) (fun ps ->
            Some (Failed (e, ps))))
        | _ ->
            None
    in
    { NBETerm.em = embed_result
    ; NBETerm.un = unembed_result
    ; NBETerm.typ = mkFV fstar_tactics_result.fv [] []
    ; NBETerm.emb_typ = fv_as_emb_typ fstar_tactics_result.fv }


let e_direction =
    let embed_direction (rng:Range.range) (d : direction) : term =
        match d with
        | TopDown -> fstar_tactics_topdown.t
        | BottomUp -> fstar_tactics_bottomup.t
    in
    let unembed_direction (t : term) : option direction =
        match (SS.compress t).n with
        | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_topdown.lid -> Some TopDown
        | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_bottomup.lid -> Some BottomUp
        | _ -> None
    in
    mk_emb embed_direction unembed_direction fstar_tactics_direction.t

let e_direction_nbe  =
    let embed_direction cb (res:direction) : NBET.t =
        match res with
        | TopDown  -> mkConstruct fstar_tactics_topdown.fv [] []
        | BottomUp -> mkConstruct fstar_tactics_bottomup.fv [] []
    in
    let unembed_direction cb (t:NBET.t) : option direction =
        match NBETerm.nbe_t_of_t t with
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_topdown.lid -> Some TopDown
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_bottomup.lid -> Some BottomUp
        | _ ->
          if !Options.debug_embedding then
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded direction: %s" (NBETerm.t_to_string t)));
          None
    in
    { NBETerm.em = embed_direction
    ; NBETerm.un = unembed_direction
    ; NBETerm.typ = mkFV fstar_tactics_direction.fv [] []
    ; NBETerm.emb_typ = fv_as_emb_typ fstar_tactics_direction.fv}

let e_ctrl_flag =
    let embed_ctrl_flag (rng:Range.range) (d : ctrl_flag) : term =
        match d with
        | Continue -> fstar_tactics_Continue.t
        | Skip     -> fstar_tactics_Skip.t
        | Abort    -> fstar_tactics_Abort.t
    in
    let unembed_ctrl_flag (t : term) : option ctrl_flag =
        match (SS.compress t).n with
        | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_Continue.lid -> Some Continue
        | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_Skip.lid     -> Some Skip
        | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_Abort.lid    -> Some Abort
        | _ -> None
    in
    mk_emb embed_ctrl_flag unembed_ctrl_flag fstar_tactics_ctrl_flag.t

let e_ctrl_flag_nbe  =
    let embed_ctrl_flag cb (res:ctrl_flag) : NBET.t =
        match res with
        | Continue -> mkConstruct fstar_tactics_Continue.fv [] []
        | Skip     -> mkConstruct fstar_tactics_Skip.fv [] []
        | Abort    -> mkConstruct fstar_tactics_Abort.fv [] []
    in
    let unembed_ctrl_flag cb (t:NBET.t) : option ctrl_flag =
        match NBETerm.nbe_t_of_t t with
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_Continue.lid  -> Some Continue
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_Skip.lid  -> Some Skip
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_Abort.lid -> Some Abort
        | _ ->
          if !Options.debug_embedding then
            Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded, (BU.format1 "Not an embedded ctrl_flag: %s" (NBETerm.t_to_string t)));
          None
    in
    { NBETerm.em = embed_ctrl_flag
    ; NBETerm.un = unembed_ctrl_flag
    ; NBETerm.typ = mkFV fstar_tactics_ctrl_flag.fv [] []
    ; NBETerm.emb_typ = fv_as_emb_typ fstar_tactics_ctrl_flag.fv }

let e_unfold_side =
  let open FStar.TypeChecker.Core in
  let embed_unfold_side (rng:Range.range) (s:side) : term =
    match s with
    | Left -> fstar_tactics_unfold_side_Left.t
    | Right -> fstar_tactics_unfold_side_Right.t
    | Both -> fstar_tactics_unfold_side_Both.t
    | Neither  -> fstar_tactics_unfold_side_Neither.t
  in
  let unembed_unfold_side (t : term) : option side =
    match (SS.compress t).n with
    | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_unfold_side_Left.lid -> Some Left
    | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_unfold_side_Right.lid -> Some Right
    | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_unfold_side_Both.lid -> Some Both
    | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_unfold_side_Neither.lid -> Some Neither
    | _ ->
        None
  in
  mk_emb embed_unfold_side unembed_unfold_side fstar_tactics_unfold_side.t

let e_unfold_side_nbe  =
  let open FStar.TypeChecker.Core in
  let embed_unfold_side cb (res:side) : NBET.t =
    match res with
    | Left -> mkConstruct fstar_tactics_unfold_side_Left.fv [] []
    | Right -> mkConstruct fstar_tactics_unfold_side_Right.fv [] []
    | Both -> mkConstruct fstar_tactics_unfold_side_Both.fv [] []
    | Neither -> mkConstruct fstar_tactics_unfold_side_Neither.fv [] []
  in
  let unembed_unfold_side cb (t:NBET.t) : option side =
    match NBETerm.nbe_t_of_t t with
    | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_unfold_side_Left.lid -> Some Left
    | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_unfold_side_Right.lid -> Some Right
    | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_unfold_side_Both.lid -> Some Both
    | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_unfold_side_Neither.lid -> Some Neither
    | _ ->
      if !Options.debug_embedding then
        Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded,
                                        BU.format1 "Not an embedded unfold_side: %s" (NBETerm.t_to_string t));
      None
  in
  { NBETerm.em = embed_unfold_side
  ; NBETerm.un = unembed_unfold_side
  ; NBETerm.typ = mkFV fstar_tactics_unfold_side.fv [] []
  ; NBETerm.emb_typ = fv_as_emb_typ fstar_tactics_unfold_side.fv }

let e_tot_or_ghost =
  let embed_tot_or_ghost (rng:Range.range) (s:tot_or_ghost) : term =
    match s with
    | E_Total -> fstar_tactics_tot_or_ghost_ETotal.t
    | E_Ghost -> fstar_tactics_tot_or_ghost_EGhost.t
  in
  let unembed_tot_or_ghost (t : term) : option tot_or_ghost =
    match (SS.compress t).n with
    | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_tot_or_ghost_ETotal.lid -> Some E_Total
    | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_tot_or_ghost_EGhost.lid -> Some E_Ghost
    | _ -> None
  in
  mk_emb embed_tot_or_ghost unembed_tot_or_ghost fstar_tactics_tot_or_ghost.t

let e_tot_or_ghost_nbe  =
  let embed_tot_or_ghost cb (res:tot_or_ghost) : NBET.t =
    match res with
    | E_Total -> mkConstruct fstar_tactics_tot_or_ghost_ETotal.fv [] []
    | E_Ghost -> mkConstruct fstar_tactics_tot_or_ghost_EGhost.fv [] []
  in
  let unembed_tot_or_ghost cb (t:NBET.t) : option tot_or_ghost =
    match NBETerm.nbe_t_of_t t with
    | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_tot_or_ghost_ETotal.lid -> Some E_Total
    | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_tot_or_ghost_EGhost.lid -> Some E_Ghost
    | _ ->
      if !Options.debug_embedding then
        Err.log_issue Range.dummyRange (Err.Warning_NotEmbedded,
                                        BU.format1 "Not an embedded tot_or_ghost: %s" (NBETerm.t_to_string t));
      None
  in
  { NBETerm.em = embed_tot_or_ghost
  ; NBETerm.un = unembed_tot_or_ghost
  ; NBETerm.typ = mkFV fstar_tactics_tot_or_ghost.fv [] []
  ; NBETerm.emb_typ = fv_as_emb_typ fstar_tactics_tot_or_ghost.fv }

let e_guard_policy =
    let embed_guard_policy (rng:Range.range) (p : guard_policy) : term =
        match p with
        | SMT   -> fstar_tactics_SMT.t
        | Goal  -> fstar_tactics_Goal.t
        | Force -> fstar_tactics_Force.t
        | Drop  -> fstar_tactics_Drop.t
    in
    let unembed_guard_policy (t : term) : option guard_policy =
        match (SS.compress t).n with
        | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_SMT.lid   -> Some SMT
        | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_Goal.lid  -> Some Goal
        | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_Force.lid -> Some Force
        | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_Drop.lid  -> Some Drop
        | _ -> None
    in
    mk_emb embed_guard_policy unembed_guard_policy fstar_tactics_guard_policy.t

let e_guard_policy_nbe  =
    let embed_guard_policy cb (p:guard_policy) : NBET.t =
        match p with
        | SMT   -> mkConstruct fstar_tactics_SMT.fv [] []
        | Goal  -> mkConstruct fstar_tactics_Goal.fv [] []
        | Force -> mkConstruct fstar_tactics_Force.fv [] []
        | Drop  -> mkConstruct fstar_tactics_Drop.fv [] []
    in
    let unembed_guard_policy cb (t:NBET.t) : option guard_policy =
        match NBETerm.nbe_t_of_t t with
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_SMT.lid   -> Some SMT
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_Goal.lid  -> Some Goal
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_Force.lid -> Some Force
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_Drop.lid  -> Some Drop
        | _ -> None
    in
    { NBETerm.em = embed_guard_policy
    ; NBETerm.un = unembed_guard_policy
    ; NBETerm.typ = mkFV fstar_tactics_guard_policy.fv [] []
    ; NBETerm.emb_typ = fv_as_emb_typ fstar_tactics_guard_policy.fv }
