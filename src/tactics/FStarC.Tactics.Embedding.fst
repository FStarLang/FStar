(*
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

module FStarC.Tactics.Embedding

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.Syntax.Embeddings
open FStarC.List
open FStarC.Class.Show

open FStarC.Tactics.Common
open FStarC.Tactics.Types

module BU      = FStarC.Util
module Err     = FStarC.Errors
module NBETerm = FStarC.TypeChecker.NBETerm
module NBET    = FStarC.TypeChecker.NBETerm
module PC      = FStarC.Parser.Const
module S       = FStarC.Syntax.Syntax
module SS      = FStarC.Syntax.Subst
module U       = FStarC.Syntax.Util

type name = bv

let fstar_tactics_lid' s = PC.fstar_tactics_lid' s
let fstar_stubs_tactics_lid' s = PC.fstar_stubs_tactics_lid' s
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
    let lid = fstar_stubs_tactics_lid' ns in
    { lid = lid;
      fv  = lid_as_data_fv lid;
      t   = lid_as_data_tm lid }

let fstar_tactics_const ns =
    let lid = fstar_stubs_tactics_lid' ns in
    { lid = lid;
      fv  = S.fvconst lid;
      t   = S.tconst lid }

let fstar_tc_core_lid s : lid =
  FStarC.Ident.lid_of_path (["FStar"; "Stubs"; "TypeChecker"; "Core"]@[s]) Range.dummyRange

let fstar_tc_core_data s =
    let lid = fstar_tc_core_lid s in
    { lid = lid;
      fv  = lid_as_data_fv lid;
      t   = lid_as_data_tm lid }

let fstar_tc_core_const s =
    let lid = fstar_tc_core_lid s in
    { lid = lid;
      fv  = S.fvconst lid;
      t   = S.tconst lid }


let fstar_tactics_proofstate    = fstar_tactics_const ["Types"; "proofstate"]
let fstar_tactics_ref_proofstate = fstar_tactics_const ["Types"; "ref_proofstate"]
let fstar_tactics_goal          = fstar_tactics_const ["Types"; "goal"]

let fstar_tactics_TacticFailure = fstar_tactics_data  ["Common"; "TacticFailure"]
let fstar_tactics_SKIP          = fstar_tactics_data  ["Common"; "SKIP"]
let fstar_tactics_Stop          = fstar_tactics_data  ["Common"; "Stop"]

let fstar_tactics_direction     = fstar_tactics_const ["Types"; "direction"]
let fstar_tactics_topdown       = fstar_tactics_data  ["Types"; "TopDown"]
let fstar_tactics_bottomup      = fstar_tactics_data  ["Types"; "BottomUp"]

let fstar_tactics_ctrl_flag     = fstar_tactics_const ["Types"; "ctrl_flag"]
let fstar_tactics_Continue      = fstar_tactics_data  ["Types"; "Continue"]
let fstar_tactics_Skip          = fstar_tactics_data  ["Types"; "Skip"]
let fstar_tactics_Abort         = fstar_tactics_data  ["Types"; "Abort"]

let fstar_tc_core_unfold_side         = fstar_tc_core_const "unfold_side"
let fstar_tc_core_unfold_side_Left    = fstar_tc_core_data  "Left"
let fstar_tc_core_unfold_side_Right   = fstar_tc_core_data  "Right"
let fstar_tc_core_unfold_side_Both    = fstar_tc_core_data  "Both"
let fstar_tc_core_unfold_side_Neither = fstar_tc_core_data  "Neither"

let fstar_tc_core_tot_or_ghost        = fstar_tc_core_const "tot_or_ghost"
let fstar_tc_core_tot_or_ghost_ETotal = fstar_tc_core_data "E_Total"
let fstar_tc_core_tot_or_ghost_EGhost = fstar_tc_core_data "E_Ghost"

let fstar_tactics_guard_policy  = fstar_tactics_const ["Types"; "guard_policy"]
let fstar_tactics_SMT           = fstar_tactics_data  ["Types"; "SMT"]
let fstar_tactics_SMTSync       = fstar_tactics_data  ["Types"; "SMTSync"]
let fstar_tactics_Goal          = fstar_tactics_data  ["Types"; "Goal"]
let fstar_tactics_Drop          = fstar_tactics_data  ["Types"; "Drop"]
let fstar_tactics_Force         = fstar_tactics_data  ["Types"; "Force"]


let mk_emb (em: Range.t -> 'a -> term)
           (un: term -> option 'a)
           (t: term) =
    mk_emb (fun x r _topt _norm -> em r x)
           (fun x _norm -> un x)
           (FStarC.Syntax.Embeddings.term_as_fv t)
let embed {|embedding 'a|} r (x:'a) = FStarC.Syntax.Embeddings.embed x r None id_norm_cb
let unembed' {|embedding 'a|} x : option 'a = FStarC.Syntax.Embeddings.unembed x id_norm_cb

// let t_result_of t   = U.mk_app fstar_tactics_result.t [S.as_arg t] // TODO: uinst on t_result?

let hd'_and_args tm =
  let tm = U.unascribe tm in
  let hd, args = U.head_and_args tm in
  (U.un_uinst hd).n, args

instance e_ref_proofstate : embedding ref_proofstate = e_lazy Lazy_ref_proofstate fstar_tactics_ref_proofstate.t
instance e_proofstate : embedding proofstate = e_lazy Lazy_proofstate fstar_tactics_proofstate.t
instance e_goal       : embedding goal       = e_lazy Lazy_goal fstar_tactics_goal.t

let unfold_lazy_ref_proofstate (i : lazyinfo) : term =
    U.exp_string "(((ref proofstate)))"

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
let fv_as_emb_typ fv = S.ET_app (show fv.fv_name, [])

let e_ref_proofstate_nbe =
    let embed_ref_proofstate _cb (ps:ref_proofstate) : NBETerm.t =
        let li = { lkind = Lazy_ref_proofstate
                 ; blob = FStarC.Dyn.mkdyn ps
                 ; ltyp = fstar_tactics_ref_proofstate.t
                 ; rng = Range.dummyRange }
        in
        let thunk = Thunk.mk (fun () -> NBETerm.mk_t <| NBETerm.Constant (NBETerm.String ("(((ref_proofstate.nbe)))", Range.dummyRange))) in
        NBETerm.mk_t (NBETerm.Lazy (Inl li, thunk))
    in
    let unembed_ref_proofstate _cb (t:NBETerm.t) : option ref_proofstate =
        match NBETerm.nbe_t_of_t t with
        | NBETerm.Lazy (Inl {blob=b; lkind = Lazy_ref_proofstate}, _) ->
            Some <| FStarC.Dyn.undyn b
        | _ ->
          if !Options.debug_embedding then
            Err.log_issue0
              Err.Warning_NotEmbedded
              (Format.fmt1 "Not an embedded NBE ref_proofstate: %s\n"
                 (NBETerm.t_to_string t));
            None
    in
    { NBETerm.em = embed_ref_proofstate
    ; NBETerm.un = unembed_ref_proofstate
    ; NBETerm.typ = (fun () -> mkFV fstar_tactics_ref_proofstate.fv [] [])
    ; NBETerm.e_typ = (fun () -> fv_as_emb_typ fstar_tactics_ref_proofstate.fv)
     }

let e_proofstate_nbe =
    let embed_proofstate _cb (ps:proofstate) : NBETerm.t =
        let li = { lkind = Lazy_proofstate
                 ; blob = FStarC.Dyn.mkdyn ps
                 ; ltyp = fstar_tactics_proofstate.t
                 ; rng = Range.dummyRange }
        in
        let thunk = Thunk.mk (fun () -> NBETerm.mk_t <| NBETerm.Constant (NBETerm.String ("(((proofstate.nbe)))", Range.dummyRange))) in
        NBETerm.mk_t (NBETerm.Lazy (Inl li, thunk))
    in
    let unembed_proofstate _cb (t:NBETerm.t) : option proofstate =
        match NBETerm.nbe_t_of_t t with
        | NBETerm.Lazy (Inl {blob=b; lkind = Lazy_proofstate}, _) ->
            Some <| FStarC.Dyn.undyn b
        | _ ->
          if !Options.debug_embedding then
            Err.log_issue0
              Err.Warning_NotEmbedded
              (Format.fmt1 "Not an embedded NBE proofstate: %s\n"
                 (NBETerm.t_to_string t));
            None
    in
    { NBETerm.em = embed_proofstate
    ; NBETerm.un = unembed_proofstate
    ; NBETerm.typ = (fun () -> mkFV fstar_tactics_proofstate.fv [] [])
    ; NBETerm.e_typ = (fun () -> fv_as_emb_typ fstar_tactics_proofstate.fv)
     }

let e_goal_nbe =
    let embed_goal _cb (ps:goal) : NBETerm.t =
        let li = { lkind = Lazy_goal
                 ; blob = FStarC.Dyn.mkdyn ps
                 ; ltyp = fstar_tactics_goal.t
                 ; rng = Range.dummyRange }
        in
        let thunk = Thunk.mk (fun () -> NBETerm.mk_t <| NBETerm.Constant (NBETerm.String ("(((goal.nbe)))", Range.dummyRange))) in
        NBETerm.mk_t <| NBETerm.Lazy (Inl li, thunk)
    in
    let unembed_goal _cb (t:NBETerm.t) : option goal =
        match NBETerm.nbe_t_of_t t with
        | NBETerm.Lazy (Inl {blob=b; lkind = Lazy_goal}, _) ->
            Some <| FStarC.Dyn.undyn b
        | _ ->
            if !Options.debug_embedding then
              Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded NBE goal: %s" (NBETerm.t_to_string t));
            None
    in
    { NBETerm.em = embed_goal
    ; NBETerm.un = unembed_goal
    ; NBETerm.typ = (fun () -> mkFV fstar_tactics_goal.fv [] [])
    ; NBETerm.e_typ = (fun () -> fv_as_emb_typ fstar_tactics_goal.fv)
     }

instance e_exn : embedding exn =
    let embed_exn (e:exn) (rng:Range.t) _ _ : term =
        match e with
        | TacticFailure s ->
            S.mk_Tm_app fstar_tactics_TacticFailure.t
                [S.as_arg (embed rng s)]
                rng

        | SKIP ->
            { fstar_tactics_SKIP.t with pos = rng }

        | Errors.Stop ->
            { fstar_tactics_Stop.t with pos = rng }

        | EExn t ->
            { t with pos = rng }

        | e ->
          let open FStarC.Pprint in
          let open FStarC.Class.PP in
          let open FStarC.Errors.Msg in
          let msg, range =
            match FStarC.Errors.issue_of_exn e with
            | Some { issue_range; issue_msg } ->
              issue_msg, issue_range
            | None ->
              [arbitrary_string (BU.message_of_exn e)], None in
          let msg = text "Uncaught exception" :: msg in
          S.mk_Tm_app fstar_tactics_TacticFailure.t
              [S.as_arg (embed rng (msg, range))]
              rng
    in
    let unembed_exn (t:term) _ : option exn =
        match hd'_and_args t with
        | Tm_fvar fv, [(s, _)] when S.fv_eq_lid fv fstar_tactics_TacticFailure.lid ->
            Option.bind (unembed' s) (fun s ->
            Some (TacticFailure s))

        | Tm_fvar fv, [] when S.fv_eq_lid fv fstar_tactics_SKIP.lid ->
          Some SKIP
        | Tm_fvar fv, [] when S.fv_eq_lid fv fstar_tactics_Stop.lid ->
          Some Errors.Stop

        | _ ->
            (* Anything else, we just pass-through *)
            Some (EExn t)
    in
    mk_emb_full
        embed_exn
        unembed_exn
        (fun () -> t_exn)
        (fun _ -> "(exn)")
        (fun () -> ET_app (show PC.exn_lid, []))

let e_exn_nbe =
    let embed_exn cb (e:exn) : NBET.t =
        match e with
        | TacticFailure s ->
            mkConstruct fstar_tactics_TacticFailure.fv
              []
              [ NBETerm.as_arg (NBETerm.embed FStar.Tactics.Typeclasses.solve cb s) ]

        | SKIP ->
            mkConstruct fstar_tactics_SKIP.fv [] []

        | _ ->
            failwith (Format.fmt1 "cannot embed exn (NBE) : %s" (BU.message_of_exn e))
    in
    let unembed_exn cb (t:NBET.t) : option exn =
        match NBETerm.nbe_t_of_t t with
        | NBETerm.Construct (fv, _, [(s, _)]) when S.fv_eq_lid fv fstar_tactics_TacticFailure.lid ->
            Option.bind (NBETerm.unembed FStar.Tactics.Typeclasses.solve cb s) (fun s ->
            Some (TacticFailure s))

        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_SKIP.lid ->
            Some SKIP

        | _ ->
            None
    in
    let fv_exn = S.fvconst PC.exn_lid in
    { NBETerm.em = embed_exn
    ; NBETerm.un = unembed_exn
    ; NBETerm.typ = (fun () -> mkFV fv_exn [] [])
    ; NBETerm.e_typ = (fun () -> fv_as_emb_typ fv_exn) }

let e_direction =
    let embed_direction (rng:Range.t) (d : direction) : term =
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
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded direction: %s" (NBETerm.t_to_string t));
          None
    in
    { NBETerm.em = embed_direction
    ; NBETerm.un = unembed_direction
    ; NBETerm.typ = (fun () ->mkFV fstar_tactics_direction.fv [] [])
    ; NBETerm.e_typ = (fun () -> fv_as_emb_typ fstar_tactics_direction.fv) }

let e_ctrl_flag =
    let embed_ctrl_flag (rng:Range.t) (d : ctrl_flag) : term =
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
            Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded ctrl_flag: %s" (NBETerm.t_to_string t));
          None
    in
    { NBETerm.em = embed_ctrl_flag
    ; NBETerm.un = unembed_ctrl_flag
    ; NBETerm.typ = (fun () -> mkFV fstar_tactics_ctrl_flag.fv [] [])
    ; NBETerm.e_typ = (fun () -> fv_as_emb_typ fstar_tactics_ctrl_flag.fv) }

let e_unfold_side =
  let open FStarC.TypeChecker.Core in
  let embed_unfold_side (rng:Range.t) (s:side) : term =
    match s with
    | Left -> fstar_tc_core_unfold_side_Left.t
    | Right -> fstar_tc_core_unfold_side_Right.t
    | Both -> fstar_tc_core_unfold_side_Both.t
    | Neither  -> fstar_tc_core_unfold_side_Neither.t
  in
  let unembed_unfold_side (t : term) : option side =
    match (SS.compress t).n with
    | Tm_fvar fv when S.fv_eq_lid fv fstar_tc_core_unfold_side_Left.lid -> Some Left
    | Tm_fvar fv when S.fv_eq_lid fv fstar_tc_core_unfold_side_Right.lid -> Some Right
    | Tm_fvar fv when S.fv_eq_lid fv fstar_tc_core_unfold_side_Both.lid -> Some Both
    | Tm_fvar fv when S.fv_eq_lid fv fstar_tc_core_unfold_side_Neither.lid -> Some Neither
    | _ ->
        None
  in
  mk_emb embed_unfold_side unembed_unfold_side fstar_tc_core_unfold_side.t

let e_unfold_side_nbe  =
  let open FStarC.TypeChecker.Core in
  let embed_unfold_side cb (res:side) : NBET.t =
    match res with
    | Left -> mkConstruct fstar_tc_core_unfold_side_Left.fv [] []
    | Right -> mkConstruct fstar_tc_core_unfold_side_Right.fv [] []
    | Both -> mkConstruct fstar_tc_core_unfold_side_Both.fv [] []
    | Neither -> mkConstruct fstar_tc_core_unfold_side_Neither.fv [] []
  in
  let unembed_unfold_side cb (t:NBET.t) : option side =
    match NBETerm.nbe_t_of_t t with
    | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tc_core_unfold_side_Left.lid ->
      Some Left
    | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tc_core_unfold_side_Right.lid ->
      Some Right
    | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tc_core_unfold_side_Both.lid ->
      Some Both
    | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tc_core_unfold_side_Neither.lid ->
      Some Neither
    | _ ->
      if !Options.debug_embedding then
        Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded unfold_side: %s" (NBETerm.t_to_string t));
      None
  in
  { NBETerm.em = embed_unfold_side
  ; NBETerm.un = unembed_unfold_side
  ; NBETerm.typ = (fun () -> mkFV fstar_tc_core_unfold_side.fv [] [])
  ; NBETerm.e_typ = (fun () -> fv_as_emb_typ fstar_tc_core_unfold_side.fv) }

let e_tot_or_ghost =
  let open FStarC.TypeChecker.Core in
  let embed_tot_or_ghost (rng:Range.t) (s:tot_or_ghost) : term =
    match s with
    | E_Total -> fstar_tc_core_tot_or_ghost_ETotal.t
    | E_Ghost -> fstar_tc_core_tot_or_ghost_EGhost.t
  in
  let unembed_tot_or_ghost (t : term) : option tot_or_ghost =
    match (SS.compress t).n with
    | Tm_fvar fv when S.fv_eq_lid fv fstar_tc_core_tot_or_ghost_ETotal.lid ->
      Some E_Total
    | Tm_fvar fv when S.fv_eq_lid fv fstar_tc_core_tot_or_ghost_EGhost.lid ->
      Some E_Ghost
    | _ -> None
  in
  mk_emb embed_tot_or_ghost unembed_tot_or_ghost fstar_tc_core_tot_or_ghost.t

let e_tot_or_ghost_nbe  =
  let open FStarC.TypeChecker.Core in
  let embed_tot_or_ghost cb (res:tot_or_ghost) : NBET.t =
    match res with
    | E_Total -> mkConstruct fstar_tc_core_tot_or_ghost_ETotal.fv [] []
    | E_Ghost -> mkConstruct fstar_tc_core_tot_or_ghost_EGhost.fv [] []
  in
  let unembed_tot_or_ghost cb (t:NBET.t) : option tot_or_ghost =
    match NBETerm.nbe_t_of_t t with
    | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tc_core_tot_or_ghost_ETotal.lid ->
      Some E_Total
    | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tc_core_tot_or_ghost_EGhost.lid ->
      Some E_Ghost
    | _ ->
      if !Options.debug_embedding then
        Err.log_issue0 Err.Warning_NotEmbedded (Format.fmt1 "Not an embedded tot_or_ghost: %s" (NBETerm.t_to_string t));
      None
  in
  { NBETerm.em = embed_tot_or_ghost
  ; NBETerm.un = unembed_tot_or_ghost
  ; NBETerm.typ = (fun () -> mkFV fstar_tc_core_tot_or_ghost.fv [] [])
  ; NBETerm.e_typ = (fun () -> fv_as_emb_typ fstar_tc_core_tot_or_ghost.fv) }

let t_tref = S.lid_as_fv PC.tref_lid None
  |> S.fv_to_tm
  |> (fun tm -> S.mk_Tm_uinst tm [U_zero])
  |> (fun head -> S.mk_Tm_app head [S.iarg S.t_term] Range.dummyRange)

let e_tref #a =
  let em (r:tref a) (rng:Range.t) _shadow _norm : term =
    U.mk_lazy r t_tref Lazy_tref (Some rng)
  in
  let un (t:term) _ : option (tref a) =
    match (SS.compress t).n with
    | Tm_lazy { lkind = Lazy_tref; blob } -> Some (Dyn.undyn blob)
    | _ -> None
  in
  mk_emb_full
    em
    un
    (fun () -> t_tref)
    (fun i -> "tref")
    (fun () -> ET_app (PC.tref_lid |> Ident.string_of_lid, [ET_abstract]))

let e_tref_nbe #a =
  let embed_tref _cb (r:tref a) : NBETerm.t =
    let li = { lkind = Lazy_tref
             ; blob = FStarC.Dyn.mkdyn r
             ; ltyp = t_tref
             ; rng = Range.dummyRange }
    in
  let thunk = Thunk.mk (fun () -> NBETerm.mk_t <| NBETerm.Constant (NBETerm.String ("(((tref.nbe)))", Range.dummyRange))) in
    NBETerm.mk_t (NBETerm.Lazy (Inl li, thunk))
  in
  let unembed_tref _cb (t:NBETerm.t) : option (tref a) =
    match NBETerm.nbe_t_of_t t with
    | NBETerm.Lazy (Inl {blob=b; lkind = Lazy_tref}, _) ->
      Some <| FStarC.Dyn.undyn b
    | _ ->
      if !Options.debug_embedding then
        Err.log_issue0
          Err.Warning_NotEmbedded
          (Format.fmt1 "Not an embedded NBE tref: %s\n"
             (NBETerm.t_to_string t));
      None
  in
  { NBETerm.em = embed_tref
  ; NBETerm.un = unembed_tref
  ; NBETerm.typ =
    (fun () ->
      let term_t = mkFV (S.lid_as_fv PC.fstar_syntax_syntax_term None) [] [] in
      mkFV (S.lid_as_fv PC.tref_lid None) [U_zero] [NBETerm.as_arg term_t])
  ; NBETerm.e_typ = (fun () -> ET_app (PC.tref_lid |> Ident.string_of_lid, [ET_abstract])) }

let e_guard_policy =
    let embed_guard_policy (rng:Range.t) (p : guard_policy) : term =
        match p with
        | SMT   -> fstar_tactics_SMT.t
        | SMTSync -> fstar_tactics_SMTSync.t
        | Goal  -> fstar_tactics_Goal.t
        | Force -> fstar_tactics_Force.t
        | Drop  -> fstar_tactics_Drop.t
    in
    let unembed_guard_policy (t : term) : option guard_policy =
        match (SS.compress t).n with
        | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_SMT.lid   -> Some SMT
        | Tm_fvar fv when S.fv_eq_lid fv fstar_tactics_SMTSync.lid   -> Some SMTSync
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
        | SMTSync -> mkConstruct fstar_tactics_SMTSync.fv [] []
        | Goal  -> mkConstruct fstar_tactics_Goal.fv [] []
        | Force -> mkConstruct fstar_tactics_Force.fv [] []
        | Drop  -> mkConstruct fstar_tactics_Drop.fv [] []
    in
    let unembed_guard_policy cb (t:NBET.t) : option guard_policy =
        match NBETerm.nbe_t_of_t t with
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_SMT.lid   -> Some SMT
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_SMTSync.lid -> Some SMTSync
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_Goal.lid  -> Some Goal
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_Force.lid -> Some Force
        | NBETerm.Construct (fv, _, []) when S.fv_eq_lid fv fstar_tactics_Drop.lid  -> Some Drop
        | _ -> None
    in
    { NBETerm.em = embed_guard_policy
    ; NBETerm.un = unembed_guard_policy
    ; NBETerm.typ = (fun () -> mkFV fstar_tactics_guard_policy.fv [] [])
    ; NBETerm.e_typ = (fun () -> fv_as_emb_typ fstar_tactics_guard_policy.fv) }
