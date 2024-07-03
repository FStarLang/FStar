open Prims
type ('g, 'vs1, 'vs2) slprop_list_equiv = unit
let (op_Dollar_Dollar :
  Pulse_Checker_Prover_Substs.ss_t ->
    Pulse_Syntax_Base.slprop Prims.list ->
      Pulse_Syntax_Base.slprop Prims.list)
  =
  fun ss ->
    fun ts ->
      FStar_List_Tot_Base.map
        (fun t -> Pulse_Checker_Prover_Substs.ss_term t ss) ts







type ('g, 'ss, 'ctxt0, 'unsolved0) match_pass_result =
  {
  ss': Pulse_Checker_Prover_Substs.ss_t ;
  ctxt_matched: Pulse_Syntax_Base.slprop Prims.list ;
  ctxt1: Pulse_Syntax_Base.slprop Prims.list ;
  ctxt_ok: unit ;
  unsolved_matched: Pulse_Syntax_Base.slprop Prims.list ;
  unsolved1: Pulse_Syntax_Base.slprop Prims.list ;
  unsolved_ok: unit ;
  match_ok: unit }
let (__proj__Mkmatch_pass_result__item__ss' :
  Pulse_Typing_Env.env ->
    Pulse_Checker_Prover_Substs.ss_t ->
      Pulse_Syntax_Base.slprop Prims.list ->
        Pulse_Syntax_Base.slprop Prims.list ->
          (unit, unit, unit, unit) match_pass_result ->
            Pulse_Checker_Prover_Substs.ss_t)
  =
  fun g ->
    fun ss ->
      fun ctxt0 ->
        fun unsolved0 ->
          fun projectee ->
            match projectee with
            | { ss'; ctxt_matched; ctxt1; ctxt_ok; unsolved_matched;
                unsolved1; unsolved_ok; match_ok;_} -> ss'
let (__proj__Mkmatch_pass_result__item__ctxt_matched :
  Pulse_Typing_Env.env ->
    Pulse_Checker_Prover_Substs.ss_t ->
      Pulse_Syntax_Base.slprop Prims.list ->
        Pulse_Syntax_Base.slprop Prims.list ->
          (unit, unit, unit, unit) match_pass_result ->
            Pulse_Syntax_Base.slprop Prims.list)
  =
  fun g ->
    fun ss ->
      fun ctxt0 ->
        fun unsolved0 ->
          fun projectee ->
            match projectee with
            | { ss'; ctxt_matched; ctxt1; ctxt_ok; unsolved_matched;
                unsolved1; unsolved_ok; match_ok;_} -> ctxt_matched
let (__proj__Mkmatch_pass_result__item__ctxt1 :
  Pulse_Typing_Env.env ->
    Pulse_Checker_Prover_Substs.ss_t ->
      Pulse_Syntax_Base.slprop Prims.list ->
        Pulse_Syntax_Base.slprop Prims.list ->
          (unit, unit, unit, unit) match_pass_result ->
            Pulse_Syntax_Base.slprop Prims.list)
  =
  fun g ->
    fun ss ->
      fun ctxt0 ->
        fun unsolved0 ->
          fun projectee ->
            match projectee with
            | { ss'; ctxt_matched; ctxt1; ctxt_ok; unsolved_matched;
                unsolved1; unsolved_ok; match_ok;_} -> ctxt1

let (__proj__Mkmatch_pass_result__item__unsolved_matched :
  Pulse_Typing_Env.env ->
    Pulse_Checker_Prover_Substs.ss_t ->
      Pulse_Syntax_Base.slprop Prims.list ->
        Pulse_Syntax_Base.slprop Prims.list ->
          (unit, unit, unit, unit) match_pass_result ->
            Pulse_Syntax_Base.slprop Prims.list)
  =
  fun g ->
    fun ss ->
      fun ctxt0 ->
        fun unsolved0 ->
          fun projectee ->
            match projectee with
            | { ss'; ctxt_matched; ctxt1; ctxt_ok; unsolved_matched;
                unsolved1; unsolved_ok; match_ok;_} -> unsolved_matched
let (__proj__Mkmatch_pass_result__item__unsolved1 :
  Pulse_Typing_Env.env ->
    Pulse_Checker_Prover_Substs.ss_t ->
      Pulse_Syntax_Base.slprop Prims.list ->
        Pulse_Syntax_Base.slprop Prims.list ->
          (unit, unit, unit, unit) match_pass_result ->
            Pulse_Syntax_Base.slprop Prims.list)
  =
  fun g ->
    fun ss ->
      fun ctxt0 ->
        fun unsolved0 ->
          fun projectee ->
            match projectee with
            | { ss'; ctxt_matched; ctxt1; ctxt_ok; unsolved_matched;
                unsolved1; unsolved_ok; match_ok;_} -> unsolved1


let (mpr_zero :
  Pulse_Typing_Env.env ->
    Pulse_Checker_Prover_Substs.ss_t ->
      Pulse_Syntax_Base.slprop Prims.list ->
        Pulse_Syntax_Base.slprop Prims.list ->
          (unit, unit, unit, unit) match_pass_result)
  =
  fun g ->
    fun ss ->
      fun ctxt0 ->
        fun unsolved0 ->
          {
            ss' = ss;
            ctxt_matched = [];
            ctxt1 = ctxt0;
            ctxt_ok = ();
            unsolved_matched = [];
            unsolved1 = unsolved0;
            unsolved_ok = ();
            match_ok = ()
          }




let (compose_mpr :
  Pulse_Typing_Env.env ->
    Pulse_Checker_Prover_Substs.ss_t ->
      Pulse_Syntax_Base.slprop Prims.list ->
        Pulse_Syntax_Base.slprop Prims.list ->
          Pulse_Syntax_Base.slprop Prims.list ->
            Pulse_Syntax_Base.slprop Prims.list ->
              (unit, unit, unit, unit) match_pass_result ->
                (unit, unit, unit, unit) match_pass_result ->
                  (unit, unit, unit, unit) match_pass_result)
  =
  fun g ->
    fun ss ->
      fun ctxt0 ->
        fun unsolved0 ->
          fun ctxt1 ->
            fun unsolved1 ->
              fun mpr1 ->
                fun mpr2 ->
                  {
                    ss' = (mpr2.ss');
                    ctxt_matched =
                      (FStar_List_Tot_Base.op_At mpr1.ctxt_matched
                         mpr2.ctxt_matched);
                    ctxt1 = (mpr2.ctxt1);
                    ctxt_ok = ();
                    unsolved_matched =
                      (FStar_List_Tot_Base.op_At mpr1.unsolved_matched
                         mpr2.unsolved_matched);
                    unsolved1 = (mpr2.unsolved1);
                    unsolved_ok = ();
                    match_ok = ()
                  }
type ('preamble, 'pst) mpr_t = (unit, unit, unit, unit) match_pass_result
let (apply_mpr :
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      (unit, unit) mpr_t ->
        (unit Pulse_Checker_Prover_Base.prover_state, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun preamble ->
           fun pst ->
             fun mpr ->
               Obj.magic
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       {
                         Pulse_Checker_Prover_Base.pg =
                           (pst.Pulse_Checker_Prover_Base.pg);
                         Pulse_Checker_Prover_Base.remaining_ctxt =
                           (mpr.ctxt1);
                         Pulse_Checker_Prover_Base.remaining_ctxt_frame_typing
                           = ();
                         Pulse_Checker_Prover_Base.uvs =
                           (pst.Pulse_Checker_Prover_Base.uvs);
                         Pulse_Checker_Prover_Base.ss = (mpr.ss');
                         Pulse_Checker_Prover_Base.nts =
                           FStar_Pervasives_Native.None;
                         Pulse_Checker_Prover_Base.solved =
                           (Pulse_Checker_Prover_Base.op_Star
                              (Pulse_Syntax_Pure.list_as_slprop
                                 mpr.unsolved_matched)
                              pst.Pulse_Checker_Prover_Base.solved);
                         Pulse_Checker_Prover_Base.unsolved = (mpr.unsolved1);
                         Pulse_Checker_Prover_Base.k =
                           (Pulse_Checker_Base.k_elab_trans
                              preamble.Pulse_Checker_Prover_Base.g0
                              pst.Pulse_Checker_Prover_Base.pg
                              pst.Pulse_Checker_Prover_Base.pg
                              (Pulse_Checker_Prover_Base.op_Star
                                 preamble.Pulse_Checker_Prover_Base.ctxt
                                 preamble.Pulse_Checker_Prover_Base.frame)
                              (Pulse_Checker_Prover_Base.op_Star
                                 (Pulse_Checker_Prover_Base.op_Star
                                    (Pulse_Syntax_Pure.list_as_slprop
                                       pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                    preamble.Pulse_Checker_Prover_Base.frame)
                                 (Pulse_Checker_Prover_Base.op_Array_Access
                                    mpr.ss'
                                    pst.Pulse_Checker_Prover_Base.solved))
                              (Pulse_Checker_Prover_Base.op_Star
                                 (Pulse_Checker_Prover_Base.op_Star
                                    (Pulse_Syntax_Pure.list_as_slprop
                                       mpr.ctxt1)
                                    preamble.Pulse_Checker_Prover_Base.frame)
                                 (Pulse_Checker_Prover_Base.op_Array_Access
                                    mpr.ss'
                                    (Pulse_Checker_Prover_Base.op_Star
                                       (Pulse_Syntax_Pure.list_as_slprop
                                          mpr.unsolved_matched)
                                       pst.Pulse_Checker_Prover_Base.solved)))
                              (Pulse_Checker_Base.k_elab_trans
                                 preamble.Pulse_Checker_Prover_Base.g0
                                 pst.Pulse_Checker_Prover_Base.pg
                                 pst.Pulse_Checker_Prover_Base.pg
                                 (Pulse_Checker_Prover_Base.op_Star
                                    preamble.Pulse_Checker_Prover_Base.ctxt
                                    preamble.Pulse_Checker_Prover_Base.frame)
                                 (Pulse_Checker_Prover_Base.op_Star
                                    (Pulse_Checker_Prover_Base.op_Star
                                       (Pulse_Syntax_Pure.list_as_slprop
                                          pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                       preamble.Pulse_Checker_Prover_Base.frame)
                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                       pst.Pulse_Checker_Prover_Base.ss
                                       pst.Pulse_Checker_Prover_Base.solved))
                                 (Pulse_Checker_Prover_Base.op_Star
                                    (Pulse_Checker_Prover_Base.op_Star
                                       (Pulse_Syntax_Pure.list_as_slprop
                                          pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                       preamble.Pulse_Checker_Prover_Base.frame)
                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                       mpr.ss'
                                       pst.Pulse_Checker_Prover_Base.solved))
                                 pst.Pulse_Checker_Prover_Base.k
                                 (Pulse_Checker_Base.k_elab_unit
                                    pst.Pulse_Checker_Prover_Base.pg
                                    (Pulse_Checker_Prover_Base.op_Star
                                       (Pulse_Checker_Prover_Base.op_Star
                                          (Pulse_Syntax_Pure.list_as_slprop
                                             pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                          preamble.Pulse_Checker_Prover_Base.frame)
                                       (Pulse_Checker_Prover_Base.op_Array_Access
                                          mpr.ss'
                                          pst.Pulse_Checker_Prover_Base.solved))))
                              (Pulse_Checker_Base.k_elab_equiv
                                 pst.Pulse_Checker_Prover_Base.pg
                                 pst.Pulse_Checker_Prover_Base.pg
                                 (Pulse_Checker_Prover_Base.op_Star
                                    (Pulse_Checker_Prover_Base.op_Star
                                       (Pulse_Syntax_Pure.list_as_slprop
                                          pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                       preamble.Pulse_Checker_Prover_Base.frame)
                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                       mpr.ss'
                                       pst.Pulse_Checker_Prover_Base.solved))
                                 (Pulse_Checker_Prover_Base.op_Star
                                    (Pulse_Checker_Prover_Base.op_Star
                                       (Pulse_Syntax_Pure.list_as_slprop
                                          pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                       preamble.Pulse_Checker_Prover_Base.frame)
                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                       mpr.ss'
                                       pst.Pulse_Checker_Prover_Base.solved))
                                 (Pulse_Checker_Prover_Base.op_Star
                                    (Pulse_Checker_Prover_Base.op_Star
                                       (Pulse_Syntax_Pure.list_as_slprop
                                          pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                       preamble.Pulse_Checker_Prover_Base.frame)
                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                       mpr.ss'
                                       pst.Pulse_Checker_Prover_Base.solved))
                                 (Pulse_Checker_Prover_Base.op_Star
                                    (Pulse_Checker_Prover_Base.op_Star
                                       (Pulse_Syntax_Pure.list_as_slprop
                                          mpr.ctxt1)
                                       preamble.Pulse_Checker_Prover_Base.frame)
                                    (Pulse_Checker_Prover_Base.op_Array_Access
                                       mpr.ss'
                                       (Pulse_Checker_Prover_Base.op_Star
                                          (Pulse_Syntax_Pure.list_as_slprop
                                             mpr.unsolved_matched)
                                          pst.Pulse_Checker_Prover_Base.solved)))
                                 (Pulse_Checker_Base.k_elab_unit
                                    pst.Pulse_Checker_Prover_Base.pg
                                    (Pulse_Checker_Prover_Base.op_Star
                                       (Pulse_Checker_Prover_Base.op_Star
                                          (Pulse_Syntax_Pure.list_as_slprop
                                             pst.Pulse_Checker_Prover_Base.remaining_ctxt)
                                          preamble.Pulse_Checker_Prover_Base.frame)
                                       (Pulse_Checker_Prover_Base.op_Array_Access
                                          mpr.ss'
                                          pst.Pulse_Checker_Prover_Base.solved)))
                                 () ()));
                         Pulse_Checker_Prover_Base.goals_inv = ();
                         Pulse_Checker_Prover_Base.solved_inv = ();
                         Pulse_Checker_Prover_Base.progress =
                           (pst.Pulse_Checker_Prover_Base.progress ||
                              (Prims.uu___is_Cons mpr.ctxt_matched));
                         Pulse_Checker_Prover_Base.allow_ambiguous =
                           (pst.Pulse_Checker_Prover_Base.allow_ambiguous)
                       }))) uu___2 uu___1 uu___
exception NoMatch of Prims.string 
let (uu___is_NoMatch : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | NoMatch uu___ -> true | uu___ -> false
let (__proj__NoMatch__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | NoMatch uu___ -> uu___
exception Ambig of (Pulse_Syntax_Base.slprop * Pulse_Syntax_Base.slprop *
  Pulse_Syntax_Base.slprop) 
let (uu___is_Ambig : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Ambig uu___ -> true | uu___ -> false
let (__proj__Ambig__item__uu___ :
  Prims.exn ->
    (Pulse_Syntax_Base.slprop * Pulse_Syntax_Base.slprop *
      Pulse_Syntax_Base.slprop))
  = fun projectee -> match projectee with | Ambig uu___ -> uu___
type ('preamble, 'pst, 'p, 'q) match_success_t =
  (Pulse_Checker_Prover_Substs.ss_t, unit) Prims.dtuple2
type matcher_t =
  Pulse_Checker_Prover_Base.preamble ->
    unit Pulse_Checker_Prover_Base.prover_state ->
      Pulse_Syntax_Base.slprop ->
        Pulse_Syntax_Base.slprop ->
          ((unit, unit, unit, unit) match_success_t, unit)
            FStar_Tactics_Effect.tac_repr