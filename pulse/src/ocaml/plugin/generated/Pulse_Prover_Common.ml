open Prims
type ('g, 't) vprop_typing = unit
type preamble =
  {
  g0: Pulse_Typing_Env.env ;
  ctxt: Pulse_Syntax_Base.vprop ;
  ctxt_typing: unit ;
  goals: Pulse_Syntax_Base.vprop }
let (__proj__Mkpreamble__item__g0 : preamble -> Pulse_Typing_Env.env) =
  fun projectee ->
    match projectee with | { g0; ctxt; ctxt_typing; goals;_} -> g0
let (__proj__Mkpreamble__item__ctxt : preamble -> Pulse_Syntax_Base.vprop) =
  fun projectee ->
    match projectee with | { g0; ctxt; ctxt_typing; goals;_} -> ctxt

let (__proj__Mkpreamble__item__goals : preamble -> Pulse_Syntax_Base.vprop) =
  fun projectee ->
    match projectee with | { g0; ctxt; ctxt_typing; goals;_} -> goals
type ss_t = (Pulse_Syntax_Base.var, Pulse_Syntax_Base.term) FStar_Map.t
let (as_subst : ss_t -> Pulse_Syntax_Naming.subst) = fun ss -> Prims.magic ()
let (shift : ss_t -> Pulse_Syntax_Naming.subst_elt Prims.list) =
  fun ss -> Pulse_Syntax_Naming.shift_subst (as_subst ss)
let (op_Array_Access :
  ss_t -> Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term) =
  fun ss -> fun t -> Pulse_Syntax_Naming.subst_term t (as_subst ss)
let op_String_Access :
  'uuuuu 'uuuuu1 . unit -> ('uuuuu, 'uuuuu1) FStar_Map.t -> 'uuuuu -> 'uuuuu1
  = fun uu___ -> FStar_Map.sel
let (op_Star :
  Pulse_Syntax_Base.vprop ->
    Pulse_Syntax_Base.vprop -> Pulse_Syntax_Base.term)
  = Pulse_Syntax_Base.tm_star
type ('ss, 'uvs, 'g) well_typed_ss = unit
type 'preamble1 prover_state =
  {
  pg: Pulse_Typing_Env.env ;
  remaining_ctxt: Pulse_Syntax_Base.vprop Prims.list ;
  uvs: Pulse_Typing_Env.env ;
  ss: ss_t ;
  solved: Pulse_Syntax_Base.vprop ;
  unsolved: Pulse_Syntax_Base.vprop Prims.list ;
  k:
    (unit, unit, unit, unit) Pulse_Checker_Auto_Elims.continuation_elaborator ;
  goals_inv: unit ;
  solved_inv: unit }
let (__proj__Mkprover_state__item__pg :
  preamble -> unit prover_state -> Pulse_Typing_Env.env) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; uvs; ss; solved; unsolved; k; goals_inv;
          solved_inv;_} -> pg
let (__proj__Mkprover_state__item__remaining_ctxt :
  preamble -> unit prover_state -> Pulse_Syntax_Base.vprop Prims.list) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; uvs; ss; solved; unsolved; k; goals_inv;
          solved_inv;_} -> remaining_ctxt
let (__proj__Mkprover_state__item__uvs :
  preamble -> unit prover_state -> Pulse_Typing_Env.env) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; uvs; ss; solved; unsolved; k; goals_inv;
          solved_inv;_} -> uvs
let (__proj__Mkprover_state__item__ss :
  preamble -> unit prover_state -> ss_t) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; uvs; ss; solved; unsolved; k; goals_inv;
          solved_inv;_} -> ss
let (__proj__Mkprover_state__item__solved :
  preamble -> unit prover_state -> Pulse_Syntax_Base.vprop) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; uvs; ss; solved; unsolved; k; goals_inv;
          solved_inv;_} -> solved
let (__proj__Mkprover_state__item__unsolved :
  preamble -> unit prover_state -> Pulse_Syntax_Base.vprop Prims.list) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; uvs; ss; solved; unsolved; k; goals_inv;
          solved_inv;_} -> unsolved
let (__proj__Mkprover_state__item__k :
  preamble ->
    unit prover_state ->
      (unit, unit, unit, unit)
        Pulse_Checker_Auto_Elims.continuation_elaborator)
  =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; uvs; ss; solved; unsolved; k; goals_inv;
          solved_inv;_} -> k
type ('ss, 'uvs) covers = (Pulse_Syntax_Base.var, unit, unit) FStar_Set.equal
type ('preamble1, 'st) is_terminal = unit
let (prove :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        Pulse_Typing_Env.env ->
          Pulse_Syntax_Base.vprop ->
            unit ->
              ((Pulse_Typing_Env.env, ss_t, Pulse_Syntax_Base.vprop,
                 (unit, unit, unit, unit)
                   Pulse_Checker_Auto_Elims.continuation_elaborator)
                 FStar_Pervasives.dtuple4,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun ctxt ->
                   fun ctxt_typing ->
                     fun uvs ->
                       fun goals ->
                         fun goals_typing ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> Prims.magic ()))) uu___5 uu___4
                uu___3 uu___2 uu___1 uu___
let (check_stapp_no_ctxt :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      ((Pulse_Typing_Env.env, Pulse_Syntax_Base.st_term,
         Pulse_Syntax_Base.comp_st,
         (unit, unit, unit) Pulse_Typing.st_typing) FStar_Pervasives.dtuple4,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun t ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> Prims.magic ())))
        uu___1 uu___
let (extend_post_hint_opt_g :
  Pulse_Typing_Env.env ->
    unit Pulse_Checker_Common.post_hint_opt ->
      Pulse_Typing_Env.env -> unit Pulse_Checker_Common.post_hint_opt)
  =
  fun g ->
    fun post_hint ->
      fun g1 ->
        match post_hint with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some post_hint1 ->
            FStar_Pervasives_Native.Some post_hint1
let (add_frame :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.vprop ->
            ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp_st,
               (unit, unit, unit) Pulse_Typing.st_typing)
               FStar_Pervasives.dtuple3,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun g ->
               fun t ->
                 fun c ->
                   fun t_typing ->
                     fun frame ->
                       Obj.magic
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> Prims.magic ()))) uu___4 uu___3
              uu___2 uu___1 uu___
let (st_typing_subst :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.comp_st ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            ss_t ->
              ((unit, unit, unit) Pulse_Typing.st_typing, unit)
                FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun uvs ->
                   fun t ->
                     fun c ->
                       fun uu___ ->
                         fun ss ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 -> Prims.magic ()))) uu___5
                uu___4 uu___3 uu___2 uu___1 uu___
let (st_typing_weakening :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.comp_st ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            Pulse_Typing_Env.env ->
              ((unit, unit, unit) Pulse_Typing.st_typing, unit)
                FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun g' ->
                   fun t ->
                     fun c ->
                       fun uu___ ->
                         fun g1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 -> Prims.magic ()))) uu___5
                uu___4 uu___3 uu___2 uu___1 uu___
let (mk_bind' :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.comp_st ->
            Pulse_Syntax_Base.comp_st ->
              Pulse_Syntax_Base.nvar ->
                (unit, unit, unit) Pulse_Typing.st_typing ->
                  unit ->
                    (unit, unit, unit) Pulse_Typing.st_typing ->
                      unit Pulse_Checker_Common.post_hint_opt ->
                        unit ->
                          ((unit, unit, unit)
                             Pulse_Checker_Common.checker_result_t,
                            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___11 ->
    fun uu___10 ->
      fun uu___9 ->
        fun uu___8 ->
          fun uu___7 ->
            fun uu___6 ->
              fun uu___5 ->
                fun uu___4 ->
                  fun uu___3 ->
                    fun uu___2 ->
                      fun uu___1 ->
                        fun uu___ ->
                          (fun g ->
                             fun pre ->
                               fun e1 ->
                                 fun e2 ->
                                   fun c1 ->
                                     fun c2 ->
                                       fun px ->
                                         fun d_e1 ->
                                           fun d_c1res ->
                                             fun d_e2 ->
                                               fun post_hint ->
                                                 fun uu___ ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           Prims.magic ())))
                            uu___11 uu___10 uu___9 uu___8 uu___7 uu___6
                            uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (check_bind :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          unit Pulse_Checker_Common.post_hint_opt ->
            Pulse_Checker_Common.check_t ->
              ((unit, unit, unit) Pulse_Checker_Common.checker_result_t,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            fun check ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.Common.fsti"
                         (Prims.of_int (148)) (Prims.of_int (47))
                         (Prims.of_int (148)) (Prims.of_int (53)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.Common.fsti"
                         (Prims.of_int (146)) (Prims.of_int (46))
                         (Prims.of_int (191)) (Prims.of_int (47)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> t.Pulse_Syntax_Base.term1))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | Pulse_Syntax_Base.Tm_Bind
                          { Pulse_Syntax_Base.binder = b;
                            Pulse_Syntax_Base.head1 = e1;
                            Pulse_Syntax_Base.body1 = e2;_}
                          ->
                          (match e1.Pulse_Syntax_Base.term1 with
                           | Pulse_Syntax_Base.Tm_STApp uu___1 ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Prover.Common.fsti"
                                             (Prims.of_int (152))
                                             (Prims.of_int (33))
                                             (Prims.of_int (152))
                                             (Prims.of_int (57)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Prover.Common.fsti"
                                             (Prims.of_int (151))
                                             (Prims.of_int (17))
                                             (Prims.of_int (189))
                                             (Prims.of_int (19)))))
                                    (Obj.magic (check_stapp_no_ctxt g e1))
                                    (fun uu___2 ->
                                       (fun uu___2 ->
                                          match uu___2 with
                                          | FStar_Pervasives.Mkdtuple4
                                              (uvs1, e11, c1, d1) ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Prover.Common.fsti"
                                                            (Prims.of_int (153))
                                                            (Prims.of_int (14))
                                                            (Prims.of_int (153))
                                                            (Prims.of_int (16)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Prover.Common.fsti"
                                                            (Prims.of_int (153))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (189))
                                                            (Prims.of_int (19)))))
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 -> c1))
                                                   (fun uu___3 ->
                                                      (fun c10 ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (53)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (19)))))
                                                              (Obj.magic
                                                                 (prove g pre
                                                                    () uvs1
                                                                    (
                                                                    Pulse_Syntax_Base.comp_pre
                                                                    c1) ()))
                                                              (fun uu___3 ->
                                                                 (fun uu___3
                                                                    ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (g1, ss1,
                                                                    remaining_pre,
                                                                    k) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.fresh
                                                                    g1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ((b.Pulse_Syntax_Base.binder_ppname),
                                                                    x)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun px
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Pulse_Typing_Env.push_binding
                                                                    g1 x
                                                                    b.Pulse_Syntax_Base.binder_ppname
                                                                    (op_Array_Access
                                                                    ss1
                                                                    (Pulse_Syntax_Base.comp_res
                                                                    c1))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun g2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    op_Star
                                                                    (Pulse_Syntax_Naming.open_term_nv
                                                                    (Pulse_Syntax_Naming.subst_term
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c1)
                                                                    (shift
                                                                    ss1)) px)
                                                                    remaining_pre))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    pre_e2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (check g2
                                                                    (Pulse_Syntax_Naming.open_st_term_nv
                                                                    e2 px)
                                                                    pre_e2 ()
                                                                    (extend_post_hint_opt_g
                                                                    g
                                                                    post_hint
                                                                    g2)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e21, c2,
                                                                    d2) ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.stateful_comp
                                                                    c2)
                                                                    then
                                                                    Obj.magic
                                                                    (Pulse_Typing_Env.fail
                                                                    g
                                                                    FStar_Pervasives_Native.None
                                                                    "Bind: c2 is not st")
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (st_typing_weakening
                                                                    g uvs1
                                                                    e11 c1 d1
                                                                    g1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (st_typing_subst
                                                                    g1 uvs1
                                                                    e11 c1
                                                                    d11 ss1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun d12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (175))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (add_frame
                                                                    g1
                                                                    (Pulse_Syntax_Naming.subst_st_term
                                                                    e11
                                                                    (as_subst
                                                                    ss1))
                                                                    (Pulse_Syntax_Naming.subst_comp
                                                                    c1
                                                                    (as_subst
                                                                    ss1)) d12
                                                                    remaining_pre))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e12,
                                                                    c11, d13)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Pulse_Syntax_Naming.close_st_term
                                                                    e21 x))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    e2_closed
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    (mk_bind'
                                                                    g1
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c11) e12
                                                                    e2_closed
                                                                    c11 c2 px
                                                                    d13 () d2
                                                                    post_hint
                                                                    ()))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun r ->
                                                                    Obj.magic
                                                                    (k
                                                                    post_hint
                                                                    r))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                   uu___3)))
                                                        uu___3))) uu___2))
                           | uu___1 ->
                               Obj.magic
                                 (Pulse_Typing_Env.fail g
                                    FStar_Pervasives_Native.None
                                    "Bind: e1 is not an stapp"))) uu___)
type ('ss1, 'ss2) ss_extends = unit
type ('preamble1, 'pst1, 'pst2) pst_extends = unit
type prover_t =
  preamble ->
    unit prover_state ->
      (unit prover_state, unit) FStar_Tactics_Effect.tac_repr
let (k_intro_exists :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.universe ->
      Pulse_Syntax_Base.binder ->
        Pulse_Syntax_Base.vprop ->
          Pulse_Syntax_Base.term ->
            Pulse_Syntax_Base.vprop ->
              ((unit, unit, unit, unit)
                 Pulse_Checker_Auto_Elims.continuation_elaborator,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun u ->
                   fun b ->
                     fun p ->
                       fun e ->
                         fun frame ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> Prims.magic ()))) uu___5 uu___4
                uu___3 uu___2 uu___1 uu___
let (intro_exists :
  preamble ->
    unit prover_state ->
      Pulse_Syntax_Base.universe ->
        Pulse_Syntax_Base.binder ->
          Pulse_Syntax_Base.vprop ->
            Pulse_Syntax_Base.vprop Prims.list ->
              unit ->
                prover_t ->
                  (unit prover_state, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun preamble1 ->
    fun pst ->
      fun u ->
        fun b ->
          fun body ->
            fun unsolved' ->
              fun uu___ ->
                fun prover ->
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Prover.Common.fsti"
                             (Prims.of_int (222)) (Prims.of_int (10))
                             (Prims.of_int (222)) (Prims.of_int (22)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Prover.Common.fsti"
                             (Prims.of_int (222)) (Prims.of_int (25))
                             (Prims.of_int (390)) (Prims.of_int (6)))))
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 -> Pulse_Typing_Env.fresh pst.pg))
                    (fun uu___1 ->
                       (fun x ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Prover.Common.fsti"
                                        (Prims.of_int (223))
                                        (Prims.of_int (11))
                                        (Prims.of_int (223))
                                        (Prims.of_int (29)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Prover.Common.fsti"
                                        (Prims.of_int (223))
                                        (Prims.of_int (32))
                                        (Prims.of_int (390))
                                        (Prims.of_int (6)))))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     ((b.Pulse_Syntax_Base.binder_ppname), x)))
                               (fun uu___1 ->
                                  (fun px ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Prover.Common.fsti"
                                                   (Prims.of_int (225))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (228))
                                                   (Prims.of_int (74)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Prover.Common.fsti"
                                                   (Prims.of_int (229))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (390))
                                                   (Prims.of_int (6)))))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___1 ->
                                                {
                                                  g0 = (pst.pg);
                                                  ctxt =
                                                    (op_Star
                                                       (Pulse_Checker_VPropEquiv.list_as_vprop
                                                          pst.remaining_ctxt)
                                                       (op_Array_Access
                                                          pst.ss pst.solved));
                                                  ctxt_typing = ();
                                                  goals =
                                                    (op_Star
                                                       (op_Star pst.solved
                                                          (Pulse_Syntax_Naming.open_term_nv
                                                             body px))
                                                       (Pulse_Checker_VPropEquiv.list_as_vprop
                                                          unsolved'))
                                                }))
                                          (fun uu___1 ->
                                             (fun preamble_sub ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Prover.Common.fsti"
                                                              (Prims.of_int (231))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (239))
                                                              (Prims.of_int (20)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Prover.Common.fsti"
                                                              (Prims.of_int (240))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (390))
                                                              (Prims.of_int (6)))))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           {
                                                             pg = (pst.pg);
                                                             remaining_ctxt =
                                                               (Pulse_Checker_VPropEquiv.vprop_as_list
                                                                  preamble_sub.ctxt);
                                                             uvs = (pst.uvs);
                                                             ss = (pst.ss);
                                                             solved =
                                                               Pulse_Syntax_Base.tm_emp;
                                                             unsolved =
                                                               (FStar_List_Tot_Base.append
                                                                  (Pulse_Checker_VPropEquiv.vprop_as_list
                                                                    (op_Array_Access
                                                                    pst.ss
                                                                    pst.solved))
                                                                  (FStar_List_Tot_Base.append
                                                                    [
                                                                    Pulse_Syntax_Naming.open_term_nv
                                                                    body px]
                                                                    unsolved'));
                                                             k =
                                                               (Prims.magic
                                                                  ());
                                                             goals_inv = ();
                                                             solved_inv = ()
                                                           }))
                                                     (fun uu___1 ->
                                                        (fun pst_sub ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (39)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (6)))))
                                                                (Obj.magic
                                                                   (prover
                                                                    preamble_sub
                                                                    pst_sub))
                                                                (fun uu___1
                                                                   ->
                                                                   (fun
                                                                    pst_sub_terminal
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    pst_sub_terminal_goals_inv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    pst_sub_terminal_goals_inv1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    pst_sub_terminal.k))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    k_sub_terminal
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (12)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Prims.magic
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    k_sub_terminal1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    k_sub_terminal1))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    k_sub_terminal2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    op_Array_Access
                                                                    pst_sub_terminal.ss
                                                                    (Pulse_Syntax_Pure.null_var
                                                                    x)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    witness
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (6)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    Prims.magic
                                                                    ()))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    k_sub_terminal3
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fsti"
                                                                    (Prims.of_int (379))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    (k_intro_exists
                                                                    pst_sub_terminal.pg
                                                                    u
                                                                    (Pulse_Syntax_Naming.subst_binder
                                                                    b
                                                                    (as_subst
                                                                    pst_sub_terminal.ss))
                                                                    (op_Array_Access
                                                                    pst_sub_terminal.ss
                                                                    body)
                                                                    witness
                                                                    (op_Star
                                                                    (op_Star
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    pst_sub_terminal.remaining_ctxt)
                                                                    (op_Array_Access
                                                                    pst_sub_terminal.ss
                                                                    pst.solved))
                                                                    (op_Array_Access
                                                                    pst_sub_terminal.ss
                                                                    (Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    unsolved')))))
                                                                    (fun
                                                                    k_intro_exists1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    {
                                                                    pg =
                                                                    (pst_sub_terminal.pg);
                                                                    remaining_ctxt
                                                                    =
                                                                    (pst_sub_terminal.remaining_ctxt);
                                                                    uvs =
                                                                    (pst_sub_terminal.uvs);
                                                                    ss =
                                                                    (pst_sub_terminal.ss);
                                                                    solved =
                                                                    (preamble1.goals);
                                                                    unsolved
                                                                    = [];
                                                                    k =
                                                                    (Prims.magic
                                                                    ());
                                                                    goals_inv
                                                                    = ();
                                                                    solved_inv
                                                                    = ()
                                                                    }))))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                                    uu___1)))
                                                          uu___1))) uu___1)))
                                    uu___1))) uu___1)
let (try_match_pq :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.vprop ->
        unit ->
          Pulse_Syntax_Base.vprop ->
            unit ->
              ((ss_t, unit) Prims.dtuple2 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun uvs ->
                   fun p ->
                     fun p_typing ->
                       fun q ->
                         fun q_typing ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> Prims.magic ()))) uu___5 uu___4
                uu___3 uu___2 uu___1 uu___
let (compose_ss : ss_t -> ss_t -> ss_t) =
  fun ss1 -> fun ss2 -> Prims.magic ()
let (match_step :
  preamble ->
    unit prover_state ->
      Pulse_Syntax_Base.vprop ->
        Pulse_Syntax_Base.vprop Prims.list ->
          Pulse_Syntax_Base.vprop ->
            Pulse_Syntax_Base.vprop Prims.list ->
              unit ->
                (unit prover_state FStar_Pervasives_Native.option, unit)
                  FStar_Tactics_Effect.tac_repr)
  =
  fun preamble1 ->
    fun pst ->
      fun p ->
        fun remaining_ctxt' ->
          fun q ->
            fun unsolved' ->
              fun uu___ ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Prover.Common.fsti"
                           (Prims.of_int (408)) (Prims.of_int (11))
                           (Prims.of_int (408)) (Prims.of_int (21)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Prover.Common.fsti"
                           (Prims.of_int (409)) (Prims.of_int (56))
                           (Prims.of_int (469)) (Prims.of_int (11)))))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 -> op_Array_Access pst.ss q))
                  (fun uu___1 ->
                     (fun q_ss ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Prover.Common.fsti"
                                      (Prims.of_int (411))
                                      (Prims.of_int (11))
                                      (Prims.of_int (411))
                                      (Prims.of_int (69)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Prover.Common.fsti"
                                      (Prims.of_int (412)) Prims.int_zero
                                      (Prims.of_int (469))
                                      (Prims.of_int (11)))))
                             (Obj.magic
                                (try_match_pq pst.pg pst.uvs p () q_ss ()))
                             (fun ropt ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     match ropt with
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Pervasives_Native.None
                                     | FStar_Pervasives_Native.Some
                                         (Prims.Mkdtuple2 (ss_q, veq)) ->
                                         FStar_Pervasives_Native.Some
                                           {
                                             pg = (pst.pg);
                                             remaining_ctxt = remaining_ctxt';
                                             uvs = (pst.uvs);
                                             ss = (compose_ss ss_q pst.ss);
                                             solved = (op_Star q pst.solved);
                                             unsolved = unsolved';
                                             k = (Prims.magic ());
                                             goals_inv = ();
                                             solved_inv = ()
                                           })))) uu___1)