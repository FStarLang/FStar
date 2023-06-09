open Prims
let (is_pure : Pulse_Syntax_Base.term -> Prims.bool) =
  fun p ->
    match p with
    | Pulse_Syntax_Base.Tm_Pure (Pulse_Syntax_Base.Tm_FStar (uu___, uu___1))
        -> true
    | uu___ -> false
let (intro_pure_tm : Pulse_Syntax_Base.term -> Pulse_Syntax_Base.st_term) =
  fun p ->
    Pulse_Typing.wr
      (Pulse_Syntax_Base.Tm_STApp
         {
           Pulse_Syntax_Base.head =
             (Pulse_Syntax_Pure.tm_pureapp
                (Pulse_Syntax_Pure.tm_fvar
                   (Pulse_Syntax_Base.as_fv
                      (Pulse_Reflection_Util.mk_steel_wrapper_lid
                         "intro_pure"))) FStar_Pervasives_Native.None p);
           Pulse_Syntax_Base.arg_qual = FStar_Pervasives_Native.None;
           Pulse_Syntax_Base.arg =
             (Pulse_Syntax_Base.Tm_FStar
                ((FStar_Reflection_Builtins.pack_ln
                    (FStar_Reflection_Data.Tv_Const
                       FStar_Reflection_Data.C_Unit)), FStar_Range.range_0))
         })
let (intro_pure_comp : Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp) =
  fun p ->
    Pulse_Syntax_Base.C_STGhost
      (Pulse_Syntax_Base.Tm_EmpInames,
        {
          Pulse_Syntax_Base.u = Pulse_Syntax_Pure.u_zero;
          Pulse_Syntax_Base.res = Pulse_Typing.tm_unit;
          Pulse_Syntax_Base.pre = Pulse_Syntax_Base.Tm_Emp;
          Pulse_Syntax_Base.post = (Pulse_Syntax_Base.Tm_Pure p)
        })
let (intro_pure_typing :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      unit -> unit -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun p ->
      fun p_typing ->
        fun p_valid ->
          Pulse_Typing.T_STApp
            (g,
              (Pulse_Syntax_Pure.tm_pureapp
                 (Pulse_Syntax_Pure.tm_fvar
                    (Pulse_Syntax_Base.as_fv
                       (Pulse_Reflection_Util.mk_steel_wrapper_lid
                          "intro_pure"))) FStar_Pervasives_Native.None p), p,
              FStar_Pervasives_Native.None, (intro_pure_comp p),
              (Pulse_Syntax_Base.Tm_FStar
                 ((FStar_Reflection_Builtins.pack_ln
                     (FStar_Reflection_Data.Tv_Const
                        FStar_Reflection_Data.C_Unit)), FStar_Range.range_0)),
              (), ())
let (intro_pure_proof_step_aux :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop Prims.list ->
      Pulse_Syntax_Base.vprop ->
        unit ->
          ((unit, unit, unit) Pulse_Checker_Auto_Util.proof_step
             FStar_Pervasives_Native.option,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun v ->
        fun v_typing ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "Pulse.Checker.Auto.IntroPure.fst"
               (Prims.of_int (67)) (Prims.of_int (18)) (Prims.of_int (67))
               (Prims.of_int (19)))
            (FStar_Range.mk_range "Pulse.Checker.Auto.IntroPure.fst"
               (Prims.of_int (65)) (Prims.of_int (42)) (Prims.of_int (93))
               (Prims.of_int (13)))
            (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> v))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | Pulse_Syntax_Base.Tm_Pure p ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range
                              "Pulse.Checker.Auto.IntroPure.fst"
                              (Prims.of_int (69)) (Prims.of_int (4))
                              (Prims.of_int (69)) (Prims.of_int (45)))
                           (FStar_Range.mk_range
                              "Pulse.Checker.Auto.IntroPure.fst"
                              (Prims.of_int (71)) (Prims.of_int (2))
                              (Prims.of_int (93)) (Prims.of_int (13)))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> ()))
                           (fun uu___1 ->
                              (fun p_typing ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Auto.IntroPure.fst"
                                         (Prims.of_int (71))
                                         (Prims.of_int (8))
                                         (Prims.of_int (71))
                                         (Prims.of_int (56)))
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Auto.IntroPure.fst"
                                         (Prims.of_int (71))
                                         (Prims.of_int (2))
                                         (Prims.of_int (93))
                                         (Prims.of_int (13)))
                                      (Obj.magic
                                         (FStar_Tactics_Builtins.check_prop_validity
                                            (Pulse_Typing.elab_env g)
                                            (Pulse_Elaborate_Pure.elab_term p)))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              match uu___1 with
                                              | (FStar_Pervasives_Native.Some
                                                 e, uu___3) ->
                                                  FStar_Pervasives_Native.Some
                                                    {
                                                      Pulse_Checker_Auto_Util.remaining'
                                                        = ctxt;
                                                      Pulse_Checker_Auto_Util.t'
                                                        = (intro_pure_tm p);
                                                      Pulse_Checker_Auto_Util.c'
                                                        = (intro_pure_comp p);
                                                      Pulse_Checker_Auto_Util.t'_typing
                                                        =
                                                        (intro_pure_typing g
                                                           p () ());
                                                      Pulse_Checker_Auto_Util.remaining_equiv
                                                        = ()
                                                    }
                                              | uu___3 ->
                                                  FStar_Pervasives_Native.None))))
                                uu___1))) uu___)
let (intro_pure_proof_step : Pulse_Checker_Auto_Util.proof_step_fn) =
  fun g ->
    fun ctxt ->
      fun v ->
        fun uu___ ->
          fun v_typing ->
            if is_pure v
            then Obj.magic (Obj.repr (intro_pure_proof_step_aux g ctxt v ()))
            else
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___2 -> FStar_Pervasives_Native.None)))
let (get_one_pure :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop Prims.list ->
      (Pulse_Syntax_Base.vprop, Pulse_Syntax_Base.vprop Prims.list, unit)
        FStar_Pervasives.dtuple3 FStar_Pervasives_Native.option)
  = fun g -> fun l -> Prims.admit ()
let (intro_pure : Pulse_Checker_Auto_Util.intro_from_unmatched_fn) =
  fun g ->
    fun uu___ ->
      fun pst ->
        match get_one_pure g pst.Pulse_Checker_Auto_Util.unmatched_pre with
        | FStar_Pervasives_Native.None ->
            Obj.magic
              (Obj.repr
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___1 -> FStar_Pervasives_Native.None)))
        | FStar_Pervasives_Native.Some (FStar_Pervasives.Mkdtuple3
            (v, rest, veq)) ->
            Obj.magic
              (Obj.repr
                 (FStar_Tactics_Effect.tac_bind
                    (FStar_Range.mk_range "Pulse.Checker.Auto.IntroPure.fst"
                       (Prims.of_int (112)) (Prims.of_int (45))
                       (Prims.of_int (112)) (Prims.of_int (53)))
                    (FStar_Range.mk_range "Pulse.Checker.Auto.IntroPure.fst"
                       (Prims.of_int (113)) (Prims.of_int (4))
                       (Prims.of_int (121)) (Prims.of_int (18)))
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))
                    (fun uu___1 ->
                       (fun v_typing ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Auto.IntroPure.fst"
                                  (Prims.of_int (113)) (Prims.of_int (10))
                                  (Prims.of_int (113)) (Prims.of_int (65)))
                               (FStar_Range.mk_range
                                  "Pulse.Checker.Auto.IntroPure.fst"
                                  (Prims.of_int (113)) (Prims.of_int (4))
                                  (Prims.of_int (121)) (Prims.of_int (18)))
                               (Obj.magic
                                  (intro_pure_proof_step_aux g
                                     pst.Pulse_Checker_Auto_Util.remaining_ctxt
                                     v ()))
                               (fun uu___1 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       match uu___1 with
                                       | FStar_Pervasives_Native.Some ps ->
                                           FStar_Pervasives_Native.Some
                                             {
                                               Pulse_Checker_Auto_Util.v = v;
                                               Pulse_Checker_Auto_Util.ps =
                                                 ps;
                                               Pulse_Checker_Auto_Util.unmatched'
                                                 = rest;
                                               Pulse_Checker_Auto_Util.unmatched_equiv
                                                 = ()
                                             }
                                       | FStar_Pervasives_Native.None ->
                                           FStar_Pervasives_Native.None))))
                         uu___1)))