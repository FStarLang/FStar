open Prims
let (elim_pure_head : Pulse_Syntax_Base.term) =
  let elim_pure_explicit_lid =
    Pulse_Reflection_Util.mk_steel_wrapper_lid "elim_pure_explicit" in
  Pulse_Syntax_Pure.tm_fvar (Pulse_Syntax_Base.as_fv elim_pure_explicit_lid)
let (elim_pure_head_ty : FStar_Reflection_Types.term) =
  let squash_p =
    Pulse_Reflection_Util.mk_squash Pulse_Syntax_Pure.u0
      (FStar_Reflection_Typing.bound_var Prims.int_zero) in
  let pure_p =
    Pulse_Reflection_Util.mk_pure
      (FStar_Reflection_Typing.bound_var Prims.int_zero) in
  let post =
    Pulse_Reflection_Util.mk_abs squash_p FStar_Reflection_Data.Q_Explicit
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Builtins.pack_fv Pulse_Reflection_Util.emp_lid))) in
  let cod =
    Pulse_Reflection_Util.mk_stt_ghost_comp Pulse_Syntax_Pure.u0 squash_p
      Pulse_Reflection_Util.emp_inames_tm pure_p post in
  Pulse_Reflection_Util.mk_arrow
    ((FStar_Reflection_Builtins.pack_ln
        (FStar_Reflection_Data.Tv_FVar
           (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.prop_qn))),
      FStar_Reflection_Data.Q_Explicit) cod
let (tm_fstar : Pulse_Syntax_Base.host_term -> Pulse_Syntax_Base.term) =
  fun t -> Pulse_Syntax_Base.Tm_FStar (t, FStar_Range.range_0)

let (mk_elim_pure : Pulse_Syntax_Base.term -> Pulse_Syntax_Base.st_term) =
  fun p ->
    let t =
      Pulse_Syntax_Base.Tm_STApp
        {
          Pulse_Syntax_Base.head = elim_pure_head;
          Pulse_Syntax_Base.arg_qual = FStar_Pervasives_Native.None;
          Pulse_Syntax_Base.arg = p
        } in
    Pulse_Typing.wr t
let (elim_pure_comp : Pulse_Syntax_Base.host_term -> Pulse_Syntax_Base.comp)
  =
  fun p ->
    let st =
      {
        Pulse_Syntax_Base.u = Pulse_Syntax_Pure.u_zero;
        Pulse_Syntax_Base.res =
          (tm_fstar (Pulse_Reflection_Util.mk_squash Pulse_Syntax_Pure.u0 p));
        Pulse_Syntax_Base.pre = (Pulse_Syntax_Base.Tm_Pure (tm_fstar p));
        Pulse_Syntax_Base.post = Pulse_Syntax_Base.Tm_Emp
      } in
    Pulse_Syntax_Base.C_STGhost (Pulse_Syntax_Base.Tm_EmpInames, st)
let (elim_pure_typing :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.host_term ->
      unit -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun p ->
      fun p_prop ->
        Pulse_Typing.T_STApp
          (g, elim_pure_head,
            (tm_fstar
               (FStar_Reflection_Builtins.pack_ln
                  (FStar_Reflection_Data.Tv_FVar
                     (FStar_Reflection_Builtins.pack_fv ["Prims"; "prop"])))),
            FStar_Pervasives_Native.None, (elim_pure_comp p), (tm_fstar p),
            (), ())
let (is_elim_pure :
  Pulse_Syntax_Base.term -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun vp ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               match vp with
               | Pulse_Syntax_Base.Tm_Pure (Pulse_Syntax_Base.Tm_FStar
                   (uu___1, uu___2)) -> true
               | uu___1 -> false))) uu___
let (mk :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        ((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp,
           (unit, unit, unit) Pulse_Typing.st_typing)
           FStar_Pervasives.dtuple3 FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun v ->
             fun v_typing ->
               Obj.magic
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       match v with
                       | Pulse_Syntax_Base.Tm_Pure
                           (Pulse_Syntax_Base.Tm_FStar (pp, uu___1)) ->
                           FStar_Pervasives_Native.Some
                             (FStar_Pervasives.Mkdtuple3
                                ((mk_elim_pure (tm_fstar pp)),
                                  (elim_pure_comp pp),
                                  (elim_pure_typing g pp ())))
                       | uu___1 -> FStar_Pervasives_Native.None))) uu___2
          uu___1 uu___
let (elim_pure :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        ((Pulse_Typing.env, Pulse_Syntax_Base.term, unit,
           (unit, unit, unit, unit)
             Pulse_Checker_Common.continuation_elaborator)
           FStar_Pervasives.dtuple4,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        Pulse_Checker_Auto_Util.add_elims g ctxt is_elim_pure mk ()