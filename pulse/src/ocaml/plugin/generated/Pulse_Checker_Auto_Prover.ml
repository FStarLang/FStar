open Prims
type framing_failure =
  {
  unmatched_preconditions: Pulse_Syntax_Base.term Prims.list ;
  remaining_context: Pulse_Syntax_Base.term Prims.list }
let (__proj__Mkframing_failure__item__unmatched_preconditions :
  framing_failure -> Pulse_Syntax_Base.term Prims.list) =
  fun projectee ->
    match projectee with
    | { unmatched_preconditions; remaining_context;_} ->
        unmatched_preconditions
let (__proj__Mkframing_failure__item__remaining_context :
  framing_failure -> Pulse_Syntax_Base.term Prims.list) =
  fun projectee ->
    match projectee with
    | { unmatched_preconditions; remaining_context;_} -> remaining_context
type ('g, 'v) vprop_typing = unit
let (ghost_comp :
  Pulse_Syntax_Base.vprop ->
    Pulse_Syntax_Base.vprop -> Pulse_Syntax_Base.comp)
  =
  fun pre ->
    fun post ->
      Pulse_Syntax_Base.C_STGhost
        (Pulse_Syntax_Base.Tm_EmpInames,
          {
            Pulse_Syntax_Base.u = Pulse_Syntax_Pure.u_zero;
            Pulse_Syntax_Base.res = Pulse_Typing.tm_unit;
            Pulse_Syntax_Base.pre = pre;
            Pulse_Syntax_Base.post = post
          })
let unit_const : 'uuuuu . unit -> 'uuuuu = fun uu___ -> Prims.magic ()
let (proof_steps_idem : Pulse_Syntax_Base.st_term) =
  {
    Pulse_Syntax_Base.term1 =
      (Pulse_Syntax_Base.Tm_Return
         {
           Pulse_Syntax_Base.ctag = Pulse_Syntax_Base.STT_Ghost;
           Pulse_Syntax_Base.insert_eq = false;
           Pulse_Syntax_Base.term = (unit_const ())
         });
    Pulse_Syntax_Base.range = FStar_Range.range_0
  }
let (proof_steps_idem_typing :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop -> (unit, unit, unit) Pulse_Typing.st_typing)
  = fun g -> fun ctxt -> Prims.magic ()
let (post_with_emp :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun t -> fun c -> fun d -> failwith "Not yet implemented:post_with_emp"
let (init_prover_state :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.comp_st ->
            (unit, unit, unit) Pulse_Typing.st_typing ->
              (unit, unit) Pulse_Checker_Auto_Util.prover_state)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun t ->
          fun c ->
            fun t_typing ->
              {
                Pulse_Checker_Auto_Util.ctxt_typing = ();
                Pulse_Checker_Auto_Util.t = t;
                Pulse_Checker_Auto_Util.c = c;
                Pulse_Checker_Auto_Util.t_typing = t_typing;
                Pulse_Checker_Auto_Util.matched_pre =
                  Pulse_Syntax_Base.Tm_Emp;
                Pulse_Checker_Auto_Util.unmatched_pre =
                  (Pulse_Checker_VPropEquiv.vprop_as_list
                     (Pulse_Syntax_Base.comp_pre c));
                Pulse_Checker_Auto_Util.remaining_ctxt =
                  (Pulse_Checker_VPropEquiv.vprop_as_list ctxt);
                Pulse_Checker_Auto_Util.proof_steps = proof_steps_idem;
                Pulse_Checker_Auto_Util.proof_steps_typing =
                  (post_with_emp g proof_steps_idem (ghost_comp ctxt ctxt)
                     (proof_steps_idem_typing g ctxt));
                Pulse_Checker_Auto_Util.pre_equiv = ()
              }
type 'c is_ghost_comp = unit
type ('g, 'ctxt, 'p) intro_result =
  {
  v: Pulse_Syntax_Base.vprop ;
  unmatched': Pulse_Syntax_Base.vprop Prims.list ;
  remaining': Pulse_Syntax_Base.vprop Prims.list ;
  t': Pulse_Syntax_Base.st_term ;
  c': Pulse_Syntax_Base.comp ;
  t'_typing: (unit, unit, unit) Pulse_Typing.st_typing ;
  unmatched_equiv: unit ;
  remaining_equiv: unit }
let (__proj__Mkintro_result__item__v :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop ->
      (unit, unit) Pulse_Checker_Auto_Util.prover_state ->
        (unit, unit, unit) intro_result -> Pulse_Syntax_Base.vprop)
  =
  fun g ->
    fun ctxt ->
      fun p ->
        fun projectee ->
          match projectee with
          | { v; unmatched'; remaining'; t'; c'; t'_typing; unmatched_equiv;
              remaining_equiv;_} -> v
let (__proj__Mkintro_result__item__unmatched' :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop ->
      (unit, unit) Pulse_Checker_Auto_Util.prover_state ->
        (unit, unit, unit) intro_result -> Pulse_Syntax_Base.vprop Prims.list)
  =
  fun g ->
    fun ctxt ->
      fun p ->
        fun projectee ->
          match projectee with
          | { v; unmatched'; remaining'; t'; c'; t'_typing; unmatched_equiv;
              remaining_equiv;_} -> unmatched'
let (__proj__Mkintro_result__item__remaining' :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop ->
      (unit, unit) Pulse_Checker_Auto_Util.prover_state ->
        (unit, unit, unit) intro_result -> Pulse_Syntax_Base.vprop Prims.list)
  =
  fun g ->
    fun ctxt ->
      fun p ->
        fun projectee ->
          match projectee with
          | { v; unmatched'; remaining'; t'; c'; t'_typing; unmatched_equiv;
              remaining_equiv;_} -> remaining'
let (__proj__Mkintro_result__item__t' :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop ->
      (unit, unit) Pulse_Checker_Auto_Util.prover_state ->
        (unit, unit, unit) intro_result -> Pulse_Syntax_Base.st_term)
  =
  fun g ->
    fun ctxt ->
      fun p ->
        fun projectee ->
          match projectee with
          | { v; unmatched'; remaining'; t'; c'; t'_typing; unmatched_equiv;
              remaining_equiv;_} -> t'
let (__proj__Mkintro_result__item__c' :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop ->
      (unit, unit) Pulse_Checker_Auto_Util.prover_state ->
        (unit, unit, unit) intro_result -> Pulse_Syntax_Base.comp)
  =
  fun g ->
    fun ctxt ->
      fun p ->
        fun projectee ->
          match projectee with
          | { v; unmatched'; remaining'; t'; c'; t'_typing; unmatched_equiv;
              remaining_equiv;_} -> c'
let (__proj__Mkintro_result__item__t'_typing :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop ->
      (unit, unit) Pulse_Checker_Auto_Util.prover_state ->
        (unit, unit, unit) intro_result ->
          (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun ctxt ->
      fun p ->
        fun projectee ->
          match projectee with
          | { v; unmatched'; remaining'; t'; c'; t'_typing; unmatched_equiv;
              remaining_equiv;_} -> t'_typing
let (add_frame :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.vprop ->
            (Pulse_Syntax_Base.comp,
              (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2)
  = fun g -> fun t -> fun c -> fun d -> fun f -> Prims.admit ()
let (with_pre_post :
  Pulse_Syntax_Base.comp_st ->
    Pulse_Syntax_Base.vprop ->
      Pulse_Syntax_Base.vprop -> Pulse_Syntax_Base.comp_st)
  =
  fun c ->
    fun pre ->
      fun post ->
        match c with
        | Pulse_Syntax_Base.C_ST s ->
            Pulse_Syntax_Base.with_st_comp c
              {
                Pulse_Syntax_Base.u = (s.Pulse_Syntax_Base.u);
                Pulse_Syntax_Base.res = (s.Pulse_Syntax_Base.res);
                Pulse_Syntax_Base.pre = pre;
                Pulse_Syntax_Base.post = post
              }
        | Pulse_Syntax_Base.C_STGhost (uu___, s) ->
            Pulse_Syntax_Base.with_st_comp c
              {
                Pulse_Syntax_Base.u = (s.Pulse_Syntax_Base.u);
                Pulse_Syntax_Base.res = (s.Pulse_Syntax_Base.res);
                Pulse_Syntax_Base.pre = pre;
                Pulse_Syntax_Base.post = post
              }
        | Pulse_Syntax_Base.C_STAtomic (uu___, s) ->
            Pulse_Syntax_Base.with_st_comp c
              {
                Pulse_Syntax_Base.u = (s.Pulse_Syntax_Base.u);
                Pulse_Syntax_Base.res = (s.Pulse_Syntax_Base.res);
                Pulse_Syntax_Base.pre = pre;
                Pulse_Syntax_Base.post = post
              }
let (pre_equiv :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.vprop ->
            unit ->
              (Pulse_Syntax_Base.comp,
                (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2)
  = fun g -> fun t -> fun c -> fun d -> fun f -> fun uu___ -> Prims.admit ()
let (pre_post_equiv :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.vprop ->
            unit ->
              Pulse_Syntax_Base.vprop ->
                unit ->
                  (Pulse_Syntax_Base.comp_st,
                    (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2)
  =
  fun g ->
    fun t ->
      fun c ->
        fun d ->
          fun pre -> fun uu___ -> fun post -> fun uu___1 -> Prims.admit ()
let (st_typing_weakening :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Typing.env -> (unit, unit, unit) Pulse_Typing.st_typing)
  = fun g -> fun t -> fun c -> fun d -> fun g' -> Prims.admit ()
let (get_next_prover_state :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop ->
      (unit, unit) Pulse_Checker_Auto_Util.prover_state ->
        (unit, unit, unit) intro_result ->
          ((unit, unit) Pulse_Checker_Auto_Util.prover_state, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun p ->
        fun r ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
               (Prims.of_int (124)) (Prims.of_int (27)) (Prims.of_int (124))
               (Prims.of_int (77)))
            (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
               (Prims.of_int (124)) (Prims.of_int (80)) (Prims.of_int (208))
               (Prims.of_int (20)))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ ->
                  Pulse_Syntax_Base.Tm_Star
                    ((Pulse_Checker_VPropEquiv.list_as_vprop r.remaining'),
                      (p.Pulse_Checker_Auto_Util.matched_pre))))
            (fun uu___ ->
               (fun remaining'_matched ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
                          (Prims.of_int (125)) (Prims.of_int (32))
                          (Prims.of_int (125)) (Prims.of_int (72)))
                       (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
                          (Prims.of_int (124)) (Prims.of_int (80))
                          (Prims.of_int (208)) (Prims.of_int (20)))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ ->
                             add_frame g
                               (__proj__Mkintro_result__item__t' g ctxt p r)
                               (__proj__Mkintro_result__item__c' g ctxt p r)
                               r.t'_typing remaining'_matched))
                       (fun uu___ ->
                          (fun uu___ ->
                             match uu___ with
                             | Prims.Mkdtuple2 (r_c', r_t'_typing) ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Auto.Prover.fst"
                                         (Prims.of_int (130))
                                         (Prims.of_int (4))
                                         (Prims.of_int (134))
                                         (Prims.of_int (61)))
                                      (FStar_Range.mk_range
                                         "Pulse.Checker.Auto.Prover.fst"
                                         (Prims.of_int (127))
                                         (Prims.of_int (60))
                                         (Prims.of_int (208))
                                         (Prims.of_int (20)))
                                      (Obj.magic
                                         (Pulse_Checker_Auto_Util.continuation_elaborator_with_bind
                                            g Pulse_Syntax_Base.Tm_Emp
                                            (ghost_comp ctxt
                                               (Pulse_Syntax_Base.Tm_Star
                                                  ((Pulse_Checker_VPropEquiv.list_as_vprop
                                                      p.Pulse_Checker_Auto_Util.remaining_ctxt),
                                                    (p.Pulse_Checker_Auto_Util.matched_pre))))
                                            p.Pulse_Checker_Auto_Util.proof_steps
                                            p.Pulse_Checker_Auto_Util.proof_steps_typing
                                            ()))
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            match uu___1 with
                                            | Prims.Mkdtuple2
                                                (x,
                                                 bind_continuation_elaborator)
                                                ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Auto.Prover.fst"
                                                        (Prims.of_int (141))
                                                        (Prims.of_int (81))
                                                        (Prims.of_int (141))
                                                        (Prims.of_int (98)))
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Auto.Prover.fst"
                                                        (Prims.of_int (141))
                                                        (Prims.of_int (101))
                                                        (Prims.of_int (208))
                                                        (Prims.of_int (20)))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 -> ()))
                                                     (fun uu___2 ->
                                                        (fun uu___2 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Auto.Prover.fst"
                                                                   (Prims.of_int (144))
                                                                   (Prims.of_int (80))
                                                                   (Prims.of_int (144))
                                                                   (Prims.of_int (88)))
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Auto.Prover.fst"
                                                                   (Prims.of_int (144))
                                                                   (Prims.of_int (91))
                                                                   (Prims.of_int (208))
                                                                   (Prims.of_int (20)))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    ()))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun d ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Prover.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (5)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Prover.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (20)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    pre_equiv
                                                                    g
                                                                    (__proj__Mkintro_result__item__t'
                                                                    g ctxt p
                                                                    r) r_c'
                                                                    r_t'_typing
                                                                    (Pulse_Syntax_Base.Tm_Star
                                                                    ((Pulse_Syntax_Base.Tm_Star
                                                                    ((Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    p.Pulse_Checker_Auto_Util.remaining_ctxt),
                                                                    (p.Pulse_Checker_Auto_Util.matched_pre))),
                                                                    Pulse_Syntax_Base.Tm_Emp))
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (r_c'1,
                                                                    r_t'_typing1)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Prover.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (78)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Prover.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (20)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    st_typing_weakening
                                                                    g
                                                                    (__proj__Mkintro_result__item__t'
                                                                    g ctxt p
                                                                    r) r_c'1
                                                                    r_t'_typing1
                                                                    (Pulse_Typing.extend
                                                                    x
                                                                    (FStar_Pervasives.Inl
                                                                    Pulse_Typing.tm_unit)
                                                                    g)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    r_t'_typing2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Prover.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (3)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Prover.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (20)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    {
                                                                    Pulse_Checker_Common.g
                                                                    = g;
                                                                    Pulse_Checker_Common.ret_ty
                                                                    =
                                                                    Pulse_Typing.tm_unit;
                                                                    Pulse_Checker_Common.u
                                                                    =
                                                                    Pulse_Syntax_Pure.u_zero;
                                                                    Pulse_Checker_Common.ty_typing
                                                                    = ();
                                                                    Pulse_Checker_Common.post
                                                                    =
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    r_c'1);
                                                                    Pulse_Checker_Common.post_typing
                                                                    = ()
                                                                    }))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    post_hint
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Prover.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (34)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Auto.Prover.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (20)))
                                                                    (Obj.magic
                                                                    (bind_continuation_elaborator
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    ((r.t'),
                                                                    r_c'1,
                                                                    r_t'_typing2))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (steps,
                                                                    steps_c,
                                                                    steps_typing)
                                                                    ->
                                                                    (match 
                                                                    pre_post_equiv
                                                                    g steps
                                                                    steps_c
                                                                    steps_typing
                                                                    ctxt ()
                                                                    (Pulse_Syntax_Base.Tm_Star
                                                                    ((Pulse_Checker_VPropEquiv.list_as_vprop
                                                                    r.remaining'),
                                                                    (Pulse_Syntax_Base.Tm_Star
                                                                    ((p.Pulse_Checker_Auto_Util.matched_pre),
                                                                    (r.v)))))
                                                                    ()
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (steps_c1,
                                                                    steps_typing1)
                                                                    ->
                                                                    {
                                                                    Pulse_Checker_Auto_Util.ctxt_typing
                                                                    = ();
                                                                    Pulse_Checker_Auto_Util.t
                                                                    =
                                                                    (p.Pulse_Checker_Auto_Util.t);
                                                                    Pulse_Checker_Auto_Util.c
                                                                    =
                                                                    (p.Pulse_Checker_Auto_Util.c);
                                                                    Pulse_Checker_Auto_Util.t_typing
                                                                    =
                                                                    (p.Pulse_Checker_Auto_Util.t_typing);
                                                                    Pulse_Checker_Auto_Util.matched_pre
                                                                    =
                                                                    (Pulse_Syntax_Base.Tm_Star
                                                                    ((p.Pulse_Checker_Auto_Util.matched_pre),
                                                                    (r.v)));
                                                                    Pulse_Checker_Auto_Util.unmatched_pre
                                                                    =
                                                                    (r.unmatched');
                                                                    Pulse_Checker_Auto_Util.remaining_ctxt
                                                                    =
                                                                    (r.remaining');
                                                                    Pulse_Checker_Auto_Util.proof_steps
                                                                    = steps;
                                                                    Pulse_Checker_Auto_Util.proof_steps_typing
                                                                    =
                                                                    steps_typing1;
                                                                    Pulse_Checker_Auto_Util.pre_equiv
                                                                    = ()
                                                                    })))))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                          uu___2))) uu___1)))
                            uu___))) uu___)
let (tm_prop : Pulse_Syntax_Base.term) =
  Pulse_Syntax_Base.Tm_FStar
    (FStar_Reflection_Typing.tm_prop, FStar_Range.range_0)
type intro_step_t =
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop ->
      (unit, unit) Pulse_Checker_Auto_Util.prover_state ->
        ((unit, unit, unit) intro_result FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr
let (get_one_pure :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop Prims.list ->
      (Pulse_Syntax_Base.vprop, Pulse_Syntax_Base.vprop Prims.list, unit)
        FStar_Pervasives.dtuple3 FStar_Pervasives_Native.option)
  = fun g -> fun l -> Prims.admit ()
let (step_intro_exists : intro_step_t) =
  fun uu___ ->
    let uu___ = Obj.magic uu___ in
    Obj.magic (failwith "Not yet implemented:step_intro_exists")
let (step_intro_pure : intro_step_t) =
  fun uu___ ->
    let uu___ = Obj.magic uu___ in
    Obj.magic (failwith "Not yet implemented:step_intro_pure")
let (step_intro_rewrite : intro_step_t) =
  fun uu___ ->
    let uu___ = Obj.magic uu___ in
    Obj.magic (failwith "Not yet implemented:step_intro_rewrite")
let (prover_step_intro_exists :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop ->
      (unit, unit) Pulse_Checker_Auto_Util.prover_state ->
        ((unit, unit) Pulse_Checker_Auto_Util.prover_state
           FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun o ->
      fun p ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
             (Prims.of_int (239)) (Prims.of_int (34)) (Prims.of_int (239))
             (Prims.of_int (55)))
          (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
             (Prims.of_int (239)) (Prims.of_int (2)) (Prims.of_int (239))
             (Prims.of_int (55))) (Obj.magic (step_intro_exists g o p))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Util.map_opt (get_next_prover_state g o p)
                     uu___)) uu___)
let (prover_step_intro_pure :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop ->
      (unit, unit) Pulse_Checker_Auto_Util.prover_state ->
        ((unit, unit) Pulse_Checker_Auto_Util.prover_state
           FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun o ->
      fun p ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
             (Prims.of_int (243)) (Prims.of_int (34)) (Prims.of_int (243))
             (Prims.of_int (53)))
          (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
             (Prims.of_int (243)) (Prims.of_int (2)) (Prims.of_int (243))
             (Prims.of_int (53))) (Obj.magic (step_intro_pure g o p))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Util.map_opt (get_next_prover_state g o p)
                     uu___)) uu___)
let (prover_step_intro_rewrite :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop ->
      (unit, unit) Pulse_Checker_Auto_Util.prover_state ->
        ((unit, unit) Pulse_Checker_Auto_Util.prover_state
           FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun o ->
      fun p ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
             (Prims.of_int (247)) (Prims.of_int (34)) (Prims.of_int (247))
             (Prims.of_int (56)))
          (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
             (Prims.of_int (247)) (Prims.of_int (2)) (Prims.of_int (247))
             (Prims.of_int (56))) (Obj.magic (step_intro_rewrite g o p))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Util.map_opt (get_next_prover_state g o p)
                     uu___)) uu___)
let rec (first_success :
  Pulse_Checker_Auto_Util.prover_step_t Prims.list ->
    Pulse_Checker_Auto_Util.prover_step_t)
  =
  fun uu___ ->
    (fun l ->
       fun g ->
         fun o ->
           fun p ->
             match l with
             | [] ->
                 Obj.magic
                   (Obj.repr
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ -> FStar_Pervasives_Native.None)))
             | s::l1 ->
                 Obj.magic
                   (Obj.repr
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range
                            "Pulse.Checker.Auto.Prover.fst"
                            (Prims.of_int (254)) (Prims.of_int (12))
                            (Prims.of_int (254)) (Prims.of_int (15)))
                         (FStar_Range.mk_range
                            "Pulse.Checker.Auto.Prover.fst"
                            (Prims.of_int (254)) (Prims.of_int (6))
                            (Prims.of_int (256)) (Prims.of_int (24)))
                         (Obj.magic (s g o p))
                         (fun uu___ ->
                            (fun uu___ ->
                               match uu___ with
                               | FStar_Pervasives_Native.None ->
                                   Obj.magic
                                     (Obj.repr (first_success l1 g o p))
                               | FStar_Pervasives_Native.Some p1 ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              FStar_Pervasives_Native.Some p1))))
                              uu___)))) uu___
let (step : Pulse_Checker_Auto_Util.prover_step_t) =
  first_success
    [Pulse_Checker_Auto_Framing.step_match;
    prover_step_intro_exists;
    prover_step_intro_pure;
    prover_step_intro_rewrite]
let (finish :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop ->
      (unit, unit) Pulse_Checker_Auto_Util.prover_state ->
        (Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp_st,
          (unit, unit, unit) Pulse_Typing.st_typing) FStar_Pervasives.dtuple3)
  =
  fun g ->
    fun o ->
      fun p ->
        let t_typing =
          Pulse_Typing_Metatheory.st_typing_equiv_pre g
            (Pulse_Checker_Auto_Util.__proj__Mkprover_state__item__t g o p)
            (Pulse_Checker_Auto_Util.__proj__Mkprover_state__item__c g o p)
            p.Pulse_Checker_Auto_Util.t_typing
            p.Pulse_Checker_Auto_Util.matched_pre () in
        let framing_token =
          FStar_Pervasives.Mkdtuple3
            ((Pulse_Checker_VPropEquiv.list_as_vprop
                p.Pulse_Checker_Auto_Util.remaining_ctxt), (), ()) in
        let uu___ =
          Pulse_Checker_Framing.apply_frame g p.Pulse_Checker_Auto_Util.t
            (Pulse_Checker_Auto_Util.proof_steps_post g o p) ()
            (Pulse_Typing_Metatheory.comp_st_with_pre
               p.Pulse_Checker_Auto_Util.c
               p.Pulse_Checker_Auto_Util.matched_pre) t_typing framing_token in
        match uu___ with
        | Prims.Mkdtuple2 (uu___1, t_typing1) ->
            let uu___2 =
              Pulse_Checker_Auto_Util.bind_proof_steps_with g o p
                p.Pulse_Checker_Auto_Util.t uu___1 t_typing1 in
            (match uu___2 with
             | Prims.Mkdtuple2 (t, t_typing2) ->
                 FStar_Pervasives.Mkdtuple3
                   (t, (Pulse_Typing_Metatheory.comp_st_with_pre uu___1 o),
                     t_typing2))
let (as_failure :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop ->
      (unit, unit) Pulse_Checker_Auto_Util.prover_state -> framing_failure)
  =
  fun g ->
    fun o ->
      fun p ->
        {
          unmatched_preconditions = (p.Pulse_Checker_Auto_Util.unmatched_pre);
          remaining_context = (p.Pulse_Checker_Auto_Util.remaining_ctxt)
        }
let rec (solve :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop ->
      (unit, unit) Pulse_Checker_Auto_Util.prover_state ->
        (((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp_st,
            (unit, unit, unit) Pulse_Typing.st_typing)
            FStar_Pervasives.dtuple3,
           framing_failure) FStar_Pervasives.either,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun o ->
      fun p ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
             (Prims.of_int (294)) (Prims.of_int (10)) (Prims.of_int (294))
             (Prims.of_int (16)))
          (FStar_Range.mk_range "Pulse.Checker.Auto.Prover.fst"
             (Prims.of_int (294)) (Prims.of_int (4)) (Prims.of_int (299))
             (Prims.of_int (20))) (Obj.magic (step g o p))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | FStar_Pervasives_Native.None ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               FStar_Pervasives.Inr (as_failure g o p))))
                | FStar_Pervasives_Native.Some p1 ->
                    Obj.magic
                      (Obj.repr
                         (match p1.Pulse_Checker_Auto_Util.unmatched_pre with
                          | [] ->
                              Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 ->
                                      FStar_Pervasives.Inl (finish g o p1)))
                          | uu___1 -> Obj.repr (solve g o p1)))) uu___)
let (prove_precondition :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        Pulse_Syntax_Base.st_term ->
          Pulse_Syntax_Base.comp_st ->
            (unit, unit, unit) Pulse_Typing.st_typing ->
              (((Pulse_Syntax_Base.st_term, Pulse_Syntax_Base.comp_st,
                  (unit, unit, unit) Pulse_Typing.st_typing)
                  FStar_Pervasives.dtuple3,
                 framing_failure) FStar_Pervasives.either,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun t ->
          fun c ->
            fun t_typing ->
              solve g ctxt (init_prover_state g ctxt () t c t_typing)