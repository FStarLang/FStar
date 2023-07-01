open Prims
type ('g, 't) vprop_typing = unit
type ('g, 'ctxt, 'gu, 'ctxtu) continuation_elaborator =
  unit Pulse_Typing.post_hint_opt ->
    (unit, unit, unit) Pulse_Checker_Common.checker_result_t ->
      ((unit, unit, unit) Pulse_Checker_Common.checker_result_t, unit)
        FStar_Tactics_Effect.tac_repr
let (k_elab_unit :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      (unit, unit, unit, unit) continuation_elaborator)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun ctxt ->
           fun p ->
             fun r ->
               Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> r)))
        uu___1 uu___
let (k_elab_trans :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Typing_Env.env ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit, unit) continuation_elaborator ->
                (unit, unit, unit, unit) continuation_elaborator ->
                  (unit, unit, unit, unit) continuation_elaborator)
  =
  fun g0 ->
    fun g1 ->
      fun g2 ->
        fun ctxt0 ->
          fun ctxt1 ->
            fun ctxt2 ->
              fun k0 ->
                fun k1 ->
                  fun post_hint ->
                    fun res ->
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                                 (Prims.of_int (26)) (Prims.of_int (39))
                                 (Prims.of_int (26)) (Prims.of_int (57)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                                 (Prims.of_int (26)) (Prims.of_int (26))
                                 (Prims.of_int (26)) (Prims.of_int (57)))))
                        (Obj.magic (k1 post_hint res))
                        (fun uu___ ->
                           (fun uu___ -> Obj.magic (k0 post_hint uu___))
                             uu___)
let (comp_st_with_post :
  Pulse_Syntax_Base.comp_st ->
    Pulse_Syntax_Base.term -> Pulse_Syntax_Base.comp_st)
  =
  fun c ->
    fun post ->
      match c with
      | Pulse_Syntax_Base.C_ST st ->
          Pulse_Syntax_Base.C_ST
            {
              Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
              Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
              Pulse_Syntax_Base.pre = (st.Pulse_Syntax_Base.pre);
              Pulse_Syntax_Base.post = post
            }
      | Pulse_Syntax_Base.C_STGhost (i, st) ->
          Pulse_Syntax_Base.C_STGhost
            (i,
              {
                Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
                Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
                Pulse_Syntax_Base.pre = (st.Pulse_Syntax_Base.pre);
                Pulse_Syntax_Base.post = post
              })
      | Pulse_Syntax_Base.C_STAtomic (i, st) ->
          Pulse_Syntax_Base.C_STAtomic
            (i,
              {
                Pulse_Syntax_Base.u = (st.Pulse_Syntax_Base.u);
                Pulse_Syntax_Base.res = (st.Pulse_Syntax_Base.res);
                Pulse_Syntax_Base.pre = (st.Pulse_Syntax_Base.pre);
                Pulse_Syntax_Base.post = post
              })
let (st_equiv_post :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.term ->
            unit -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun t ->
      fun c ->
        fun d ->
          fun post ->
            fun veq ->
              let c' = comp_st_with_post c post in
              let uu___ =
                Pulse_Typing_Metatheory.st_comp_typing_inversion g
                  (Pulse_Syntax_Base.st_comp_of_comp c)
                  (Pulse_Typing_Metatheory.comp_typing_inversion g c
                     (Pulse_Typing_Metatheory.st_typing_correctness g t c d)) in
              match uu___ with
              | FStar_Pervasives.Mkdtuple4 (u_of, pre_typing, x, post_typing)
                  ->
                  let st_equiv =
                    Pulse_Typing.ST_VPropEquiv
                      (g, c, c', x, (), (), (), (), ()) in
                  Pulse_Typing.T_Equiv (g, t, c, c', d, st_equiv)
let (simplify_post :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.comp_st ->
        (unit, unit, unit) Pulse_Typing.st_typing ->
          Pulse_Syntax_Base.term -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun t -> fun c -> fun d -> fun post -> st_equiv_post g t c d post ()
let (k_elab_equiv_continutation :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            (unit, unit, unit, unit) continuation_elaborator ->
              unit -> (unit, unit, unit, unit) continuation_elaborator)
  =
  fun g1 ->
    fun g2 ->
      fun ctxt ->
        fun ctxt1 ->
          fun ctxt2 ->
            fun k ->
              fun d ->
                fun post_hint ->
                  fun res ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                               (Prims.of_int (74)) (Prims.of_int (60))
                               (Prims.of_int (77)) (Prims.of_int (33)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                               (Prims.of_int (78)) (Prims.of_int (4))
                               (Prims.of_int (88)) (Prims.of_int (34)))))
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ ->
                            FStar_Pervasives.Mkdtuple3
                              (Pulse_Syntax_Base.tm_emp, (), ())))
                      (fun uu___ ->
                         (fun framing_token ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Prover.Common.fst"
                                          (Prims.of_int (79))
                                          (Prims.of_int (26))
                                          (Prims.of_int (79))
                                          (Prims.of_int (29)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Prover.Common.fst"
                                          (Prims.of_int (78))
                                          (Prims.of_int (4))
                                          (Prims.of_int (88))
                                          (Prims.of_int (34)))))
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___ -> res))
                                 (fun uu___ ->
                                    (fun uu___ ->
                                       match uu___ with
                                       | FStar_Pervasives.Mkdtuple3
                                           (st, c, st_d) ->
                                           if
                                             Prims.op_Negation
                                               (Pulse_Syntax_Base.stateful_comp
                                                  c)
                                           then
                                             Obj.magic
                                               (k post_hint
                                                  (FStar_Pervasives.Mkdtuple3
                                                     (st, c, st_d)))
                                           else
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Prover.Common.fst"
                                                           (Prims.of_int (83))
                                                           (Prims.of_int (18))
                                                           (Prims.of_int (83))
                                                           (Prims.of_int (95)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Prover.Common.fst"
                                                           (Prims.of_int (81))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (88))
                                                           (Prims.of_int (34)))))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                          g2
                                                          (Pulse_Syntax_Base.st_comp_of_comp
                                                             c)
                                                          (Pulse_Typing_Metatheory.comp_typing_inversion
                                                             g2 c
                                                             (Pulse_Typing_Metatheory.st_typing_correctness
                                                                g2 st c st_d))))
                                                  (fun uu___2 ->
                                                     (fun uu___2 ->
                                                        match uu___2 with
                                                        | FStar_Pervasives.Mkdtuple4
                                                            (uu___3,
                                                             pre_typing,
                                                             uu___4, uu___5)
                                                            ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (95)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (34)))))
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___6 ->
                                                                    Pulse_Checker_Framing.apply_frame
                                                                    g2 st
                                                                    ctxt1 ()
                                                                    c st_d
                                                                    framing_token))
                                                                 (fun uu___6
                                                                    ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    Prims.Mkdtuple2
                                                                    (c',
                                                                    st_d') ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    simplify_post
                                                                    g2 st c'
                                                                    st_d'
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    st_d'1 ->
                                                                    Obj.magic
                                                                    (k
                                                                    post_hint
                                                                    (FStar_Pervasives.Mkdtuple3
                                                                    (st,
                                                                    (comp_st_with_post
                                                                    c'
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c)),
                                                                    st_d'1))))
                                                                    uu___7)))
                                                                    uu___6)))
                                                       uu___2))) uu___)))
                           uu___)
let (k_elab_equiv_prefix :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            (unit, unit, unit, unit) continuation_elaborator ->
              unit -> (unit, unit, unit, unit) continuation_elaborator)
  =
  fun g1 ->
    fun g2 ->
      fun ctxt1 ->
        fun ctxt2 ->
          fun ctxt ->
            fun k ->
              fun d ->
                fun post_hint ->
                  fun res ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                               (Prims.of_int (97)) (Prims.of_int (60))
                               (Prims.of_int (99)) (Prims.of_int (31)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                               (Prims.of_int (100)) (Prims.of_int (4))
                               (Prims.of_int (115)) (Prims.of_int (11)))))
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ ->
                            FStar_Pervasives.Mkdtuple3
                              (Pulse_Syntax_Base.tm_emp, (), ())))
                      (fun uu___ ->
                         (fun framing_token ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Prover.Common.fst"
                                          (Prims.of_int (101))
                                          (Prims.of_int (12))
                                          (Prims.of_int (101))
                                          (Prims.of_int (27)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Prover.Common.fst"
                                          (Prims.of_int (101))
                                          (Prims.of_int (30))
                                          (Prims.of_int (115))
                                          (Prims.of_int (11)))))
                                 (Obj.magic (k post_hint res))
                                 (fun res1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___ ->
                                         match res1 with
                                         | FStar_Pervasives.Mkdtuple3
                                             (st, c, st_d) ->
                                             if
                                               Prims.op_Negation
                                                 (Pulse_Syntax_Base.stateful_comp
                                                    c)
                                             then
                                               FStar_Pervasives.Mkdtuple3
                                                 (st, c, st_d)
                                             else
                                               (match Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                        g1
                                                        (Pulse_Syntax_Base.st_comp_of_comp
                                                           c)
                                                        (Pulse_Typing_Metatheory.comp_typing_inversion
                                                           g1 c
                                                           (Pulse_Typing_Metatheory.st_typing_correctness
                                                              g1 st c st_d))
                                                with
                                                | FStar_Pervasives.Mkdtuple4
                                                    (uu___2, pre_typing,
                                                     uu___3, uu___4)
                                                    ->
                                                    (match Pulse_Checker_Framing.apply_frame
                                                             g1 st ctxt2 () c
                                                             st_d
                                                             framing_token
                                                     with
                                                     | Prims.Mkdtuple2
                                                         (c', st_d') ->
                                                         FStar_Pervasives.Mkdtuple3
                                                           (st,
                                                             (comp_st_with_post
                                                                c'
                                                                (Pulse_Syntax_Base.comp_post
                                                                   c)),
                                                             (simplify_post
                                                                g1 st c'
                                                                st_d'
                                                                (Pulse_Syntax_Base.comp_post
                                                                   c)))))))))
                           uu___)
let (k_elab_equiv :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit, unit) continuation_elaborator ->
                unit ->
                  unit -> (unit, unit, unit, unit) continuation_elaborator)
  =
  fun g1 ->
    fun g2 ->
      fun ctxt1 ->
        fun ctxt1' ->
          fun ctxt2 ->
            fun ctxt2' ->
              fun k ->
                fun d1 ->
                  fun d2 ->
                    let k1 =
                      k_elab_equiv_continutation g1 g2 ctxt1 ctxt2 ctxt2' k
                        () in
                    let k2 =
                      k_elab_equiv_prefix g1 g2 ctxt1 ctxt1' ctxt2' k1 () in
                    k2
let rec (list_as_vprop' :
  Pulse_Syntax_Base.vprop ->
    Pulse_Syntax_Base.vprop Prims.list -> Pulse_Syntax_Base.vprop)
  =
  fun vp ->
    fun fvps ->
      match fvps with
      | [] -> vp
      | hd::tl -> list_as_vprop' (Pulse_Syntax_Base.tm_star vp hd) tl
let rec (canon_right_aux :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop Prims.list ->
      (Pulse_Syntax_Base.vprop ->
         (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
        ->
        ((Pulse_Syntax_Base.vprop Prims.list,
           Pulse_Syntax_Base.vprop Prims.list, unit) FStar_Pervasives.dtuple3,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun vps ->
             fun f ->
               match vps with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ ->
                              FStar_Pervasives.Mkdtuple3 ([], [], ()))))
               | hd::rest ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Prover.Common.fst"
                                    (Prims.of_int (144)) (Prims.of_int (7))
                                    (Prims.of_int (144)) (Prims.of_int (11)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Prover.Common.fst"
                                    (Prims.of_int (144)) (Prims.of_int (4))
                                    (Prims.of_int (168)) (Prims.of_int (7)))))
                           (Obj.magic (f hd))
                           (fun uu___ ->
                              (fun uu___ ->
                                 if uu___
                                 then
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Prover.Common.fst"
                                                 (Prims.of_int (146))
                                                 (Prims.of_int (32))
                                                 (Prims.of_int (146))
                                                 (Prims.of_int (56)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Prover.Common.fst"
                                                 (Prims.of_int (145))
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (162))
                                                 (Prims.of_int (34)))))
                                        (Obj.magic (canon_right_aux g rest f))
                                        (fun uu___1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 ->
                                                match uu___1 with
                                                | FStar_Pervasives.Mkdtuple3
                                                    (vps', fvps, uu___3) ->
                                                    FStar_Pervasives.Mkdtuple3
                                                      (vps', (hd :: fvps),
                                                        ()))))
                                 else
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Prover.Common.fst"
                                                 (Prims.of_int (165))
                                                 (Prims.of_int (33))
                                                 (Prims.of_int (165))
                                                 (Prims.of_int (57)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Prover.Common.fst"
                                                 (Prims.of_int (164))
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (167))
                                                 (Prims.of_int (33)))))
                                        (Obj.magic (canon_right_aux g rest f))
                                        (fun uu___2 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                match uu___2 with
                                                | FStar_Pervasives.Mkdtuple3
                                                    (vps', pures, uu___4) ->
                                                    FStar_Pervasives.Mkdtuple3
                                                      ((hd :: vps'), pures,
                                                        ()))))) uu___))))
          uu___2 uu___1 uu___
let (canon_right :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        unit ->
          (Pulse_Syntax_Base.vprop ->
             (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
            ->
            ((Pulse_Syntax_Base.term, unit,
               (unit, unit, unit, unit) continuation_elaborator)
               FStar_Pervasives.dtuple3,
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun frame ->
        fun ctxt_frame_typing ->
          fun f ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                       (Prims.of_int (179)) (Prims.of_int (33))
                       (Prims.of_int (179)) (Prims.of_int (73)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                       (Prims.of_int (179)) (Prims.of_int (3))
                       (Prims.of_int (184)) (Prims.of_int (110)))))
              (Obj.magic
                 (canon_right_aux g
                    (Pulse_Checker_VPropEquiv.vprop_as_list ctxt) f))
              (fun uu___ ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      match uu___ with
                      | FStar_Pervasives.Mkdtuple3 (vps', pures, veq) ->
                          FStar_Pervasives.Mkdtuple3
                            ((list_as_vprop'
                                (Pulse_Checker_VPropEquiv.list_as_vprop vps')
                                pures), (),
                              (k_elab_equiv g g
                                 (Pulse_Syntax_Base.tm_star ctxt frame)
                                 (Pulse_Syntax_Base.tm_star ctxt frame)
                                 (Pulse_Syntax_Base.tm_star ctxt frame)
                                 (Pulse_Syntax_Base.tm_star
                                    (list_as_vprop'
                                       (Pulse_Checker_VPropEquiv.list_as_vprop
                                          vps') pures) frame)
                                 (k_elab_unit g
                                    (Pulse_Syntax_Base.tm_star ctxt frame))
                                 () ()))))
let (continuation_elaborator_with_bind :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.comp ->
        Pulse_Syntax_Base.st_term ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            unit ->
              ((Pulse_Syntax_Base.var,
                 (unit, unit, unit, unit) continuation_elaborator)
                 Prims.dtuple2,
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
                   fun c1 ->
                     fun e1 ->
                       fun e1_typing ->
                         fun ctxt_pre1_typing ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ ->
                                   match Pulse_Checker_Framing.apply_frame g
                                           e1
                                           (Pulse_Syntax_Base.tm_star ctxt
                                              (Pulse_Syntax_Base.comp_pre c1))
                                           () c1 e1_typing
                                           (FStar_Pervasives.Mkdtuple3
                                              (ctxt, (), ()))
                                   with
                                   | Prims.Mkdtuple2 (c11, e1_typing1) ->
                                       (match Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                g
                                                (Pulse_Syntax_Base.st_comp_of_comp
                                                   c11)
                                                (Pulse_Typing_Metatheory.comp_typing_inversion
                                                   g c11
                                                   (Pulse_Typing_Metatheory.st_typing_correctness
                                                      g e1 c11 e1_typing1))
                                        with
                                        | FStar_Pervasives.Mkdtuple4
                                            (u_of_1, pre_typing, uu___1,
                                             uu___2)
                                            ->
                                            Prims.Mkdtuple2
                                              ((Pulse_Typing_Env.fresh g),
                                                ((fun post_hint ->
                                                    fun res ->
                                                      FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Prover.Common.fst"
                                                                 (Prims.of_int (217))
                                                                 (Prims.of_int (34))
                                                                 (Prims.of_int (217))
                                                                 (Prims.of_int (37)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Prover.Common.fst"
                                                                 (Prims.of_int (216))
                                                                 (Prims.of_int (24))
                                                                 (Prims.of_int (249))
                                                                 (Prims.of_int (5)))))
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___3 -> res))
                                                        (fun uu___3 ->
                                                           (fun uu___3 ->
                                                              match uu___3
                                                              with
                                                              | FStar_Pervasives.Mkdtuple3
                                                                  (e2, c2,
                                                                   e2_typing)
                                                                  ->
                                                                  if
                                                                    Prims.op_Negation
                                                                    (Pulse_Syntax_Base.stateful_comp
                                                                    c2)
                                                                  then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V1_Derived.fail
                                                                    "Unexpected non-stateful comp in continuation elaborate"))
                                                                  else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    e2_typing))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    e2_typing1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Pulse_Syntax_Naming.close_st_term
                                                                    e2
                                                                    (Pulse_Typing_Env.fresh
                                                                    g)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    e2_closed
                                                                    ->
                                                                    if
                                                                    FStar_Set.mem
                                                                    (Pulse_Typing_Env.fresh
                                                                    g)
                                                                    (Pulse_Syntax_Naming.freevars
                                                                    (Pulse_Syntax_Base.comp_post
                                                                    c2))
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V1_Derived.fail
                                                                    "Impossible"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (Pulse_Typing_Combinators.bind_res_and_post_typing
                                                                    g
                                                                    (Pulse_Syntax_Base.st_comp_of_comp
                                                                    c2)
                                                                    (Pulse_Typing_Env.fresh
                                                                    g)
                                                                    post_hint))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (t_typing,
                                                                    post_typing)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    (Pulse_Typing_Combinators.mk_bind
                                                                    g
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt
                                                                    (Pulse_Syntax_Base.comp_pre
                                                                    c1)) e1
                                                                    e2_closed
                                                                    c11 c2
                                                                    (Pulse_Syntax_Base.v_as_nv
                                                                    (Pulse_Typing_Env.fresh
                                                                    g))
                                                                    e1_typing1
                                                                    ()
                                                                    e2_typing1
                                                                    () ()))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e, c,
                                                                    e_typing)
                                                                    ->
                                                                    FStar_Pervasives.Mkdtuple3
                                                                    (e, c,
                                                                    e_typing)))))
                                                                    uu___6))))
                                                                    uu___5)))
                                                                    uu___5))))
                                                             uu___3))))))))
                uu___5 uu___4 uu___3 uu___2 uu___1 uu___
type mk_t =
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        ((Pulse_Syntax_Base.ppname, Pulse_Syntax_Base.st_term,
           Pulse_Syntax_Base.comp, (unit, unit, unit) Pulse_Typing.st_typing)
           FStar_Pervasives.dtuple4 FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr
let (elim_one :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.vprop ->
        Pulse_Syntax_Base.vprop ->
          unit ->
            Pulse_Syntax_Base.ppname ->
              Pulse_Syntax_Base.st_term ->
                Pulse_Syntax_Base.comp ->
                  (unit, unit, unit) Pulse_Typing.st_typing ->
                    ((Pulse_Typing_Env.env, Pulse_Syntax_Base.term, unit,
                       (unit, unit, unit, unit) continuation_elaborator)
                       FStar_Pervasives.dtuple4,
                      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun frame ->
        fun p ->
          fun ctxt_frame_p_typing ->
            fun nx ->
              fun e1 ->
                fun c1 ->
                  fun e1_typing ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                               (Prims.of_int (265)) (Prims.of_int (26))
                               (Prims.of_int (265)) (Prims.of_int (69)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                               (Prims.of_int (265)) (Prims.of_int (72))
                               (Prims.of_int (287)) (Prims.of_int (40)))))
                      (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ()))
                      (fun uu___ ->
                         (fun ctxt_frame_typing ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Prover.Common.fst"
                                          (Prims.of_int (267))
                                          (Prims.of_int (4))
                                          (Prims.of_int (267))
                                          (Prims.of_int (88)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Prover.Common.fst"
                                          (Prims.of_int (265))
                                          (Prims.of_int (72))
                                          (Prims.of_int (287))
                                          (Prims.of_int (40)))))
                                 (Obj.magic
                                    (continuation_elaborator_with_bind g
                                       (Pulse_Syntax_Base.tm_star ctxt frame)
                                       c1 e1 e1_typing ()))
                                 (fun uu___ ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___1 ->
                                         match uu___ with
                                         | Prims.Mkdtuple2 (x, k) ->
                                             FStar_Pervasives.Mkdtuple4
                                               ((Pulse_Typing_Env.push_binding
                                                   g x nx
                                                   (Pulse_Syntax_Base.comp_res
                                                      c1)),
                                                 (Pulse_Syntax_Base.tm_star
                                                    (Pulse_Syntax_Naming.open_term_nv
                                                       (Pulse_Syntax_Base.comp_post
                                                          c1)
                                                       (Pulse_Syntax_Base.v_as_nv
                                                          x)) ctxt), (),
                                                 (k_elab_equiv g
                                                    (Pulse_Typing_Env.push_binding
                                                       g x nx
                                                       (Pulse_Syntax_Base.comp_res
                                                          c1))
                                                    (Pulse_Syntax_Base.tm_star
                                                       (Pulse_Syntax_Base.tm_star
                                                          ctxt frame) p)
                                                    (Pulse_Syntax_Base.tm_star
                                                       (Pulse_Syntax_Base.tm_star
                                                          ctxt frame) p)
                                                    (Pulse_Syntax_Base.tm_star
                                                       (Pulse_Syntax_Naming.open_term_nv
                                                          (Pulse_Syntax_Base.comp_post
                                                             c1)
                                                          (Pulse_Syntax_Base.v_as_nv
                                                             x))
                                                       (Pulse_Syntax_Base.tm_star
                                                          ctxt frame))
                                                    (Pulse_Syntax_Base.tm_star
                                                       (Pulse_Syntax_Base.tm_star
                                                          (Pulse_Syntax_Naming.open_term_nv
                                                             (Pulse_Syntax_Base.comp_post
                                                                c1)
                                                             (Pulse_Syntax_Base.v_as_nv
                                                                x)) ctxt)
                                                       frame) k () ()))))))
                           uu___)
let rec (elim_all :
  Pulse_Typing_Env.env ->
    (Pulse_Syntax_Base.vprop ->
       (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
      ->
      mk_t ->
        Pulse_Syntax_Base.term ->
          Pulse_Syntax_Base.term ->
            unit ->
              ((Prims.bool * (Pulse_Typing_Env.env, Pulse_Syntax_Base.term,
                 unit, (unit, unit, unit, unit) continuation_elaborator)
                 FStar_Pervasives.dtuple4),
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun g ->
                 fun f ->
                   fun mk ->
                     fun ctxt ->
                       fun frame ->
                         fun ctxt_frame_typing ->
                           match ctxt.Pulse_Syntax_Base.t with
                           | Pulse_Syntax_Base.Tm_Star (ctxt', p) ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Prover.Common.fst"
                                                (Prims.of_int (301))
                                                (Prims.of_int (9))
                                                (Prims.of_int (301))
                                                (Prims.of_int (89)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Prover.Common.fst"
                                                (Prims.of_int (302))
                                                (Prims.of_int (7))
                                                (Prims.of_int (322))
                                                (Prims.of_int (10)))))
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___ -> ()))
                                       (fun uu___ ->
                                          (fun p_typing ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Prover.Common.fst"
                                                           (Prims.of_int (302))
                                                           (Prims.of_int (10))
                                                           (Prims.of_int (302))
                                                           (Prims.of_int (13)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Prover.Common.fst"
                                                           (Prims.of_int (302))
                                                           (Prims.of_int (7))
                                                           (Prims.of_int (322))
                                                           (Prims.of_int (10)))))
                                                  (Obj.magic (f p))
                                                  (fun uu___ ->
                                                     (fun uu___ ->
                                                        if uu___
                                                        then
                                                          Obj.magic
                                                            (Obj.repr
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (35)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (70)))))
                                                                  (Obj.magic
                                                                    (mk g p
                                                                    ()))
                                                                  (fun uu___1
                                                                    ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives.Mkdtuple4
                                                                    (nx, e1,
                                                                    c1,
                                                                    e1_typing))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (elim_one
                                                                    g ctxt'
                                                                    frame p
                                                                    () nx e1
                                                                    c1
                                                                    e1_typing))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (g',
                                                                    uu___3,
                                                                    ctxt_typing',
                                                                    k) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    k))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun k1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    k_elab_equiv
                                                                    g g'
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt'
                                                                    frame) p)
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt' p)
                                                                    frame)
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    uu___3
                                                                    frame)
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    uu___3
                                                                    frame) k1
                                                                    () ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun k2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Prover.Common.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    (elim_all
                                                                    g' f mk
                                                                    uu___3
                                                                    frame ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (uu___6,
                                                                    FStar_Pervasives.Mkdtuple4
                                                                    (g'',
                                                                    ctxt'',
                                                                    ctxt_typing'',
                                                                    k')) ->
                                                                    (true,
                                                                    (FStar_Pervasives.Mkdtuple4
                                                                    (g'',
                                                                    ctxt'',
                                                                    (),
                                                                    (k_elab_trans
                                                                    g g' g''
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt' p)
                                                                    frame)
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    uu___3
                                                                    frame)
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt''
                                                                    frame) k2
                                                                    k'))))))))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___2)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    (false,
                                                                    (FStar_Pervasives.Mkdtuple4
                                                                    (g, ctxt,
                                                                    (),
                                                                    (k_elab_unit
                                                                    g
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt
                                                                    frame)))))))))
                                                                    uu___1)))
                                                        else
                                                          Obj.magic
                                                            (Obj.repr
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___2
                                                                    ->
                                                                    (false,
                                                                    (FStar_Pervasives.Mkdtuple4
                                                                    (g, ctxt,
                                                                    (),
                                                                    (k_elab_unit
                                                                    g
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt
                                                                    frame)))))))))
                                                       uu___))) uu___)))
                           | uu___ ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___1 ->
                                          (false,
                                            (FStar_Pervasives.Mkdtuple4
                                               (g, ctxt, (),
                                                 (k_elab_unit g
                                                    (Pulse_Syntax_Base.tm_star
                                                       ctxt frame)))))))))
                uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (add_elims_aux :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (Pulse_Syntax_Base.vprop ->
           (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
          ->
          mk_t ->
            unit ->
              ((Prims.bool * (Pulse_Typing_Env.env, Pulse_Syntax_Base.term,
                 unit, (unit, unit, unit, unit) continuation_elaborator)
                 FStar_Pervasives.dtuple4),
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun frame ->
        fun f ->
          fun mk ->
            fun ctxt_frame_typing ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                         (Prims.of_int (335)) (Prims.of_int (40))
                         (Prims.of_int (335)) (Prims.of_int (71)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                         (Prims.of_int (335)) (Prims.of_int (4))
                         (Prims.of_int (338)) (Prims.of_int (66)))))
                (Obj.magic (canon_right g ctxt frame () f))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | FStar_Pervasives.Mkdtuple3 (ctxt', ctxt'_typing, k)
                          ->
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Prover.Common.fst"
                                        (Prims.of_int (337))
                                        (Prims.of_int (9))
                                        (Prims.of_int (337))
                                        (Prims.of_int (35)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Prover.Common.fst"
                                        (Prims.of_int (335))
                                        (Prims.of_int (74))
                                        (Prims.of_int (338))
                                        (Prims.of_int (66)))))
                               (Obj.magic (elim_all g f mk ctxt' frame ()))
                               (fun uu___1 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       match uu___1 with
                                       | (progress,
                                          FStar_Pervasives.Mkdtuple4
                                          (g', ctxt'', ctxt''_typing, k')) ->
                                           (progress,
                                             (FStar_Pervasives.Mkdtuple4
                                                (g', ctxt'', (),
                                                  (k_elab_trans g g g'
                                                     (Pulse_Syntax_Base.tm_star
                                                        ctxt frame)
                                                     (Pulse_Syntax_Base.tm_star
                                                        ctxt' frame)
                                                     (Pulse_Syntax_Base.tm_star
                                                        ctxt'' frame) k k'))))))))
                     uu___)
let rec (add_elims :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (Pulse_Syntax_Base.vprop ->
           (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
          ->
          mk_t ->
            unit ->
              ((Pulse_Typing_Env.env, Pulse_Syntax_Base.term, unit,
                 (unit, unit, unit, unit) continuation_elaborator)
                 FStar_Pervasives.dtuple4,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun frame ->
        fun f ->
          fun mk ->
            fun ctxt_typing ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                         (Prims.of_int (348)) (Prims.of_int (25))
                         (Prims.of_int (348)) (Prims.of_int (55)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.Common.fst"
                         (Prims.of_int (348)) (Prims.of_int (4))
                         (Prims.of_int (355)) (Prims.of_int (6)))))
                (Obj.magic (add_elims_aux g ctxt frame f mk ()))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | (progress, res) ->
                          if Prims.op_Negation progress
                          then
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 -> res)))
                          else
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Prover.Common.fst"
                                             (Prims.of_int (352))
                                             (Prims.of_int (45))
                                             (Prims.of_int (352))
                                             (Prims.of_int (48)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Pulse.Prover.Common.fst"
                                             (Prims.of_int (351))
                                             (Prims.of_int (10))
                                             (Prims.of_int (355))
                                             (Prims.of_int (6)))))
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 -> res))
                                    (fun uu___2 ->
                                       (fun uu___2 ->
                                          match uu___2 with
                                          | FStar_Pervasives.Mkdtuple4
                                              (g', ctxt', ctxt'_typing, k) ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Prover.Common.fst"
                                                            (Prims.of_int (353))
                                                            (Prims.of_int (49))
                                                            (Prims.of_int (353))
                                                            (Prims.of_int (76)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Pulse.Prover.Common.fst"
                                                            (Prims.of_int (352))
                                                            (Prims.of_int (51))
                                                            (Prims.of_int (354))
                                                            (Prims.of_int (57)))))
                                                   (Obj.magic
                                                      (add_elims g' ctxt'
                                                         frame f mk ()))
                                                   (fun uu___3 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___4 ->
                                                           match uu___3 with
                                                           | FStar_Pervasives.Mkdtuple4
                                                               (g'', ctxt'',
                                                                ctxt''_typing,
                                                                k')
                                                               ->
                                                               FStar_Pervasives.Mkdtuple4
                                                                 (g'',
                                                                   ctxt'',
                                                                   (),
                                                                   (k_elab_trans
                                                                    g g' g''
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt
                                                                    frame)
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt'
                                                                    frame)
                                                                    (Pulse_Syntax_Base.tm_star
                                                                    ctxt''
                                                                    frame) k
                                                                    k'))))))
                                         uu___2)))) uu___)
type preamble =
  {
  g0: Pulse_Typing_Env.env ;
  ctxt: Pulse_Syntax_Base.vprop ;
  frame: Pulse_Syntax_Base.vprop ;
  ctxt_frame_typing: unit ;
  goals: Pulse_Syntax_Base.vprop }
let (__proj__Mkpreamble__item__g0 : preamble -> Pulse_Typing_Env.env) =
  fun projectee ->
    match projectee with
    | { g0; ctxt; frame; ctxt_frame_typing; goals;_} -> g0
let (__proj__Mkpreamble__item__ctxt : preamble -> Pulse_Syntax_Base.vprop) =
  fun projectee ->
    match projectee with
    | { g0; ctxt; frame; ctxt_frame_typing; goals;_} -> ctxt
let (__proj__Mkpreamble__item__frame : preamble -> Pulse_Syntax_Base.vprop) =
  fun projectee ->
    match projectee with
    | { g0; ctxt; frame; ctxt_frame_typing; goals;_} -> frame

let (__proj__Mkpreamble__item__goals : preamble -> Pulse_Syntax_Base.vprop) =
  fun projectee ->
    match projectee with
    | { g0; ctxt; frame; ctxt_frame_typing; goals;_} -> goals
let (op_Array_Access :
  Pulse_Prover_Substs.t -> Pulse_Syntax_Base.term -> Pulse_Syntax_Base.term)
  = fun ss -> fun t -> Pulse_Prover_Substs.subst_term t ss
let (op_Star :
  Pulse_Syntax_Base.vprop ->
    Pulse_Syntax_Base.vprop -> Pulse_Syntax_Base.term)
  = Pulse_Syntax_Base.tm_star
type ('ss, 'uvs, 'g) well_typed_ss = unit
type 'preamble1 prover_state =
  {
  pg: Pulse_Typing_Env.env ;
  remaining_ctxt: Pulse_Syntax_Base.vprop Prims.list ;
  remaining_ctxt_frame_typing: unit ;
  uvs: Pulse_Typing_Env.env ;
  ss: Pulse_Prover_Substs.t ;
  solved: Pulse_Syntax_Base.vprop ;
  unsolved: Pulse_Syntax_Base.vprop Prims.list ;
  solved_typing: unit ;
  k: (unit, unit, unit, unit) continuation_elaborator ;
  goals_inv: unit }
let (__proj__Mkprover_state__item__pg :
  preamble -> unit prover_state -> Pulse_Typing_Env.env) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; solved;
          unsolved; solved_typing; k; goals_inv;_} -> pg
let (__proj__Mkprover_state__item__remaining_ctxt :
  preamble -> unit prover_state -> Pulse_Syntax_Base.vprop Prims.list) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; solved;
          unsolved; solved_typing; k; goals_inv;_} -> remaining_ctxt

let (__proj__Mkprover_state__item__uvs :
  preamble -> unit prover_state -> Pulse_Typing_Env.env) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; solved;
          unsolved; solved_typing; k; goals_inv;_} -> uvs
let (__proj__Mkprover_state__item__ss :
  preamble -> unit prover_state -> Pulse_Prover_Substs.t) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; solved;
          unsolved; solved_typing; k; goals_inv;_} -> ss
let (__proj__Mkprover_state__item__solved :
  preamble -> unit prover_state -> Pulse_Syntax_Base.vprop) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; solved;
          unsolved; solved_typing; k; goals_inv;_} -> solved
let (__proj__Mkprover_state__item__unsolved :
  preamble -> unit prover_state -> Pulse_Syntax_Base.vprop Prims.list) =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; solved;
          unsolved; solved_typing; k; goals_inv;_} -> unsolved

let (__proj__Mkprover_state__item__k :
  preamble ->
    unit prover_state -> (unit, unit, unit, unit) continuation_elaborator)
  =
  fun preamble1 ->
    fun projectee ->
      match projectee with
      | { pg; remaining_ctxt; remaining_ctxt_frame_typing; uvs; ss; solved;
          unsolved; solved_typing; k; goals_inv;_} -> k
type ('preamble1, 'st) is_terminal = unit
let (extend_post_hint_opt_g :
  Pulse_Typing_Env.env ->
    unit Pulse_Typing.post_hint_opt ->
      Pulse_Typing_Env.env -> unit Pulse_Typing.post_hint_opt)
  =
  fun g ->
    fun post_hint ->
      fun g1 ->
        match post_hint with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some post_hint1 ->
            FStar_Pervasives_Native.Some post_hint1
let (st_typing_subst :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.comp_st ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            Pulse_Prover_Substs.t ->
              ((unit, unit, unit) Pulse_Typing.st_typing
                 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun uvs ->
      fun t ->
        fun c ->
          fun d ->
            fun ss ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.Common.fsti"
                         (Prims.of_int (140)) (Prims.of_int (10))
                         (Prims.of_int (140)) (Prims.of_int (42)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Prover.Common.fsti"
                         (Prims.of_int (141)) (Prims.of_int (2))
                         (Prims.of_int (146)) (Prims.of_int (13)))))
                (Obj.magic
                   (Pulse_Prover_Substs.check_well_typedness g uvs ss))
                (fun b ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        if Prims.op_Negation b
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            (Pulse_Prover_Substs.st_typing_nt_substs g uvs
                               (Pulse_Typing_Env.mk_env
                                  (Pulse_Typing_Env.fstar_env g)) t c d
                               (Pulse_Prover_Substs.as_nt_substs ss))))
let (st_typing_weakening :
  Pulse_Typing_Env.env ->
    Pulse_Typing_Env.env ->
      Pulse_Syntax_Base.st_term ->
        Pulse_Syntax_Base.comp_st ->
          (unit, unit, unit) Pulse_Typing.st_typing ->
            Pulse_Typing_Env.env -> (unit, unit, unit) Pulse_Typing.st_typing)
  =
  fun g ->
    fun g' ->
      fun t ->
        fun c ->
          fun d ->
            fun g1 ->
              let g2 = Pulse_Typing_Env.diff g1 g in
              let d1 =
                Pulse_Typing_Metatheory.st_typing_weakening g g' t c d g2 in
              d1
type ('ss1, 'ss2) ss_extends = unit
type ('preamble1, 'pst1, 'pst2) pst_extends = unit
type prover_t =
  preamble ->
    unit prover_state ->
      (unit prover_state, unit) FStar_Tactics_Effect.tac_repr
let (prove :
  Pulse_Typing_Env.env ->
    Pulse_Syntax_Base.vprop ->
      unit ->
        Pulse_Typing_Env.env ->
          Pulse_Syntax_Base.vprop ->
            unit ->
              ((Pulse_Typing_Env.env, Pulse_Prover_Substs.t,
                 Pulse_Syntax_Base.vprop,
                 (unit, unit, unit, unit) continuation_elaborator)
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
                                (fun uu___ -> Prims.admit ()))) uu___5 uu___4
                uu___3 uu___2 uu___1 uu___