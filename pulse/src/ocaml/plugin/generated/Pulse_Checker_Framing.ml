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
let (print_vprop_l :
  Pulse_Syntax_Base.term Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun vps ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "Pulse.Checker.Framing.fst" (Prims.of_int (20))
         (Prims.of_int (4)) (Prims.of_int (20)) (Prims.of_int (55)))
      (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
         (Prims.of_int (19)) (Prims.of_int (590)) (Prims.of_int (31)))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
               (Prims.of_int (20)) (Prims.of_int (26)) (Prims.of_int (20))
               (Prims.of_int (54)))
            (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
               (Prims.of_int (20)) (Prims.of_int (4)) (Prims.of_int (20))
               (Prims.of_int (55)))
            (Obj.magic
               (FStar_Tactics_Util.map Pulse_Syntax_Printer.term_to_string
                  vps))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 -> FStar_String.concat ";\n " uu___))))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> Prims.strcat "[" (Prims.strcat uu___ "]")))
let (print_framing_failure :
  framing_failure -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun ff ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "Pulse.Checker.Framing.fst" (Prims.of_int (25))
         (Prims.of_int (4)) (Prims.of_int (25)) (Prims.of_int (40)))
      (FStar_Range.mk_range "Pulse.Checker.Framing.fst" (Prims.of_int (23))
         (Prims.of_int (2)) (Prims.of_int (25)) (Prims.of_int (40)))
      (Obj.magic (print_vprop_l ff.remaining_context))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                    (Prims.of_int (23)) (Prims.of_int (2))
                    (Prims.of_int (25)) (Prims.of_int (40)))
                 (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                    (Prims.of_int (23)) (Prims.of_int (2))
                    (Prims.of_int (25)) (Prims.of_int (40)))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                          (Prims.of_int (24)) (Prims.of_int (4))
                          (Prims.of_int (24)) (Prims.of_int (46)))
                       (FStar_Range.mk_range "FStar.Printf.fst"
                          (Prims.of_int (121)) (Prims.of_int (8))
                          (Prims.of_int (123)) (Prims.of_int (44)))
                       (Obj.magic (print_vprop_l ff.unmatched_preconditions))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               fun x ->
                                 Prims.strcat
                                   (Prims.strcat
                                      " { unmatched_preconditions = "
                                      (Prims.strcat uu___1
                                         ";\n remaining_context = "))
                                   (Prims.strcat x "\n}")))))
                 (fun uu___1 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___2 -> uu___1 uu___)))) uu___)
type ('g, 'p, 'q) match_result =
  {
  matched: Pulse_Syntax_Base.vprop Prims.list ;
  unmatched_p: Pulse_Syntax_Base.vprop Prims.list ;
  unmatched_q: Pulse_Syntax_Base.vprop Prims.list ;
  p_eq: unit ;
  q_eq: unit }
let (__proj__Mkmatch_result__item__matched :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term Prims.list ->
      Pulse_Syntax_Base.term Prims.list ->
        (unit, unit, unit) match_result -> Pulse_Syntax_Base.vprop Prims.list)
  =
  fun g ->
    fun p ->
      fun q ->
        fun projectee ->
          match projectee with
          | { matched; unmatched_p; unmatched_q; p_eq; q_eq;_} -> matched
let (__proj__Mkmatch_result__item__unmatched_p :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term Prims.list ->
      Pulse_Syntax_Base.term Prims.list ->
        (unit, unit, unit) match_result -> Pulse_Syntax_Base.vprop Prims.list)
  =
  fun g ->
    fun p ->
      fun q ->
        fun projectee ->
          match projectee with
          | { matched; unmatched_p; unmatched_q; p_eq; q_eq;_} -> unmatched_p
let (__proj__Mkmatch_result__item__unmatched_q :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term Prims.list ->
      Pulse_Syntax_Base.term Prims.list ->
        (unit, unit, unit) match_result -> Pulse_Syntax_Base.vprop Prims.list)
  =
  fun g ->
    fun p ->
      fun q ->
        fun projectee ->
          match projectee with
          | { matched; unmatched_p; unmatched_q; p_eq; q_eq;_} -> unmatched_q
let (equational : Pulse_Syntax_Base.term -> Prims.bool) =
  fun t ->
    match t with
    | Pulse_Syntax_Base.Tm_FStar (host_term, uu___) ->
        (match FStar_Reflection_Builtins.inspect_ln host_term with
         | FStar_Reflection_Data.Tv_Match (uu___1, uu___2, uu___3) -> true
         | uu___1 -> false)
    | uu___ -> false
let (check_one_vprop :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (unit FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun p ->
             fun q ->
               if Pulse_Syntax_Base.eq_tm p q
               then
                 Obj.magic
                   (Obj.repr
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ -> FStar_Pervasives_Native.Some ())))
               else
                 Obj.magic
                   (Obj.repr
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                            (Prims.of_int (43)) (Prims.of_int (6))
                            (Prims.of_int (45)) (Prims.of_int (44)))
                         (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                            (Prims.of_int (47)) (Prims.of_int (4))
                            (Prims.of_int (54)) (Prims.of_int (13)))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               match ((Pulse_Syntax_Pure.is_pure_app p),
                                       (Pulse_Syntax_Pure.is_pure_app q))
                               with
                               | (FStar_Pervasives_Native.Some
                                  (hd_p, uu___2, uu___3),
                                  FStar_Pervasives_Native.Some
                                  (hd_q, uu___4, uu___5)) ->
                                   Pulse_Syntax_Base.eq_tm hd_p hd_q
                               | (uu___2, uu___3) ->
                                   (equational p) || (equational q)))
                         (fun uu___1 ->
                            (fun check_extensional_equality ->
                               if check_extensional_equality
                               then
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Framing.fst"
                                            (Prims.of_int (49))
                                            (Prims.of_int (15))
                                            (Prims.of_int (49))
                                            (Prims.of_int (26)))
                                         (FStar_Range.mk_range
                                            "Pulse.Checker.Framing.fst"
                                            (Prims.of_int (49))
                                            (Prims.of_int (29))
                                            (Prims.of_int (53))
                                            (Prims.of_int (23)))
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___1 ->
                                               Pulse_Elaborate_Pure.elab_term
                                                 p))
                                         (fun uu___1 ->
                                            (fun v0 ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Framing.fst"
                                                       (Prims.of_int (50))
                                                       (Prims.of_int (15))
                                                       (Prims.of_int (50))
                                                       (Prims.of_int (26)))
                                                    (FStar_Range.mk_range
                                                       "Pulse.Checker.Framing.fst"
                                                       (Prims.of_int (51))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (53))
                                                       (Prims.of_int (23)))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___1 ->
                                                          Pulse_Elaborate_Pure.elab_term
                                                            q))
                                                    (fun uu___1 ->
                                                       (fun v1 ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Framing.fst"
                                                                  (Prims.of_int (51))
                                                                  (Prims.of_int (12))
                                                                  (Prims.of_int (51))
                                                                  (Prims.of_int (44)))
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Checker.Framing.fst"
                                                                  (Prims.of_int (51))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (53))
                                                                  (Prims.of_int (23)))
                                                               (Obj.magic
                                                                  (FStar_Tactics_Builtins.check_equiv
                                                                    (Pulse_Typing.elab_env
                                                                    g) v0 v1))
                                                               (fun uu___1 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    token,
                                                                    uu___3)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ()
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    uu___3)
                                                                    ->
                                                                    FStar_Pervasives_Native.None))))
                                                         uu___1))) uu___1)))
                               else
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            FStar_Pervasives_Native.None))))
                              uu___1)))) uu___2 uu___1 uu___
type ('g, 'p, 'qs) split_one_vprop_res =
  (Pulse_Syntax_Base.term Prims.list, Pulse_Syntax_Base.term, unit,
    Pulse_Syntax_Base.term Prims.list) FStar_Pervasives.dtuple4
    FStar_Pervasives_Native.option
let rec (maybe_split_one_vprop :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term Prims.list ->
        ((unit, unit, unit) split_one_vprop_res, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun p ->
             fun qs ->
               match qs with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> FStar_Pervasives_Native.None)))
               | q::qs1 ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                              (Prims.of_int (69)) (Prims.of_int (18))
                              (Prims.of_int (69)) (Prims.of_int (39)))
                           (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                              (Prims.of_int (70)) (Prims.of_int (6))
                              (Prims.of_int (74)) (Prims.of_int (64)))
                           (Obj.magic (check_one_vprop g p q))
                           (fun uu___ ->
                              (fun d_opt ->
                                 if
                                   FStar_Pervasives_Native.uu___is_Some d_opt
                                 then
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___ ->
                                              FStar_Pervasives_Native.Some
                                                (FStar_Pervasives.Mkdtuple4
                                                   ([], q, (), qs1)))))
                                 else
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Framing.fst"
                                              (Prims.of_int (72))
                                              (Prims.of_int (17))
                                              (Prims.of_int (72))
                                              (Prims.of_int (45)))
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Framing.fst"
                                              (Prims.of_int (72))
                                              (Prims.of_int (11))
                                              (Prims.of_int (74))
                                              (Prims.of_int (64)))
                                           (Obj.magic
                                              (maybe_split_one_vprop g p qs1))
                                           (fun uu___1 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 ->
                                                   match uu___1 with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       FStar_Pervasives_Native.None
                                                   | FStar_Pervasives_Native.Some
                                                       (FStar_Pervasives.Mkdtuple4
                                                       (l, q', d, r)) ->
                                                       FStar_Pervasives_Native.Some
                                                         (FStar_Pervasives.Mkdtuple4
                                                            ((q :: l), q',
                                                              (), r)))))))
                                uu___)))) uu___2 uu___1 uu___
type ('g, 'req, 'ctxt) framing_success =
  (Pulse_Syntax_Base.term Prims.list, unit) Prims.dtuple2
type ('g, 'req, 'ctxt) try_frame_result =
  ((unit, unit, unit) framing_success, framing_failure)
    FStar_Pervasives.either
let (mk_framing_failure :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term Prims.list ->
      Pulse_Syntax_Base.term Prims.list ->
        Pulse_Syntax_Base.term Prims.list ->
          Pulse_Syntax_Base.term Prims.list ->
            Pulse_Syntax_Base.term ->
              (unit, unit, unit) try_frame_result ->
                (unit, unit, unit) try_frame_result)
  =
  fun g ->
    fun req ->
      fun req' ->
        fun ctxt ->
          fun ctxt' ->
            fun unmatched_pre ->
              fun res ->
                match res with
                | FStar_Pervasives.Inr failure ->
                    FStar_Pervasives.Inr
                      {
                        unmatched_preconditions = (unmatched_pre ::
                          (failure.unmatched_preconditions));
                        remaining_context = (failure.remaining_context)
                      }
                | FStar_Pervasives.Inl (Prims.Mkdtuple2 (frame, uu___)) ->
                    FStar_Pervasives.Inr
                      {
                        unmatched_preconditions = [unmatched_pre];
                        remaining_context = frame
                      }
let rec (try_split_vprop :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term Prims.list ->
      Pulse_Syntax_Base.term Prims.list ->
        (((Pulse_Syntax_Base.term Prims.list, unit) Prims.dtuple2,
           framing_failure) FStar_Pervasives.either,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun req ->
             fun ctxt ->
               match req with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ ->
                              FStar_Pervasives.Inl
                                (Prims.Mkdtuple2 (ctxt, ())))))
               | hd::tl ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                              (Prims.of_int (104)) (Prims.of_int (12))
                              (Prims.of_int (104)) (Prims.of_int (43)))
                           (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                              (Prims.of_int (104)) (Prims.of_int (6))
                              (Prims.of_int (128)) (Prims.of_int (30)))
                           (Obj.magic (maybe_split_one_vprop g hd ctxt))
                           (fun uu___ ->
                              (fun uu___ ->
                                 match uu___ with
                                 | FStar_Pervasives_Native.None ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Framing.fst"
                                             (Prims.of_int (106))
                                             (Prims.of_int (30))
                                             (Prims.of_int (106))
                                             (Prims.of_int (57)))
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Framing.fst"
                                             (Prims.of_int (106))
                                             (Prims.of_int (8))
                                             (Prims.of_int (106))
                                             (Prims.of_int (57)))
                                          (Obj.magic
                                             (try_split_vprop g tl ctxt))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  mk_framing_failure g tl req
                                                    ctxt ctxt hd uu___1)))
                                 | FStar_Pervasives_Native.Some
                                     (FStar_Pervasives.Mkdtuple4
                                     (l, q, d, r)) ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Framing.fst"
                                             (Prims.of_int (112))
                                             (Prims.of_int (12))
                                             (Prims.of_int (112))
                                             (Prims.of_int (50)))
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Framing.fst"
                                             (Prims.of_int (114))
                                             (Prims.of_int (8))
                                             (Prims.of_int (128))
                                             (Prims.of_int (30)))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___1 -> ()))
                                          (fun uu___1 ->
                                             (fun d1 ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Framing.fst"
                                                        (Prims.of_int (114))
                                                        (Prims.of_int (14))
                                                        (Prims.of_int (114))
                                                        (Prims.of_int (42)))
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Framing.fst"
                                                        (Prims.of_int (114))
                                                        (Prims.of_int (8))
                                                        (Prims.of_int (128))
                                                        (Prims.of_int (30)))
                                                     (Obj.magic
                                                        (try_split_vprop g tl
                                                           (FStar_List_Tot_Base.op_At
                                                              l r)))
                                                     (fun uu___1 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___2 ->
                                                             match uu___1
                                                             with
                                                             | FStar_Pervasives.Inr
                                                                 failure ->
                                                                 FStar_Pervasives.Inr
                                                                   failure
                                                             | FStar_Pervasives.Inl
                                                                 (Prims.Mkdtuple2
                                                                 (frame, d2))
                                                                 ->
                                                                 FStar_Pervasives.Inl
                                                                   (Prims.Mkdtuple2
                                                                    (frame,
                                                                    ()))))))
                                               uu___1))) uu___)))) uu___2
          uu___1 uu___
let (split_vprop :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        Pulse_Syntax_Base.term ->
          (((Pulse_Syntax_Base.term, unit, unit) FStar_Pervasives.dtuple3,
             framing_failure) FStar_Pervasives.either,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt ->
      fun ctxt_typing ->
        fun req ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
               (Prims.of_int (139)) (Prims.of_int (18)) (Prims.of_int (139))
               (Prims.of_int (39)))
            (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
               (Prims.of_int (139)) (Prims.of_int (42)) (Prims.of_int (151))
               (Prims.of_int (50)))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ -> Pulse_Checker_VPropEquiv.vprop_as_list ctxt))
            (fun uu___ ->
               (fun ctxt_l ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                          (Prims.of_int (140)) (Prims.of_int (17))
                          (Prims.of_int (140)) (Prims.of_int (37)))
                       (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                          (Prims.of_int (141)) (Prims.of_int (5))
                          (Prims.of_int (151)) (Prims.of_int (50)))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ ->
                             Pulse_Checker_VPropEquiv.vprop_as_list req))
                       (fun uu___ ->
                          (fun req_l ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range
                                     "Pulse.Checker.Framing.fst"
                                     (Prims.of_int (141)) (Prims.of_int (11))
                                     (Prims.of_int (141)) (Prims.of_int (41)))
                                  (FStar_Range.mk_range
                                     "Pulse.Checker.Framing.fst"
                                     (Prims.of_int (141)) (Prims.of_int (5))
                                     (Prims.of_int (151)) (Prims.of_int (50)))
                                  (Obj.magic (try_split_vprop g req_l ctxt_l))
                                  (fun uu___ ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___1 ->
                                          match uu___ with
                                          | FStar_Pervasives.Inr failure ->
                                              FStar_Pervasives.Inr failure
                                          | FStar_Pervasives.Inl
                                              (Prims.Mkdtuple2 (frame, veq))
                                              ->
                                              FStar_Pervasives.Inl
                                                (FStar_Pervasives.Mkdtuple3
                                                   ((Pulse_Checker_VPropEquiv.list_as_vprop
                                                       frame), (), ()))))))
                            uu___))) uu___)
let rec (all_matches :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.vprop Prims.list ->
      Pulse_Syntax_Base.vprop Prims.list ->
        ((unit, unit, unit) match_result, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun g ->
           fun p ->
             fun q ->
               match p with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ ->
                              {
                                matched = [];
                                unmatched_p = p;
                                unmatched_q = q;
                                p_eq = ();
                                q_eq = ()
                              })))
               | hd::tl ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                              (Prims.of_int (162)) (Prims.of_int (12))
                              (Prims.of_int (162)) (Prims.of_int (40)))
                           (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                              (Prims.of_int (162)) (Prims.of_int (6))
                              (Prims.of_int (190)) (Prims.of_int (25)))
                           (Obj.magic (maybe_split_one_vprop g hd q))
                           (fun uu___ ->
                              (fun uu___ ->
                                 match uu___ with
                                 | FStar_Pervasives_Native.None ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Framing.fst"
                                             (Prims.of_int (164))
                                             (Prims.of_int (18))
                                             (Prims.of_int (164))
                                             (Prims.of_int (36)))
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Framing.fst"
                                             (Prims.of_int (167))
                                             (Prims.of_int (10))
                                             (Prims.of_int (167))
                                             (Prims.of_int (58)))
                                          (Obj.magic (all_matches g tl q))
                                          (fun res ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___1 ->
                                                  {
                                                    matched = (res.matched);
                                                    unmatched_p = (hd ::
                                                      (res.unmatched_p));
                                                    unmatched_q =
                                                      (res.unmatched_q);
                                                    p_eq = ();
                                                    q_eq = ()
                                                  })))
                                 | FStar_Pervasives_Native.Some res ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Framing.fst"
                                             (Prims.of_int (170))
                                             (Prims.of_int (35))
                                             (Prims.of_int (170))
                                             (Prims.of_int (38)))
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Framing.fst"
                                             (Prims.of_int (169))
                                             (Prims.of_int (19))
                                             (Prims.of_int (190))
                                             (Prims.of_int (25)))
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___1 -> res))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                match uu___1 with
                                                | FStar_Pervasives.Mkdtuple4
                                                    (l, found, v, r) ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Framing.fst"
                                                            (Prims.of_int (172))
                                                            (Prims.of_int (41))
                                                            (Prims.of_int (172))
                                                            (Prims.of_int (42)))
                                                         (FStar_Range.mk_range
                                                            "Pulse.Checker.Framing.fst"
                                                            (Prims.of_int (172))
                                                            (Prims.of_int (45))
                                                            (Prims.of_int (190))
                                                            (Prims.of_int (25)))
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___2 -> ()))
                                                         (fun uu___2 ->
                                                            (fun v1 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Framing.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (42)))
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Checker.Framing.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (23)))
                                                                    (
                                                                    Obj.magic
                                                                    (all_matches
                                                                    g tl
                                                                    (FStar_List_Tot_Base.op_At
                                                                    l r)))
                                                                    (
                                                                    fun res1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    {
                                                                    matched =
                                                                    (hd ::
                                                                    (res1.matched));
                                                                    unmatched_p
                                                                    =
                                                                    (res1.unmatched_p);
                                                                    unmatched_q
                                                                    =
                                                                    (res1.unmatched_q);
                                                                    p_eq = ();
                                                                    q_eq = ()
                                                                    }))))
                                                              uu___2)))
                                               uu___1))) uu___)))) uu___2
          uu___1 uu___
let rec (check_equiv_emp :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term -> unit FStar_Pervasives_Native.option)
  =
  fun g ->
    fun vp ->
      match vp with
      | Pulse_Syntax_Base.Tm_Emp -> FStar_Pervasives_Native.Some ()
      | Pulse_Syntax_Base.Tm_Star (vp1, vp2) ->
          (match ((check_equiv_emp g vp1), (check_equiv_emp g vp2)) with
           | (FStar_Pervasives_Native.Some d1, FStar_Pervasives_Native.Some
              d2) -> FStar_Pervasives_Native.Some ()
           | (uu___, uu___1) -> FStar_Pervasives_Native.None)
      | uu___ -> FStar_Pervasives_Native.None
let (check_vprop_equiv :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun vp1 ->
      fun vp2 ->
        fun vp1_typing ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
               (Prims.of_int (216)) (Prims.of_int (8)) (Prims.of_int (216))
               (Prims.of_int (40)))
            (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
               (Prims.of_int (216)) (Prims.of_int (2)) (Prims.of_int (242))
               (Prims.of_int (54))) (Obj.magic (split_vprop g vp1 () vp2))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | FStar_Pervasives.Inr failure ->
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Framing.fst"
                                 (Prims.of_int (218)) (Prims.of_int (11))
                                 (Prims.of_int (222)) (Prims.of_int (94)))
                              (FStar_Range.mk_range
                                 "Pulse.Checker.Framing.fst"
                                 (Prims.of_int (218)) (Prims.of_int (4))
                                 (Prims.of_int (222)) (Prims.of_int (94)))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Framing.fst"
                                       (Prims.of_int (222))
                                       (Prims.of_int (16))
                                       (Prims.of_int (222))
                                       (Prims.of_int (93)))
                                    (FStar_Range.mk_range
                                       "Pulse.Checker.Framing.fst"
                                       (Prims.of_int (218))
                                       (Prims.of_int (11))
                                       (Prims.of_int (222))
                                       (Prims.of_int (94)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Framing.fst"
                                             (Prims.of_int (222))
                                             (Prims.of_int (36))
                                             (Prims.of_int (222))
                                             (Prims.of_int (92)))
                                          (FStar_Range.mk_range
                                             "Pulse.Checker.Framing.fst"
                                             (Prims.of_int (222))
                                             (Prims.of_int (16))
                                             (Prims.of_int (222))
                                             (Prims.of_int (93)))
                                          (Obj.magic
                                             (FStar_Tactics_Util.map
                                                Pulse_Syntax_Printer.term_to_string
                                                failure.unmatched_preconditions))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  FStar_String.concat "\n"
                                                    uu___1))))
                                    (fun uu___1 ->
                                       (fun uu___1 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Framing.fst"
                                                  (Prims.of_int (218))
                                                  (Prims.of_int (11))
                                                  (Prims.of_int (222))
                                                  (Prims.of_int (94)))
                                               (FStar_Range.mk_range
                                                  "Pulse.Checker.Framing.fst"
                                                  (Prims.of_int (218))
                                                  (Prims.of_int (11))
                                                  (Prims.of_int (222))
                                                  (Prims.of_int (94)))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Framing.fst"
                                                        (Prims.of_int (221))
                                                        (Prims.of_int (16))
                                                        (Prims.of_int (221))
                                                        (Prims.of_int (38)))
                                                     (FStar_Range.mk_range
                                                        "Pulse.Checker.Framing.fst"
                                                        (Prims.of_int (218))
                                                        (Prims.of_int (11))
                                                        (Prims.of_int (222))
                                                        (Prims.of_int (94)))
                                                     (Obj.magic
                                                        (Pulse_Syntax_Printer.term_to_string
                                                           vp2))
                                                     (fun uu___2 ->
                                                        (fun uu___2 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Framing.fst"
                                                                   (Prims.of_int (218))
                                                                   (Prims.of_int (11))
                                                                   (Prims.of_int (222))
                                                                   (Prims.of_int (94)))
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Checker.Framing.fst"
                                                                   (Prims.of_int (218))
                                                                   (Prims.of_int (11))
                                                                   (Prims.of_int (222))
                                                                   (Prims.of_int (94)))
                                                                (Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Framing.fst"
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (38)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    vp1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_vprop_equiv: "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " and "))
                                                                    (Prims.strcat
                                                                    x
                                                                    " are not equivalent; missing preconditions:\n"))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
                                                                (fun uu___3
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    uu___3
                                                                    uu___2))))
                                                          uu___2)))
                                               (fun uu___2 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___3 ->
                                                       uu___2 uu___1))))
                                         uu___1)))
                              (fun uu___1 ->
                                 FStar_Tactics_Derived.fail uu___1)))
                  | FStar_Pervasives.Inl (FStar_Pervasives.Mkdtuple3
                      (frame, uu___1, d)) ->
                      Obj.magic
                        (Obj.repr
                           (match check_equiv_emp g frame with
                            | FStar_Pervasives_Native.Some d_frame_equiv_emp
                                ->
                                Obj.repr
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 -> ()))
                            | FStar_Pervasives_Native.None ->
                                Obj.repr
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Framing.fst"
                                        (Prims.of_int (239))
                                        (Prims.of_int (13))
                                        (Prims.of_int (242))
                                        (Prims.of_int (54)))
                                     (FStar_Range.mk_range
                                        "Pulse.Checker.Framing.fst"
                                        (Prims.of_int (239))
                                        (Prims.of_int (6))
                                        (Prims.of_int (242))
                                        (Prims.of_int (54)))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Framing.fst"
                                              (Prims.of_int (242))
                                              (Prims.of_int (29))
                                              (Prims.of_int (242))
                                              (Prims.of_int (53)))
                                           (FStar_Range.mk_range
                                              "Pulse.Checker.Framing.fst"
                                              (Prims.of_int (239))
                                              (Prims.of_int (13))
                                              (Prims.of_int (242))
                                              (Prims.of_int (54)))
                                           (Obj.magic
                                              (Pulse_Syntax_Printer.term_to_string
                                                 frame))
                                           (fun uu___2 ->
                                              (fun uu___2 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Framing.fst"
                                                         (Prims.of_int (239))
                                                         (Prims.of_int (13))
                                                         (Prims.of_int (242))
                                                         (Prims.of_int (54)))
                                                      (FStar_Range.mk_range
                                                         "Pulse.Checker.Framing.fst"
                                                         (Prims.of_int (239))
                                                         (Prims.of_int (13))
                                                         (Prims.of_int (242))
                                                         (Prims.of_int (54)))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Framing.fst"
                                                               (Prims.of_int (241))
                                                               (Prims.of_int (29))
                                                               (Prims.of_int (241))
                                                               (Prims.of_int (51)))
                                                            (FStar_Range.mk_range
                                                               "Pulse.Checker.Framing.fst"
                                                               (Prims.of_int (239))
                                                               (Prims.of_int (13))
                                                               (Prims.of_int (242))
                                                               (Prims.of_int (54)))
                                                            (Obj.magic
                                                               (Pulse_Syntax_Printer.term_to_string
                                                                  vp2))
                                                            (fun uu___3 ->
                                                               (fun uu___3 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Framing.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (54)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Framing.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (54)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Checker.Framing.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (51)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (Pulse_Syntax_Printer.term_to_string
                                                                    vp1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "check_vprop_equiv: "
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    " and "))
                                                                    (Prims.strcat
                                                                    x
                                                                    " are not equivalent, frame: "))
                                                                    (Prims.strcat
                                                                    x1 "\n")))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4
                                                                    uu___3))))
                                                                 uu___3)))
                                                      (fun uu___3 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              uu___3 uu___2))))
                                                uu___2)))
                                     (fun uu___2 ->
                                        FStar_Tactics_Derived.fail uu___2)))))
                 uu___)
type ('g, 'ctxt, 'req) frame_for_req_in_ctxt =
  (Pulse_Syntax_Base.term, unit, unit) FStar_Pervasives.dtuple3
let (frame_of :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      Pulse_Syntax_Base.term ->
        (unit, unit, unit) frame_for_req_in_ctxt -> Pulse_Syntax_Base.term)
  =
  fun g ->
    fun ctxt ->
      fun req ->
        fun f ->
          let uu___ = f in
          match uu___ with
          | FStar_Pervasives.Mkdtuple3 (frame, uu___1, uu___2) -> frame
let (check_frameable :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        Pulse_Syntax_Base.term ->
          (((unit, unit, unit) frame_for_req_in_ctxt, framing_failure)
             FStar_Pervasives.either,
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun ctxt -> fun ctxt_typing -> fun req -> split_vprop g ctxt () req
let (apply_frame :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          Pulse_Syntax_Base.comp ->
            (unit, unit, unit) Pulse_Typing.st_typing ->
              (unit, unit, unit) frame_for_req_in_ctxt ->
                (Pulse_Syntax_Base.comp_st,
                  (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2)
  =
  fun g ->
    fun t ->
      fun ctxt ->
        fun ctxt_typing ->
          fun c ->
            fun t_typing ->
              fun frame_t ->
                let s = Pulse_Syntax_Base.st_comp_of_comp c in
                let uu___ = frame_t in
                match uu___ with
                | FStar_Pervasives.Mkdtuple3 (frame, frame_typing, ve) ->
                    let t_typing1 =
                      Pulse_Typing.T_Frame (g, t, c, frame, (), t_typing) in
                    let c' = Pulse_Typing.add_frame c frame in
                    let c'_typing =
                      Pulse_Typing_Metatheory.st_typing_correctness g t
                        (Pulse_Typing.add_frame c frame) t_typing1 in
                    let s' = Pulse_Syntax_Base.st_comp_of_comp c' in
                    let s'' =
                      {
                        Pulse_Syntax_Base.u = (s'.Pulse_Syntax_Base.u);
                        Pulse_Syntax_Base.res = (s'.Pulse_Syntax_Base.res);
                        Pulse_Syntax_Base.pre = ctxt;
                        Pulse_Syntax_Base.post = (s'.Pulse_Syntax_Base.post)
                      } in
                    let c'' = Pulse_Syntax_Base.with_st_comp c' s'' in
                    let st_typing =
                      Pulse_Typing_Metatheory.comp_typing_inversion g
                        (Pulse_Typing.add_frame c frame) c'_typing in
                    let uu___1 =
                      Pulse_Typing_Metatheory.st_comp_typing_inversion g
                        (Pulse_Syntax_Base.st_comp_of_comp
                           (Pulse_Typing.add_frame c frame)) st_typing in
                    (match uu___1 with
                     | FStar_Pervasives.Mkdtuple4
                         (res_typing, pre_typing, x, post_typing) ->
                         let st_equiv =
                           Pulse_Typing.ST_VPropEquiv
                             (g, c', c'', x, (), (), (), (), ()) in
                         let t_typing2 =
                           Pulse_Typing.T_Equiv
                             (g, t, (Pulse_Typing.add_frame c frame), c'',
                               t_typing1, st_equiv) in
                         Prims.Mkdtuple2 (c'', t_typing2))
let (try_frame_pre :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.st_term ->
      Pulse_Syntax_Base.term ->
        unit ->
          Pulse_Syntax_Base.comp_st ->
            (unit, unit, unit) Pulse_Typing.st_typing ->
              (((Pulse_Syntax_Base.comp_st,
                  (unit, unit, unit) Pulse_Typing.st_typing) Prims.dtuple2,
                 framing_failure) FStar_Pervasives.either,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      fun pre ->
        fun pre_typing ->
          fun c ->
            fun t_typing ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                   (Prims.of_int (301)) (Prims.of_int (10))
                   (Prims.of_int (301)) (Prims.of_int (49)))
                (FStar_Range.mk_range "Pulse.Checker.Framing.fst"
                   (Prims.of_int (301)) (Prims.of_int (4))
                   (Prims.of_int (305)) (Prims.of_int (24)))
                (Obj.magic
                   (check_frameable g pre () (Pulse_Syntax_Base.comp_pre c)))
                (fun uu___ ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 ->
                        match uu___ with
                        | FStar_Pervasives.Inr failure ->
                            FStar_Pervasives.Inr failure
                        | FStar_Pervasives.Inl frame_t ->
                            (match apply_frame g t pre () c t_typing frame_t
                             with
                             | Prims.Mkdtuple2 (c', st_d) ->
                                 FStar_Pervasives.Inl
                                   (Prims.Mkdtuple2 (c', st_d)))))
let (frame_empty :
  Pulse_Typing.env ->
    Pulse_Syntax_Base.term ->
      unit ->
        Pulse_Syntax_Base.universe ->
          Pulse_Syntax_Base.term ->
            unit ->
              Pulse_Syntax_Base.st_term ->
                Pulse_Syntax_Base.comp_st ->
                  (unit, unit, unit) Pulse_Typing.st_typing ->
                    ((Pulse_Syntax_Base.comp_st,
                       (unit, unit, unit) Pulse_Typing.st_typing)
                       Prims.dtuple2,
                      unit) FStar_Tactics_Effect.tac_repr)
  =
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
                         fun pre_typing ->
                           fun u ->
                             fun ty ->
                               fun ut ->
                                 fun t ->
                                   fun c0 ->
                                     fun d ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___ ->
                                               match Pulse_Typing_Metatheory.st_comp_typing_inversion
                                                       g
                                                       (Pulse_Syntax_Base.st_comp_of_comp
                                                          (Pulse_Typing.add_frame
                                                             c0 pre))
                                                       (Pulse_Typing_Metatheory.comp_typing_inversion
                                                          g
                                                          (Pulse_Typing.add_frame
                                                             c0 pre)
                                                          (Pulse_Typing_Metatheory.st_typing_correctness
                                                             g t
                                                             (Pulse_Typing.add_frame
                                                                c0 pre)
                                                             (Pulse_Typing.T_Frame
                                                                (g, t, c0,
                                                                  pre, (), d))))
                                               with
                                               | FStar_Pervasives.Mkdtuple4
                                                   (res_typing, pre_typing1,
                                                    x, post_typing)
                                                   ->
                                                   Prims.Mkdtuple2
                                                     ((Pulse_Syntax_Base.with_st_comp
                                                         (Pulse_Typing.add_frame
                                                            c0 pre)
                                                         {
                                                           Pulse_Syntax_Base.u
                                                             =
                                                             ((Pulse_Syntax_Base.st_comp_of_comp
                                                                 (Pulse_Typing.add_frame
                                                                    c0 pre)).Pulse_Syntax_Base.u);
                                                           Pulse_Syntax_Base.res
                                                             =
                                                             ((Pulse_Syntax_Base.st_comp_of_comp
                                                                 (Pulse_Typing.add_frame
                                                                    c0 pre)).Pulse_Syntax_Base.res);
                                                           Pulse_Syntax_Base.pre
                                                             = pre;
                                                           Pulse_Syntax_Base.post
                                                             =
                                                             ((Pulse_Syntax_Base.st_comp_of_comp
                                                                 (Pulse_Typing.add_frame
                                                                    c0 pre)).Pulse_Syntax_Base.post)
                                                         }),
                                                       (Pulse_Typing.T_Equiv
                                                          (g, t,
                                                            (Pulse_Typing.add_frame
                                                               c0 pre),
                                                            (Pulse_Syntax_Base.with_st_comp
                                                               (Pulse_Typing.add_frame
                                                                  c0 pre)
                                                               {
                                                                 Pulse_Syntax_Base.u
                                                                   =
                                                                   ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.add_frame
                                                                    c0 pre)).Pulse_Syntax_Base.u);
                                                                 Pulse_Syntax_Base.res
                                                                   =
                                                                   ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.add_frame
                                                                    c0 pre)).Pulse_Syntax_Base.res);
                                                                 Pulse_Syntax_Base.pre
                                                                   = pre;
                                                                 Pulse_Syntax_Base.post
                                                                   =
                                                                   ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.add_frame
                                                                    c0 pre)).Pulse_Syntax_Base.post)
                                                               }),
                                                            (Pulse_Typing.T_Frame
                                                               (g, t, c0,
                                                                 pre, (), d)),
                                                            (Pulse_Typing.ST_VPropEquiv
                                                               (g,
                                                                 (Pulse_Typing.add_frame
                                                                    c0 pre),
                                                                 (Pulse_Syntax_Base.with_st_comp
                                                                    (
                                                                    Pulse_Typing.add_frame
                                                                    c0 pre)
                                                                    {
                                                                    Pulse_Syntax_Base.u
                                                                    =
                                                                    ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.add_frame
                                                                    c0 pre)).Pulse_Syntax_Base.u);
                                                                    Pulse_Syntax_Base.res
                                                                    =
                                                                    ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.add_frame
                                                                    c0 pre)).Pulse_Syntax_Base.res);
                                                                    Pulse_Syntax_Base.pre
                                                                    = pre;
                                                                    Pulse_Syntax_Base.post
                                                                    =
                                                                    ((Pulse_Syntax_Base.st_comp_of_comp
                                                                    (Pulse_Typing.add_frame
                                                                    c0 pre)).Pulse_Syntax_Base.post)
                                                                    }), x,
                                                                 (), (), (),
                                                                 (), ()))))))))
                      uu___8 uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1
                      uu___