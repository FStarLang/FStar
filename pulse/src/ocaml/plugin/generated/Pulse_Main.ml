open Prims
let (main' :
  Pulse_Syntax_Base.st_term ->
    Pulse_Syntax_Base.term ->
      FStar_Reflection_Typing.fstar_top_env ->
        ((FStar_Reflection_Types.term * FStar_Reflection_Types.typ), 
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun pre ->
      fun g ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (20))
             (Prims.of_int (4)) (Prims.of_int (20)) (Prims.of_int (87)))
          (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (21))
             (Prims.of_int (4)) (Prims.of_int (32)) (Prims.of_int (66)))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (20))
                   (Prims.of_int (12)) (Prims.of_int (20))
                   (Prims.of_int (87)))
                (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (20))
                   (Prims.of_int (4)) (Prims.of_int (20)) (Prims.of_int (87)))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range "Pulse.Main.fst"
                         (Prims.of_int (20)) (Prims.of_int (63))
                         (Prims.of_int (20)) (Prims.of_int (86)))
                      (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                         (Prims.of_int (19)) (Prims.of_int (590))
                         (Prims.of_int (31)))
                      (Obj.magic (Pulse_Syntax_Printer.st_term_to_string t))
                      (fun uu___ ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 ->
                              Prims.strcat "About to check pulse term:\n"
                                (Prims.strcat uu___ "\n")))))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic (FStar_Tactics_Builtins.print uu___)) uu___)))
          (fun uu___ ->
             (fun uu___ ->
                match Pulse_Soundness_Common.check_top_level_environment g
                with
                | FStar_Pervasives_Native.None ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Derived.fail
                            "pulse main: top-level environment does not include stt at the expected types"))
                | FStar_Pervasives_Native.Some g1 ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range "Pulse.Main.fst"
                               (Prims.of_int (24)) (Prims.of_int (38))
                               (Prims.of_int (24)) (Prims.of_int (73)))
                            (FStar_Range.mk_range "Pulse.Main.fst"
                               (Prims.of_int (23)) (Prims.of_int (15))
                               (Prims.of_int (32)) (Prims.of_int (66)))
                            (Obj.magic (Pulse_Checker_Pure.check_term g1 pre))
                            (fun uu___1 ->
                               (fun uu___1 ->
                                  match uu___1 with
                                  | FStar_Pervasives.Mkdtuple3
                                      (pre1, ty, pre_typing) ->
                                      if
                                        Pulse_Syntax_Base.eq_tm ty
                                          Pulse_Syntax_Base.Tm_VProp
                                      then
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Range.mk_range
                                                   "Pulse.Main.fst"
                                                   (Prims.of_int (26))
                                                   (Prims.of_int (56))
                                                   (Prims.of_int (26))
                                                   (Prims.of_int (68)))
                                                (FStar_Range.mk_range
                                                   "Pulse.Main.fst"
                                                   (Prims.of_int (26))
                                                   (Prims.of_int (71))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (27)))
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___2 -> ()))
                                                (fun uu___2 ->
                                                   (fun pre_typing1 ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "Pulse.Main.fst"
                                                              (Prims.of_int (27))
                                                              (Prims.of_int (38))
                                                              (Prims.of_int (27))
                                                              (Prims.of_int (67)))
                                                           (FStar_Range.mk_range
                                                              "Pulse.Main.fst"
                                                              (Prims.of_int (26))
                                                              (Prims.of_int (71))
                                                              (Prims.of_int (31))
                                                              (Prims.of_int (27)))
                                                           (Obj.magic
                                                              (Pulse_Checker.check
                                                                 g1 t pre1 ()
                                                                 FStar_Pervasives_Native.None))
                                                           (fun uu___2 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___3
                                                                   ->
                                                                   match uu___2
                                                                   with
                                                                   | 
                                                                   FStar_Pervasives.Mkdtuple3
                                                                    (t1, c,
                                                                    t_typing)
                                                                    ->
                                                                    ((Pulse_Elaborate_Core.elab_st_typing
                                                                    g1 t1 c
                                                                    t_typing),
                                                                    (Pulse_Elaborate_Pure.elab_comp
                                                                    c))))))
                                                     uu___2)))
                                      else
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Derived.fail
                                                "pulse main: cannot typecheck pre at type vprop")))
                                 uu___1)))) uu___)
let (main :
  Pulse_Syntax_Base.st_term ->
    Pulse_Syntax_Base.term -> FStar_Reflection_Typing.dsl_tac_t)
  = fun t -> fun pre -> main' t pre
let (tuple2_lid : Prims.string Prims.list) =
  ["FStar"; "Pervasives"; "Native"; "tuple2"]
let (tuple3_lid : Prims.string Prims.list) =
  ["FStar"; "Pervasives"; "Native"; "tuple3"]
let (tuple4_lid : Prims.string Prims.list) =
  ["FStar"; "Pervasives"; "Native"; "tuple4"]
let (tuple5_lid : Prims.string Prims.list) =
  ["FStar"; "Pervasives"; "Native"; "tuple5"]
let (tuple6_lid : Prims.string Prims.list) =
  ["FStar"; "Pervasives"; "Native"; "tuple6"]
let (tuple7_lid : Prims.string Prims.list) =
  ["FStar"; "Pervasives"; "Native"; "tuple7"]
type 'a err = ('a, Prims.string) FStar_Pervasives.either
let error : 'a . Prims.string -> ('a err, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___ ->
    (fun msg ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ -> FStar_Pervasives.Inr msg))) uu___
let op_let_Question :
  'a 'b .
    'a err ->
      ('a -> ('b err, unit) FStar_Tactics_Effect.tac_repr) ->
        ('b err, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun o ->
         fun f ->
           match o with
           | FStar_Pervasives.Inr msg ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> FStar_Pervasives.Inr msg)))
           | FStar_Pervasives.Inl v -> Obj.magic (Obj.repr (f v))) uu___1
        uu___
let unexpected_term :
  'uuuuu .
    Prims.string ->
      FStar_Reflection_Types.term ->
        ('uuuuu err, unit) FStar_Tactics_Effect.tac_repr
  =
  fun msg ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (57))
           (Prims.of_int (8)) (Prims.of_int (59)) (Prims.of_int (49)))
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (57))
           (Prims.of_int (2)) (Prims.of_int (59)) (Prims.of_int (49)))
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (59))
                 (Prims.of_int (28)) (Prims.of_int (59)) (Prims.of_int (48)))
              (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                 (Prims.of_int (19)) (Prims.of_int (590)) (Prims.of_int (31)))
              (Obj.magic (FStar_Tactics_Builtins.term_to_string t))
              (fun uu___ ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      Prims.strcat
                        (Prims.strcat "Unexpected term ("
                           (Prims.strcat msg "): ")) (Prims.strcat uu___ "")))))
        (fun uu___ -> (fun uu___ -> Obj.magic (error uu___)) uu___)
let (readback_maybe_unknown_ty :
  FStar_Reflection_Types.term -> Pulse_Syntax_Base.term) =
  fun t ->
    match Pulse_Readback.readback_ty t with
    | FStar_Pervasives_Native.Some t1 -> t1
    | FStar_Pervasives_Native.None -> Pulse_Syntax_Base.Tm_Unknown
let (readback_ty :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      (Pulse_Syntax_Base.term err, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun t ->
           match Pulse_Readback.readback_ty t with
           | FStar_Pervasives_Native.None ->
               Obj.magic (Obj.repr (unexpected_term "readback failed" t))
           | FStar_Pervasives_Native.Some t1 ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> FStar_Pervasives.Inl t1)))) uu___1 uu___
let (mk_star : Pulse_Syntax_Base.term Prims.list -> Pulse_Syntax_Base.term) =
  fun l ->
    match l with
    | [] -> Pulse_Syntax_Base.Tm_Emp
    | x::[] -> x
    | x::y::[] -> Pulse_Syntax_Base.Tm_Star (x, y)
    | x::y::tl ->
        FStar_List_Tot_Base.fold_left
          (fun t -> fun x1 -> Pulse_Syntax_Base.Tm_Star (t, x1))
          (Pulse_Syntax_Base.Tm_Star (x, y)) tl
let (is_ntuple : FStar_Reflection_Types.name -> Prims.bool) =
  fun s ->
    (((((s = tuple2_lid) || (s = tuple3_lid)) || (s = tuple4_lid)) ||
        (s = tuple5_lid))
       || (s = tuple6_lid))
      || (s = tuple7_lid)
let rec (translate_vprop :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      (Pulse_Syntax_Base.vprop err, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (87))
           (Prims.of_int (19)) (Prims.of_int (87)) (Prims.of_int (32)))
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (87))
           (Prims.of_int (3)) (Prims.of_int (105)) (Prims.of_int (21)))
        (Obj.magic (FStar_Tactics_SyntaxHelpers.collect_app t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (hd, args) ->
                  (match FStar_Reflection_Builtins.inspect_ln hd with
                   | FStar_Reflection_Data.Tv_FVar fv ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range "Pulse.Main.fst"
                               (Prims.of_int (90)) (Prims.of_int (15))
                               (Prims.of_int (90)) (Prims.of_int (28)))
                            (FStar_Range.mk_range "Pulse.Main.fst"
                               (Prims.of_int (91)) (Prims.of_int (6))
                               (Prims.of_int (102)) (Prims.of_int (26)))
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 ->
                                  FStar_Reflection_Builtins.inspect_fv fv))
                            (fun uu___1 ->
                               (fun qn ->
                                  if qn = Pulse_Reflection_Util.exists_lid
                                  then Obj.magic (translate_exists g t)
                                  else
                                    if qn = FStar_Reflection_Const.exists_qn
                                    then
                                      Obj.magic
                                        (translate_exists_formula g t)
                                    else
                                      if qn = Pulse_Reflection_Util.star_lid
                                      then Obj.magic (translate_star g t)
                                      else
                                        if is_ntuple qn
                                        then
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "Pulse.Main.fst"
                                                  (Prims.of_int (98))
                                                  (Prims.of_int (20))
                                                  (Prims.of_int (98))
                                                  (Prims.of_int (66)))
                                               (FStar_Range.mk_range
                                                  "Pulse.Main.fst"
                                                  (Prims.of_int (98))
                                                  (Prims.of_int (11))
                                                  (Prims.of_int (99))
                                                  (Prims.of_int (26)))
                                               (Obj.magic
                                                  (translate_vprop_list g
                                                     (FStar_List_Tot_Base.map
                                                        FStar_Pervasives_Native.fst
                                                        args)))
                                               (fun uu___4 ->
                                                  (fun uu___4 ->
                                                     Obj.magic
                                                       (op_let_Question
                                                          uu___4
                                                          (fun uu___5 ->
                                                             (fun l ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Inl
                                                                    (mk_star
                                                                    l))))
                                                               uu___5)))
                                                    uu___4))
                                        else
                                          if
                                            qn =
                                              Pulse_Reflection_Util.pure_lid
                                          then Obj.magic (translate_pure g t)
                                          else Obj.magic (readback_ty g t))
                                 uu___1))
                   | uu___1 -> Obj.magic (readback_ty g t))) uu___)
and (translate_exists :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      (Pulse_Syntax_Base.term err, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun t ->
           match FStar_Reflection_Builtins.inspect_ln t with
           | FStar_Reflection_Data.Tv_App (hd, (arg, uu___)) ->
               Obj.magic
                 (Obj.repr
                    (match FStar_Reflection_Builtins.inspect_ln hd with
                     | FStar_Reflection_Data.Tv_FVar fv ->
                         Obj.repr
                           (if
                              (FStar_Reflection_Builtins.inspect_fv fv) =
                                Pulse_Reflection_Util.exists_lid
                            then Obj.repr (translate_exists_sl_body g arg)
                            else
                              Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 ->
                                      FStar_Pervasives.Inr
                                        "try readback exists: not an exists lid")))
                     | uu___1 ->
                         Obj.repr
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 ->
                                 FStar_Pervasives.Inr
                                   "try readback exists: head not an fvar"))))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 ->
                          FStar_Pervasives.Inr
                            "try readback exists: not an app")))) uu___1
        uu___
and (translate_exists_sl_body :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      (Pulse_Syntax_Base.term err, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun t ->
           match FStar_Reflection_Builtins.inspect_ln t with
           | FStar_Reflection_Data.Tv_Abs (b, body) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (123)) (Prims.of_int (17))
                          (Prims.of_int (123)) (Prims.of_int (47)))
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (123)) (Prims.of_int (50))
                          (Prims.of_int (127)) (Prims.of_int (49)))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ ->
                             (FStar_Reflection_Builtins.inspect_binder b).FStar_Reflection_Data.binder_sort))
                       (fun uu___ ->
                          (fun sort ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (124)) (Prims.of_int (14))
                                     (Prims.of_int (124)) (Prims.of_int (38)))
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (124)) (Prims.of_int (41))
                                     (Prims.of_int (127)) (Prims.of_int (49)))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___ ->
                                        FStar_Reflection_Builtins.pack_universe
                                          FStar_Reflection_Data.Uv_Unk))
                                  (fun uu___ ->
                                     (fun u ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (125))
                                                (Prims.of_int (14))
                                                (Prims.of_int (125))
                                                (Prims.of_int (44)))
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (126))
                                                (Prims.of_int (6))
                                                (Prims.of_int (127))
                                                (Prims.of_int (49)))
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___ ->
                                                   readback_maybe_unknown_ty
                                                     sort))
                                             (fun uu___ ->
                                                (fun t1 ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (126))
                                                           (Prims.of_int (18))
                                                           (Prims.of_int (126))
                                                           (Prims.of_int (40)))
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (126))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (127))
                                                           (Prims.of_int (49)))
                                                        (Obj.magic
                                                           (translate_vprop g
                                                              body))
                                                        (fun uu___ ->
                                                           (fun uu___ ->
                                                              Obj.magic
                                                                (op_let_Question
                                                                   uu___
                                                                   (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Pervasives.Inl
                                                                    (Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (u, t1,
                                                                    body1,
                                                                    Pulse_Syntax_Base.should_elim_true)))))
                                                                    uu___1)))
                                                             uu___))) uu___)))
                                       uu___))) uu___)))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 ->
                          FStar_Pervasives.Inr
                            "in readback exists: the arg not a lambda"))))
        uu___1 uu___
and (translate_exists_formula :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      (Pulse_Syntax_Base.term err, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (133))
           (Prims.of_int (8)) (Prims.of_int (134)) (Prims.of_int (47)))
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (136))
           (Prims.of_int (4)) (Prims.of_int (149)) (Prims.of_int (19)))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              fun uu___1 ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (133))
                     (Prims.of_int (12)) (Prims.of_int (134))
                     (Prims.of_int (47)))
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (133))
                     (Prims.of_int (8)) (Prims.of_int (134))
                     (Prims.of_int (47)))
                  (Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "Pulse.Main.fst"
                           (Prims.of_int (134)) (Prims.of_int (28))
                           (Prims.of_int (134)) (Prims.of_int (46)))
                        (FStar_Range.mk_range "prims.fst"
                           (Prims.of_int (590)) (Prims.of_int (19))
                           (Prims.of_int (590)) (Prims.of_int (31)))
                        (Obj.magic (FStar_Tactics_Builtins.term_to_string t))
                        (fun uu___2 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 ->
                                Prims.strcat "Not an exists formula: "
                                  (Prims.strcat uu___2 "")))))
                  (fun uu___2 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___3 -> FStar_Pervasives.Inr uu___2))))
        (fun uu___ ->
           (fun fail ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Main.fst"
                      (Prims.of_int (136)) (Prims.of_int (10))
                      (Prims.of_int (136)) (Prims.of_int (27)))
                   (FStar_Range.mk_range "Pulse.Main.fst"
                      (Prims.of_int (136)) (Prims.of_int (4))
                      (Prims.of_int (149)) (Prims.of_int (19)))
                   (Obj.magic (FStar_Reflection_Formula.term_as_formula t))
                   (fun uu___ ->
                      (fun uu___ ->
                         match uu___ with
                         | FStar_Reflection_Formula.Exists (bv, sort, body)
                             ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (138)) (Prims.of_int (15))
                                     (Prims.of_int (138)) (Prims.of_int (28)))
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (138)) (Prims.of_int (31))
                                     (Prims.of_int (141)) (Prims.of_int (74)))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 ->
                                        FStar_Reflection_Builtins.inspect_bv
                                          bv))
                                  (fun uu___1 ->
                                     (fun bv1 ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (139))
                                                (Prims.of_int (14))
                                                (Prims.of_int (139))
                                                (Prims.of_int (44)))
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (140))
                                                (Prims.of_int (6))
                                                (Prims.of_int (141))
                                                (Prims.of_int (74)))
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   readback_maybe_unknown_ty
                                                     sort))
                                             (fun uu___1 ->
                                                (fun t1 ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (140))
                                                           (Prims.of_int (18))
                                                           (Prims.of_int (140))
                                                           (Prims.of_int (40)))
                                                        (FStar_Range.mk_range
                                                           "Pulse.Main.fst"
                                                           (Prims.of_int (140))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (141))
                                                           (Prims.of_int (74)))
                                                        (Obj.magic
                                                           (translate_vprop g
                                                              body))
                                                        (fun uu___1 ->
                                                           (fun uu___1 ->
                                                              Obj.magic
                                                                (op_let_Question
                                                                   uu___1
                                                                   (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Inl
                                                                    (Pulse_Syntax_Base.Tm_ExistsSL
                                                                    ((FStar_Reflection_Builtins.pack_universe
                                                                    FStar_Reflection_Data.Uv_Unk),
                                                                    t1,
                                                                    body1,
                                                                    Pulse_Syntax_Base.should_elim_true)))))
                                                                    uu___2)))
                                                             uu___1))) uu___1)))
                                       uu___1))
                         | uu___1 ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (143)) (Prims.of_int (21))
                                     (Prims.of_int (143)) (Prims.of_int (34)))
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (142)) (Prims.of_int (10))
                                     (Prims.of_int (149)) (Prims.of_int (19)))
                                  (Obj.magic
                                     (FStar_Tactics_SyntaxHelpers.collect_app
                                        t))
                                  (fun uu___2 ->
                                     (fun uu___2 ->
                                        match uu___2 with
                                        | (hd, args) ->
                                            (match ((FStar_Reflection_Builtins.inspect_ln
                                                       hd), args)
                                             with
                                             | (FStar_Reflection_Data.Tv_FVar
                                                fv, (arg, uu___3)::[]) ->
                                                 if
                                                   (FStar_Reflection_Builtins.inspect_fv
                                                      fv)
                                                     =
                                                     FStar_Reflection_Const.exists_qn
                                                 then
                                                   Obj.magic
                                                     (translate_exists_sl_body
                                                        g arg)
                                                 else Obj.magic (fail ())
                                             | uu___3 -> Obj.magic (fail ())))
                                       uu___2))) uu___))) uu___)
and (translate_star :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      (Pulse_Syntax_Base.term err, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (153))
           (Prims.of_int (19)) (Prims.of_int (153)) (Prims.of_int (32)))
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (153))
           (Prims.of_int (3)) (Prims.of_int (162)) (Prims.of_int (28)))
        (Obj.magic (FStar_Tactics_SyntaxHelpers.collect_app t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (hd, args) ->
                  (match ((FStar_Reflection_Builtins.inspect_ln hd), args)
                   with
                   | (FStar_Reflection_Data.Tv_FVar fv,
                      (l, uu___1)::(r, uu___2)::[]) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range "Pulse.Main.fst"
                                  (Prims.of_int (156)) (Prims.of_int (16))
                                  (Prims.of_int (156)) (Prims.of_int (29)))
                               (FStar_Range.mk_range "Pulse.Main.fst"
                                  (Prims.of_int (157)) (Prims.of_int (6))
                                  (Prims.of_int (161)) (Prims.of_int (27)))
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 ->
                                     FStar_Reflection_Builtins.inspect_fv fv))
                               (fun uu___3 ->
                                  (fun lid ->
                                     if lid = Pulse_Reflection_Util.star_lid
                                     then
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "Pulse.Main.fst"
                                                  (Prims.of_int (158))
                                                  (Prims.of_int (20))
                                                  (Prims.of_int (158))
                                                  (Prims.of_int (39)))
                                               (FStar_Range.mk_range
                                                  "Pulse.Main.fst"
                                                  (Prims.of_int (158))
                                                  (Prims.of_int (11))
                                                  (Prims.of_int (160))
                                                  (Prims.of_int (31)))
                                               (Obj.magic
                                                  (translate_vprop g l))
                                               (fun uu___3 ->
                                                  (fun uu___3 ->
                                                     Obj.magic
                                                       (op_let_Question
                                                          uu___3
                                                          (fun l1 ->
                                                             FStar_Tactics_Effect.tac_bind
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Main.fst"
                                                                  (Prims.of_int (159))
                                                                  (Prims.of_int (20))
                                                                  (Prims.of_int (159))
                                                                  (Prims.of_int (39)))
                                                               (FStar_Range.mk_range
                                                                  "Pulse.Main.fst"
                                                                  (Prims.of_int (159))
                                                                  (Prims.of_int (11))
                                                                  (Prims.of_int (160))
                                                                  (Prims.of_int (31)))
                                                               (Obj.magic
                                                                  (translate_vprop
                                                                    g r))
                                                               (fun uu___4 ->
                                                                  (fun uu___4
                                                                    ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___4
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun r1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Inl
                                                                    (mk_star
                                                                    [l1; r1]))))
                                                                    uu___5)))
                                                                    uu___4))))
                                                    uu___3)))
                                     else
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___4 ->
                                                  FStar_Pervasives.Inr
                                                    "Not a star")))) uu___3)))
                   | uu___1 ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 ->
                                  FStar_Pervasives.Inr "Not a star")))))
             uu___)
and (translate_pure :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      (Pulse_Syntax_Base.term err, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (166))
           (Prims.of_int (19)) (Prims.of_int (166)) (Prims.of_int (32)))
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (166))
           (Prims.of_int (3)) (Prims.of_int (173)) (Prims.of_int (28)))
        (Obj.magic (FStar_Tactics_SyntaxHelpers.collect_app t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (hd, args) ->
                  (match ((FStar_Reflection_Builtins.inspect_ln hd), args)
                   with
                   | (FStar_Reflection_Data.Tv_FVar fv, (p, uu___1)::[]) ->
                       Obj.magic
                         (Obj.repr
                            (if
                               (FStar_Reflection_Builtins.inspect_fv fv) =
                                 Pulse_Reflection_Util.pure_lid
                             then
                               Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "Pulse.Main.fst"
                                       (Prims.of_int (170))
                                       (Prims.of_int (20))
                                       (Prims.of_int (170))
                                       (Prims.of_int (35)))
                                    (FStar_Range.mk_range "Pulse.Main.fst"
                                       (Prims.of_int (170))
                                       (Prims.of_int (11))
                                       (Prims.of_int (171))
                                       (Prims.of_int (26)))
                                    (Obj.magic (readback_ty g p))
                                    (fun uu___2 ->
                                       (fun uu___2 ->
                                          Obj.magic
                                            (op_let_Question uu___2
                                               (fun uu___3 ->
                                                  (fun p1 ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___3 ->
                                                             FStar_Pervasives.Inl
                                                               (Pulse_Syntax_Base.Tm_Pure
                                                                  p1))))
                                                    uu___3))) uu___2))
                             else
                               Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___3 ->
                                       FStar_Pervasives.Inr "Not a pure"))))
                   | uu___1 ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 ->
                                  FStar_Pervasives.Inr "Not a pure")))))
             uu___)
and (translate_vprop_list :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term Prims.list ->
      (Pulse_Syntax_Base.term Prims.list err, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun l ->
           match l with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> FStar_Pervasives.Inl [])))
           | hd::tl ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (179)) (Prims.of_int (14))
                          (Prims.of_int (179)) (Prims.of_int (34)))
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (179)) (Prims.of_int (4))
                          (Prims.of_int (181)) (Prims.of_int (16)))
                       (Obj.magic (translate_vprop g hd))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (op_let_Question uu___
                                  (fun hd1 ->
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range "Pulse.Main.fst"
                                          (Prims.of_int (180))
                                          (Prims.of_int (14))
                                          (Prims.of_int (180))
                                          (Prims.of_int (39)))
                                       (FStar_Range.mk_range "Pulse.Main.fst"
                                          (Prims.of_int (180))
                                          (Prims.of_int (4))
                                          (Prims.of_int (181))
                                          (Prims.of_int (16)))
                                       (Obj.magic (translate_vprop_list g tl))
                                       (fun uu___1 ->
                                          (fun uu___1 ->
                                             Obj.magic
                                               (op_let_Question uu___1
                                                  (fun uu___2 ->
                                                     (fun tl1 ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___2 ->
                                                                FStar_Pervasives.Inl
                                                                  (hd1 ::
                                                                  tl1))))
                                                       uu___2))) uu___1))))
                            uu___)))) uu___1 uu___
let (readback_comp :
  FStar_Reflection_Types.term ->
    (Pulse_Syntax_Base.comp err, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Derived.try_with
      (fun uu___ ->
         (fun uu___ ->
            match () with
            | () ->
                (match Pulse_Readback.readback_comp t with
                 | FStar_Pervasives_Native.None ->
                     Obj.magic (Obj.repr (unexpected_term "computation" t))
                 | FStar_Pervasives_Native.Some c ->
                     Obj.magic
                       (Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 -> FStar_Pervasives.Inl c))))) uu___)
      (fun uu___ ->
         match uu___ with
         | FStar_Tactics_Common.TacticFailure msg -> unexpected_term msg t
         | uu___1 -> unexpected_term "readback failed" t)
let (translate_bv_ty_as_binder :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.bv ->
      FStar_Reflection_Types.term -> Pulse_Syntax_Base.binder)
  =
  fun g ->
    fun x ->
      fun sort ->
        let bv_view = FStar_Reflection_Builtins.inspect_bv x in
        let b_ty' = readback_maybe_unknown_ty sort in
        {
          Pulse_Syntax_Base.binder_ty = b_ty';
          Pulse_Syntax_Base.binder_ppname =
            (bv_view.FStar_Reflection_Data.bv_ppname)
        }
let (translate_binder :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.binder ->
      ((Pulse_Syntax_Base.binder * Pulse_Syntax_Base.qualifier
         FStar_Pervasives_Native.option) err,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun b ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (204))
           (Prims.of_int (8)) (Prims.of_int (204)) (Prims.of_int (26)))
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (203))
           (Prims.of_int (3)) (Prims.of_int (212)) (Prims.of_int (16)))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> FStar_Reflection_Builtins.inspect_binder b))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | { FStar_Reflection_Data.binder_bv = bv;
                  FStar_Reflection_Data.binder_qual = aq;
                  FStar_Reflection_Data.binder_attrs = attrs;
                  FStar_Reflection_Data.binder_sort = sort;_} ->
                  (match (attrs, aq) with
                   | (uu___1::uu___2, uu___3) ->
                       Obj.magic (Obj.repr (error "Unexpected attribute"))
                   | (uu___1, FStar_Reflection_Data.Q_Meta uu___2) ->
                       Obj.magic
                         (Obj.repr (error "Unexpected binder qualifier"))
                   | uu___1 ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 ->
                                  FStar_Pervasives.Inl
                                    ((translate_bv_ty_as_binder g bv sort),
                                      (Pulse_Readback.readback_qual aq)))))))
             uu___)
let (is_head_fv :
  FStar_Reflection_Types.term ->
    Prims.string Prims.list ->
      (FStar_Reflection_Data.argv Prims.list FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun fv ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (215))
           (Prims.of_int (19)) (Prims.of_int (215)) (Prims.of_int (34)))
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (214))
           (Prims.of_int (75)) (Prims.of_int (221)) (Prims.of_int (13)))
        (Obj.magic (FStar_Tactics_SyntaxHelpers.collect_app t))
        (fun uu___ ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                match uu___ with
                | (head, args) ->
                    (match FStar_Reflection_Builtins.inspect_ln head with
                     | FStar_Reflection_Data.Tv_FVar fv' ->
                         if (FStar_Reflection_Builtins.inspect_fv fv') = fv
                         then FStar_Pervasives_Native.Some args
                         else FStar_Pervasives_Native.None
                     | uu___2 -> FStar_Pervasives_Native.None)))
let (mk_tests_lid : Prims.string -> Prims.string Prims.list) =
  fun s -> ["Tests"; "Common"; s]
let (expects_fv : Prims.string Prims.list) = mk_tests_lid "expects"
let (provides_fv : Prims.string Prims.list) = mk_tests_lid "provides"
let (intro_fv : Prims.string Prims.list) = mk_tests_lid "intro"
let (elim_fv : Prims.string Prims.list) = mk_tests_lid "elim"
let (while_fv : Prims.string Prims.list) = mk_tests_lid "while"
let (invariant_fv : Prims.string Prims.list) = mk_tests_lid "invariant"
let (par_fv : Prims.string Prims.list) = mk_tests_lid "par"
let (rewrite_fv : Prims.string Prims.list) = mk_tests_lid "rewrite"
let (local_fv : Prims.string Prims.list) = mk_tests_lid "local"
let (tot_fv : Prims.string Prims.list) = mk_tests_lid "tot"
let rec (shift_bvs_in_tm_fstar :
  Pulse_Syntax_Base.host_term ->
    Prims.nat ->
      (Pulse_Syntax_Base.host_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun t ->
         fun n ->
           match FStar_Reflection_Builtins.inspect_ln t with
           | FStar_Reflection_Data.Tv_BVar bv ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          if
                            n <
                              (FStar_Reflection_Builtins.inspect_bv bv).FStar_Reflection_Data.bv_index
                          then
                            FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_BVar
                                 (FStar_Reflection_Builtins.pack_bv
                                    {
                                      FStar_Reflection_Data.bv_ppname =
                                        ((FStar_Reflection_Builtins.inspect_bv
                                            bv).FStar_Reflection_Data.bv_ppname);
                                      FStar_Reflection_Data.bv_index =
                                        ((FStar_Reflection_Builtins.inspect_bv
                                            bv).FStar_Reflection_Data.bv_index
                                           - Prims.int_one)
                                    }))
                          else t)))
           | FStar_Reflection_Data.Tv_App (head, (arg, q)) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (245)) (Prims.of_int (14))
                          (Prims.of_int (245)) (Prims.of_int (36)))
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (246)) (Prims.of_int (4))
                          (Prims.of_int (253)) (Prims.of_int (36)))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ ->
                             FStar_Reflection_Builtins.pack_ln
                               FStar_Reflection_Data.Tv_Unknown))
                       (fun uu___ ->
                          (fun unk ->
                             if
                               (FStar_Reflection_Builtins.term_eq head unk)
                                 ||
                                 (FStar_Reflection_Builtins.term_eq arg unk)
                             then
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Derived.fail
                                       "Unknown in Tm_FStar"))
                             else
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range "Pulse.Main.fst"
                                          (Prims.of_int (251))
                                          (Prims.of_int (17))
                                          (Prims.of_int (251))
                                          (Prims.of_int (45)))
                                       (FStar_Range.mk_range "Pulse.Main.fst"
                                          (Prims.of_int (251))
                                          (Prims.of_int (48))
                                          (Prims.of_int (253))
                                          (Prims.of_int (36)))
                                       (Obj.magic
                                          (shift_bvs_in_tm_fstar head n))
                                       (fun uu___1 ->
                                          (fun head1 ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Range.mk_range
                                                     "Pulse.Main.fst"
                                                     (Prims.of_int (252))
                                                     (Prims.of_int (16))
                                                     (Prims.of_int (252))
                                                     (Prims.of_int (43)))
                                                  (FStar_Range.mk_range
                                                     "Pulse.Main.fst"
                                                     (Prims.of_int (253))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (253))
                                                     (Prims.of_int (36)))
                                                  (Obj.magic
                                                     (shift_bvs_in_tm_fstar
                                                        arg n))
                                                  (fun arg1 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___1 ->
                                                          FStar_Reflection_Builtins.pack_ln
                                                            (FStar_Reflection_Data.Tv_App
                                                               (head1,
                                                                 (arg1, q)))))))
                                            uu___1)))) uu___)))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> t))))
        uu___1 uu___
let rec (shift_bvs_in_else :
  Pulse_Syntax_Base.term ->
    Prims.nat -> (Pulse_Syntax_Base.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun t ->
         fun n ->
           match t with
           | Pulse_Syntax_Base.Tm_Emp ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t)))
           | Pulse_Syntax_Base.Tm_Pure p ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (267)) (Prims.of_int (25))
                          (Prims.of_int (267)) (Prims.of_int (48)))
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (267)) (Prims.of_int (17))
                          (Prims.of_int (267)) (Prims.of_int (48)))
                       (Obj.magic (shift_bvs_in_else p n))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> Pulse_Syntax_Base.Tm_Pure uu___))))
           | Pulse_Syntax_Base.Tm_Star (l, r) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (269)) (Prims.of_int (12))
                          (Prims.of_int (269)) (Prims.of_int (35)))
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (269)) (Prims.of_int (4))
                          (Prims.of_int (270)) (Prims.of_int (35)))
                       (Obj.magic (shift_bvs_in_else l n))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (270)) (Prims.of_int (12))
                                     (Prims.of_int (270)) (Prims.of_int (35)))
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (269)) (Prims.of_int (4))
                                     (Prims.of_int (270)) (Prims.of_int (35)))
                                  (Obj.magic (shift_bvs_in_else r n))
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 ->
                                          Pulse_Syntax_Base.Tm_Star
                                            (uu___, uu___1))))) uu___)))
           | Pulse_Syntax_Base.Tm_ExistsSL (u, t1, body, se) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (272)) (Prims.of_int (18))
                          (Prims.of_int (272)) (Prims.of_int (41)))
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (272)) (Prims.of_int (4))
                          (Prims.of_int (274)) (Prims.of_int (20)))
                       (Obj.magic (shift_bvs_in_else t1 n))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (273)) (Prims.of_int (18))
                                     (Prims.of_int (273)) (Prims.of_int (50)))
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (272)) (Prims.of_int (4))
                                     (Prims.of_int (274)) (Prims.of_int (20)))
                                  (Obj.magic
                                     (shift_bvs_in_else body
                                        (n + Prims.int_one)))
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 ->
                                          Pulse_Syntax_Base.Tm_ExistsSL
                                            (u, uu___, uu___1, se))))) uu___)))
           | Pulse_Syntax_Base.Tm_ForallSL (u, t1, body) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (276)) (Prims.of_int (18))
                          (Prims.of_int (276)) (Prims.of_int (41)))
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (276)) (Prims.of_int (4))
                          (Prims.of_int (277)) (Prims.of_int (50)))
                       (Obj.magic (shift_bvs_in_else t1 n))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (277)) (Prims.of_int (18))
                                     (Prims.of_int (277)) (Prims.of_int (50)))
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (276)) (Prims.of_int (4))
                                     (Prims.of_int (277)) (Prims.of_int (50)))
                                  (Obj.magic
                                     (shift_bvs_in_else body
                                        (n + Prims.int_one)))
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 ->
                                          Pulse_Syntax_Base.Tm_ForallSL
                                            (u, uu___, uu___1))))) uu___)))
           | Pulse_Syntax_Base.Tm_FStar (t1, r) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (281)) (Prims.of_int (13))
                          (Prims.of_int (281)) (Prims.of_int (40)))
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (281)) (Prims.of_int (4))
                          (Prims.of_int (281)) (Prims.of_int (42)))
                       (Obj.magic (shift_bvs_in_tm_fstar t1 n))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               Pulse_Syntax_Base.Tm_FStar (uu___, r)))))
           | Pulse_Syntax_Base.Tm_VProp ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t)))
           | Pulse_Syntax_Base.Tm_Inames ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t)))
           | Pulse_Syntax_Base.Tm_EmpInames ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t)))
           | Pulse_Syntax_Base.Tm_Unknown ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> t))))
        uu___1 uu___
let (shift_bvs_in_else_opt :
  Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
    Prims.nat ->
      (Pulse_Syntax_Base.term FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun t ->
         fun n ->
           match t with
           | FStar_Pervasives_Native.None ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> FStar_Pervasives_Native.None)))
           | FStar_Pervasives_Native.Some t1 ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (292)) (Prims.of_int (21))
                          (Prims.of_int (292)) (Prims.of_int (44)))
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (292)) (Prims.of_int (16))
                          (Prims.of_int (292)) (Prims.of_int (44)))
                       (Obj.magic (shift_bvs_in_else t1 n))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> FStar_Pervasives_Native.Some uu___)))))
        uu___1 uu___
let rec (shift_bvs_in_else_list :
  Pulse_Syntax_Base.term Prims.list ->
    Prims.nat ->
      (Pulse_Syntax_Base.term Prims.list, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun t ->
         fun n ->
           match t with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> [])))
           | hd::tl ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (298)) (Prims.of_int (6))
                          (Prims.of_int (298)) (Prims.of_int (28)))
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (298)) (Prims.of_int (6))
                          (Prims.of_int (299)) (Prims.of_int (33)))
                       (Obj.magic (shift_bvs_in_else hd n))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (299)) (Prims.of_int (6))
                                     (Prims.of_int (299)) (Prims.of_int (33)))
                                  (FStar_Range.mk_range "Pulse.Main.fst"
                                     (Prims.of_int (298)) (Prims.of_int (6))
                                     (Prims.of_int (299)) (Prims.of_int (33)))
                                  (Obj.magic (shift_bvs_in_else_list tl n))
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 -> uu___ :: uu___1))))
                            uu___)))) uu___1 uu___
let (shift_bvs_in_else_binder :
  Pulse_Syntax_Base.binder ->
    Prims.nat ->
      (Pulse_Syntax_Base.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun n ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (302))
           (Prims.of_int (20)) (Prims.of_int (302)) (Prims.of_int (51)))
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (302))
           (Prims.of_int (3)) (Prims.of_int (302)) (Prims.of_int (51)))
        (Obj.magic (shift_bvs_in_else b.Pulse_Syntax_Base.binder_ty n))
        (fun uu___ ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                {
                  Pulse_Syntax_Base.binder_ty = uu___;
                  Pulse_Syntax_Base.binder_ppname =
                    (b.Pulse_Syntax_Base.binder_ppname)
                }))
let rec (shift_bvs_in_else_st :
  Pulse_Syntax_Base.st_term ->
    Prims.nat ->
      (Pulse_Syntax_Base.st_term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun n ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (306))
           (Prims.of_int (2)) (Prims.of_int (363)) (Prims.of_int (47)))
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (365))
           (Prims.of_int (4)) (Prims.of_int (365)) (Prims.of_int (30)))
        (match t.Pulse_Syntax_Base.term1 with
         | Pulse_Syntax_Base.Tm_Return
             { Pulse_Syntax_Base.ctag = ctag;
               Pulse_Syntax_Base.insert_eq = insert_eq;
               Pulse_Syntax_Base.term = term;_}
             ->
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (308)) (Prims.of_int (16))
                        (Prims.of_int (308)) (Prims.of_int (62)))
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (308)) (Prims.of_int (4))
                        (Prims.of_int (308)) (Prims.of_int (64)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (308)) (Prims.of_int (38))
                              (Prims.of_int (308)) (Prims.of_int (62)))
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (308)) (Prims.of_int (16))
                              (Prims.of_int (308)) (Prims.of_int (62)))
                           (Obj.magic (shift_bvs_in_else term n))
                           (fun uu___ ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 ->
                                   {
                                     Pulse_Syntax_Base.ctag = ctag;
                                     Pulse_Syntax_Base.insert_eq = insert_eq;
                                     Pulse_Syntax_Base.term = uu___
                                   }))))
                     (fun uu___ ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> Pulse_Syntax_Base.Tm_Return uu___))))
         | Pulse_Syntax_Base.Tm_Abs uu___ ->
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Derived.fail
                     "Did not expect an Tm_Abs in shift_bvs_in_else_st"))
         | Pulse_Syntax_Base.Tm_STApp
             { Pulse_Syntax_Base.head = head;
               Pulse_Syntax_Base.arg_qual = arg_qual;
               Pulse_Syntax_Base.arg = arg;_}
             ->
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (312)) (Prims.of_int (15))
                        (Prims.of_int (314)) (Prims.of_int (44)))
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (312)) (Prims.of_int (4))
                        (Prims.of_int (314)) (Prims.of_int (46)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (312)) (Prims.of_int (22))
                              (Prims.of_int (312)) (Prims.of_int (46)))
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (312)) (Prims.of_int (15))
                              (Prims.of_int (314)) (Prims.of_int (44)))
                           (Obj.magic (shift_bvs_in_else head n))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (314))
                                         (Prims.of_int (21))
                                         (Prims.of_int (314))
                                         (Prims.of_int (44)))
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (312))
                                         (Prims.of_int (15))
                                         (Prims.of_int (314))
                                         (Prims.of_int (44)))
                                      (Obj.magic (shift_bvs_in_else arg n))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              {
                                                Pulse_Syntax_Base.head =
                                                  uu___;
                                                Pulse_Syntax_Base.arg_qual =
                                                  arg_qual;
                                                Pulse_Syntax_Base.arg =
                                                  uu___1
                                              })))) uu___)))
                     (fun uu___ ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> Pulse_Syntax_Base.Tm_STApp uu___))))
         | Pulse_Syntax_Base.Tm_Bind
             { Pulse_Syntax_Base.binder = binder;
               Pulse_Syntax_Base.head1 = head;
               Pulse_Syntax_Base.body1 = body;_}
             ->
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (316)) (Prims.of_int (14))
                        (Prims.of_int (318)) (Prims.of_int (54)))
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (316)) (Prims.of_int (4))
                        (Prims.of_int (318)) (Prims.of_int (56)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (316)) (Prims.of_int (23))
                              (Prims.of_int (316)) (Prims.of_int (56)))
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (316)) (Prims.of_int (14))
                              (Prims.of_int (318)) (Prims.of_int (54)))
                           (Obj.magic (shift_bvs_in_else_binder binder n))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (317))
                                         (Prims.of_int (21))
                                         (Prims.of_int (317))
                                         (Prims.of_int (48)))
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (316))
                                         (Prims.of_int (14))
                                         (Prims.of_int (318))
                                         (Prims.of_int (54)))
                                      (Obj.magic
                                         (shift_bvs_in_else_st head n))
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Range.mk_range
                                                    "Pulse.Main.fst"
                                                    (Prims.of_int (318))
                                                    (Prims.of_int (21))
                                                    (Prims.of_int (318))
                                                    (Prims.of_int (54)))
                                                 (FStar_Range.mk_range
                                                    "Pulse.Main.fst"
                                                    (Prims.of_int (316))
                                                    (Prims.of_int (14))
                                                    (Prims.of_int (318))
                                                    (Prims.of_int (54)))
                                                 (Obj.magic
                                                    (shift_bvs_in_else_st
                                                       body
                                                       (n + Prims.int_one)))
                                                 (fun uu___2 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 ->
                                                         {
                                                           Pulse_Syntax_Base.binder
                                                             = uu___;
                                                           Pulse_Syntax_Base.head1
                                                             = uu___1;
                                                           Pulse_Syntax_Base.body1
                                                             = uu___2
                                                         })))) uu___1)))
                                uu___)))
                     (fun uu___ ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> Pulse_Syntax_Base.Tm_Bind uu___))))
         | Pulse_Syntax_Base.Tm_TotBind
             { Pulse_Syntax_Base.head2 = head;
               Pulse_Syntax_Base.body2 = body;_}
             ->
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (320)) (Prims.of_int (17))
                        (Prims.of_int (321)) (Prims.of_int (57)))
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (320)) (Prims.of_int (4))
                        (Prims.of_int (321)) (Prims.of_int (59)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (320)) (Prims.of_int (24))
                              (Prims.of_int (320)) (Prims.of_int (48)))
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (320)) (Prims.of_int (17))
                              (Prims.of_int (321)) (Prims.of_int (57)))
                           (Obj.magic (shift_bvs_in_else head n))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (321))
                                         (Prims.of_int (24))
                                         (Prims.of_int (321))
                                         (Prims.of_int (57)))
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (320))
                                         (Prims.of_int (17))
                                         (Prims.of_int (321))
                                         (Prims.of_int (57)))
                                      (Obj.magic
                                         (shift_bvs_in_else_st body
                                            (n + Prims.int_one)))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              {
                                                Pulse_Syntax_Base.head2 =
                                                  uu___;
                                                Pulse_Syntax_Base.body2 =
                                                  uu___1
                                              })))) uu___)))
                     (fun uu___ ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> Pulse_Syntax_Base.Tm_TotBind uu___))))
         | Pulse_Syntax_Base.Tm_If
             { Pulse_Syntax_Base.b1 = b; Pulse_Syntax_Base.then_ = then_;
               Pulse_Syntax_Base.else_ = else_;
               Pulse_Syntax_Base.post2 = post;_}
             ->
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (323)) (Prims.of_int (12))
                        (Prims.of_int (326)) (Prims.of_int (53)))
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (323)) (Prims.of_int (4))
                        (Prims.of_int (326)) (Prims.of_int (55)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (323)) (Prims.of_int (16))
                              (Prims.of_int (323)) (Prims.of_int (37)))
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (323)) (Prims.of_int (12))
                              (Prims.of_int (326)) (Prims.of_int (53)))
                           (Obj.magic (shift_bvs_in_else b n))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (324))
                                         (Prims.of_int (20))
                                         (Prims.of_int (324))
                                         (Prims.of_int (48)))
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (323))
                                         (Prims.of_int (12))
                                         (Prims.of_int (326))
                                         (Prims.of_int (53)))
                                      (Obj.magic
                                         (shift_bvs_in_else_st then_ n))
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Range.mk_range
                                                    "Pulse.Main.fst"
                                                    (Prims.of_int (325))
                                                    (Prims.of_int (20))
                                                    (Prims.of_int (325))
                                                    (Prims.of_int (48)))
                                                 (FStar_Range.mk_range
                                                    "Pulse.Main.fst"
                                                    (Prims.of_int (323))
                                                    (Prims.of_int (12))
                                                    (Prims.of_int (326))
                                                    (Prims.of_int (53)))
                                                 (Obj.magic
                                                    (shift_bvs_in_else_st
                                                       else_ n))
                                                 (fun uu___2 ->
                                                    (fun uu___2 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Range.mk_range
                                                               "Pulse.Main.fst"
                                                               (Prims.of_int (326))
                                                               (Prims.of_int (19))
                                                               (Prims.of_int (326))
                                                               (Prims.of_int (53)))
                                                            (FStar_Range.mk_range
                                                               "Pulse.Main.fst"
                                                               (Prims.of_int (323))
                                                               (Prims.of_int (12))
                                                               (Prims.of_int (326))
                                                               (Prims.of_int (53)))
                                                            (Obj.magic
                                                               (shift_bvs_in_else_opt
                                                                  post
                                                                  (n +
                                                                    Prims.int_one)))
                                                            (fun uu___3 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___4
                                                                    ->
                                                                    {
                                                                    Pulse_Syntax_Base.b1
                                                                    = uu___;
                                                                    Pulse_Syntax_Base.then_
                                                                    = uu___1;
                                                                    Pulse_Syntax_Base.else_
                                                                    = uu___2;
                                                                    Pulse_Syntax_Base.post2
                                                                    = uu___3
                                                                    }))))
                                                      uu___2))) uu___1)))
                                uu___)))
                     (fun uu___ ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> Pulse_Syntax_Base.Tm_If uu___))))
         | Pulse_Syntax_Base.Tm_ElimExists { Pulse_Syntax_Base.p = p;_} ->
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (328)) (Prims.of_int (20))
                        (Prims.of_int (328)) (Prims.of_int (45)))
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (328)) (Prims.of_int (4))
                        (Prims.of_int (328)) (Prims.of_int (47)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (328)) (Prims.of_int (24))
                              (Prims.of_int (328)) (Prims.of_int (45)))
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (328)) (Prims.of_int (20))
                              (Prims.of_int (328)) (Prims.of_int (45)))
                           (Obj.magic (shift_bvs_in_else p n))
                           (fun uu___ ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 ->
                                   { Pulse_Syntax_Base.p = uu___ }))))
                     (fun uu___ ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 ->
                             Pulse_Syntax_Base.Tm_ElimExists uu___))))
         | Pulse_Syntax_Base.Tm_IntroExists
             { Pulse_Syntax_Base.erased = erased; Pulse_Syntax_Base.p1 = p;
               Pulse_Syntax_Base.witnesses = witnesses;_}
             ->
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (330)) (Prims.of_int (21))
                        (Prims.of_int (332)) (Prims.of_int (67)))
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (330)) (Prims.of_int (4))
                        (Prims.of_int (332)) (Prims.of_int (69)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (331)) (Prims.of_int (25))
                              (Prims.of_int (331)) (Prims.of_int (46)))
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (330)) (Prims.of_int (21))
                              (Prims.of_int (332)) (Prims.of_int (67)))
                           (Obj.magic (shift_bvs_in_else p n))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (332))
                                         (Prims.of_int (33))
                                         (Prims.of_int (332))
                                         (Prims.of_int (67)))
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (330))
                                         (Prims.of_int (21))
                                         (Prims.of_int (332))
                                         (Prims.of_int (67)))
                                      (Obj.magic
                                         (shift_bvs_in_else_list witnesses n))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              {
                                                Pulse_Syntax_Base.erased =
                                                  erased;
                                                Pulse_Syntax_Base.p1 = uu___;
                                                Pulse_Syntax_Base.witnesses =
                                                  uu___1
                                              })))) uu___)))
                     (fun uu___ ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 ->
                             Pulse_Syntax_Base.Tm_IntroExists uu___))))
         | Pulse_Syntax_Base.Tm_While
             { Pulse_Syntax_Base.invariant = invariant;
               Pulse_Syntax_Base.condition = condition;
               Pulse_Syntax_Base.body3 = body;_}
             ->
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (334)) (Prims.of_int (15))
                        (Prims.of_int (336)) (Prims.of_int (49)))
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (334)) (Prims.of_int (4))
                        (Prims.of_int (336)) (Prims.of_int (51)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (334)) (Prims.of_int (27))
                              (Prims.of_int (334)) (Prims.of_int (62)))
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (334)) (Prims.of_int (15))
                              (Prims.of_int (336)) (Prims.of_int (49)))
                           (Obj.magic
                              (shift_bvs_in_else invariant
                                 (n + Prims.int_one)))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (335))
                                         (Prims.of_int (27))
                                         (Prims.of_int (335))
                                         (Prims.of_int (59)))
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (334))
                                         (Prims.of_int (15))
                                         (Prims.of_int (336))
                                         (Prims.of_int (49)))
                                      (Obj.magic
                                         (shift_bvs_in_else_st condition n))
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Range.mk_range
                                                    "Pulse.Main.fst"
                                                    (Prims.of_int (336))
                                                    (Prims.of_int (22))
                                                    (Prims.of_int (336))
                                                    (Prims.of_int (49)))
                                                 (FStar_Range.mk_range
                                                    "Pulse.Main.fst"
                                                    (Prims.of_int (334))
                                                    (Prims.of_int (15))
                                                    (Prims.of_int (336))
                                                    (Prims.of_int (49)))
                                                 (Obj.magic
                                                    (shift_bvs_in_else_st
                                                       body n))
                                                 (fun uu___2 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 ->
                                                         {
                                                           Pulse_Syntax_Base.invariant
                                                             = uu___;
                                                           Pulse_Syntax_Base.condition
                                                             = uu___1;
                                                           Pulse_Syntax_Base.body3
                                                             = uu___2
                                                         })))) uu___1)))
                                uu___)))
                     (fun uu___ ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> Pulse_Syntax_Base.Tm_While uu___))))
         | Pulse_Syntax_Base.Tm_Par
             { Pulse_Syntax_Base.pre11 = pre1;
               Pulse_Syntax_Base.body11 = body1;
               Pulse_Syntax_Base.post11 = post1;
               Pulse_Syntax_Base.pre2 = pre2;
               Pulse_Syntax_Base.body21 = body2;
               Pulse_Syntax_Base.post21 = post2;_}
             ->
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (339)) (Prims.of_int (13))
                        (Prims.of_int (344)) (Prims.of_int (52)))
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (339)) (Prims.of_int (4))
                        (Prims.of_int (344)) (Prims.of_int (54)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (339)) (Prims.of_int (20))
                              (Prims.of_int (339)) (Prims.of_int (44)))
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (339)) (Prims.of_int (13))
                              (Prims.of_int (344)) (Prims.of_int (52)))
                           (Obj.magic (shift_bvs_in_else pre1 n))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (340))
                                         (Prims.of_int (21))
                                         (Prims.of_int (340))
                                         (Prims.of_int (49)))
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (339))
                                         (Prims.of_int (13))
                                         (Prims.of_int (344))
                                         (Prims.of_int (52)))
                                      (Obj.magic
                                         (shift_bvs_in_else_st body1 n))
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Range.mk_range
                                                    "Pulse.Main.fst"
                                                    (Prims.of_int (341))
                                                    (Prims.of_int (21))
                                                    (Prims.of_int (341))
                                                    (Prims.of_int (52)))
                                                 (FStar_Range.mk_range
                                                    "Pulse.Main.fst"
                                                    (Prims.of_int (339))
                                                    (Prims.of_int (13))
                                                    (Prims.of_int (344))
                                                    (Prims.of_int (52)))
                                                 (Obj.magic
                                                    (shift_bvs_in_else post1
                                                       (n + Prims.int_one)))
                                                 (fun uu___2 ->
                                                    (fun uu___2 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Range.mk_range
                                                               "Pulse.Main.fst"
                                                               (Prims.of_int (342))
                                                               (Prims.of_int (20))
                                                               (Prims.of_int (342))
                                                               (Prims.of_int (44)))
                                                            (FStar_Range.mk_range
                                                               "Pulse.Main.fst"
                                                               (Prims.of_int (339))
                                                               (Prims.of_int (13))
                                                               (Prims.of_int (344))
                                                               (Prims.of_int (52)))
                                                            (Obj.magic
                                                               (shift_bvs_in_else
                                                                  pre2 n))
                                                            (fun uu___3 ->
                                                               (fun uu___3 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (49)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (52)))
                                                                    (Obj.magic
                                                                    (shift_bvs_in_else_st
                                                                    body2 n))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (52)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (52)))
                                                                    (Obj.magic
                                                                    (shift_bvs_in_else
                                                                    post2
                                                                    (n +
                                                                    Prims.int_one)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    {
                                                                    Pulse_Syntax_Base.pre11
                                                                    = uu___;
                                                                    Pulse_Syntax_Base.body11
                                                                    = uu___1;
                                                                    Pulse_Syntax_Base.post11
                                                                    = uu___2;
                                                                    Pulse_Syntax_Base.pre2
                                                                    = uu___3;
                                                                    Pulse_Syntax_Base.body21
                                                                    = uu___4;
                                                                    Pulse_Syntax_Base.post21
                                                                    = uu___5
                                                                    }))))
                                                                    uu___4)))
                                                                 uu___3)))
                                                      uu___2))) uu___1)))
                                uu___)))
                     (fun uu___ ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> Pulse_Syntax_Base.Tm_Par uu___))))
         | Pulse_Syntax_Base.Tm_Rewrite
             { Pulse_Syntax_Base.t1 = t1; Pulse_Syntax_Base.t2 = t2;_} ->
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (347)) (Prims.of_int (15))
                        (Prims.of_int (348)) (Prims.of_int (40)))
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (347)) (Prims.of_int (2))
                        (Prims.of_int (348)) (Prims.of_int (42)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (347)) (Prims.of_int (20))
                              (Prims.of_int (347)) (Prims.of_int (42)))
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (347)) (Prims.of_int (15))
                              (Prims.of_int (348)) (Prims.of_int (40)))
                           (Obj.magic (shift_bvs_in_else t1 n))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (348))
                                         (Prims.of_int (18))
                                         (Prims.of_int (348))
                                         (Prims.of_int (40)))
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (347))
                                         (Prims.of_int (15))
                                         (Prims.of_int (348))
                                         (Prims.of_int (40)))
                                      (Obj.magic (shift_bvs_in_else t2 n))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              {
                                                Pulse_Syntax_Base.t1 = uu___;
                                                Pulse_Syntax_Base.t2 = uu___1
                                              })))) uu___)))
                     (fun uu___ ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> Pulse_Syntax_Base.Tm_Rewrite uu___))))
         | Pulse_Syntax_Base.Tm_WithLocal
             { Pulse_Syntax_Base.initializer1 = initializer1;
               Pulse_Syntax_Base.body4 = body;_}
             ->
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (351)) (Prims.of_int (19))
                        (Prims.of_int (352)) (Prims.of_int (59)))
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (351)) (Prims.of_int (4))
                        (Prims.of_int (352)) (Prims.of_int (61)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (351)) (Prims.of_int (33))
                              (Prims.of_int (351)) (Prims.of_int (64)))
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (351)) (Prims.of_int (19))
                              (Prims.of_int (352)) (Prims.of_int (59)))
                           (Obj.magic (shift_bvs_in_else initializer1 n))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (352))
                                         (Prims.of_int (26))
                                         (Prims.of_int (352))
                                         (Prims.of_int (59)))
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (351))
                                         (Prims.of_int (19))
                                         (Prims.of_int (352))
                                         (Prims.of_int (59)))
                                      (Obj.magic
                                         (shift_bvs_in_else_st body
                                            (n + Prims.int_one)))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              {
                                                Pulse_Syntax_Base.initializer1
                                                  = uu___;
                                                Pulse_Syntax_Base.body4 =
                                                  uu___1
                                              })))) uu___)))
                     (fun uu___ ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> Pulse_Syntax_Base.Tm_WithLocal uu___))))
         | Pulse_Syntax_Base.Tm_Admit
             { Pulse_Syntax_Base.ctag1 = ctag; Pulse_Syntax_Base.u1 = u;
               Pulse_Syntax_Base.typ = typ; Pulse_Syntax_Base.post3 = post;_}
             ->
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (355)) (Prims.of_int (15))
                        (Prims.of_int (360)) (Prims.of_int (71)))
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (355)) (Prims.of_int (4))
                        (Prims.of_int (360)) (Prims.of_int (73)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (356)) (Prims.of_int (21))
                              (Prims.of_int (356)) (Prims.of_int (44)))
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (355)) (Prims.of_int (15))
                              (Prims.of_int (360)) (Prims.of_int (71)))
                           (Obj.magic (shift_bvs_in_else typ n))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (358))
                                         (Prims.of_int (17))
                                         (Prims.of_int (360))
                                         (Prims.of_int (71)))
                                      (FStar_Range.mk_range "Pulse.Main.fst"
                                         (Prims.of_int (355))
                                         (Prims.of_int (15))
                                         (Prims.of_int (360))
                                         (Prims.of_int (71)))
                                      (match post with
                                       | FStar_Pervasives_Native.None ->
                                           Obj.magic
                                             (Obj.repr
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___1 ->
                                                      FStar_Pervasives_Native.None)))
                                       | FStar_Pervasives_Native.Some post1
                                           ->
                                           Obj.magic
                                             (Obj.repr
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Range.mk_range
                                                      "Pulse.Main.fst"
                                                      (Prims.of_int (360))
                                                      (Prims.of_int (38))
                                                      (Prims.of_int (360))
                                                      (Prims.of_int (70)))
                                                   (FStar_Range.mk_range
                                                      "Pulse.Main.fst"
                                                      (Prims.of_int (360))
                                                      (Prims.of_int (33))
                                                      (Prims.of_int (360))
                                                      (Prims.of_int (70)))
                                                   (Obj.magic
                                                      (shift_bvs_in_else
                                                         post1
                                                         (n + Prims.int_one)))
                                                   (fun uu___1 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           FStar_Pervasives_Native.Some
                                                             uu___1)))))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              {
                                                Pulse_Syntax_Base.ctag1 =
                                                  ctag;
                                                Pulse_Syntax_Base.u1 = u;
                                                Pulse_Syntax_Base.typ = uu___;
                                                Pulse_Syntax_Base.post3 =
                                                  uu___1
                                              })))) uu___)))
                     (fun uu___ ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> Pulse_Syntax_Base.Tm_Admit uu___))))
         | Pulse_Syntax_Base.Tm_Protect { Pulse_Syntax_Base.t = t1;_} ->
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (363)) (Prims.of_int (17))
                        (Prims.of_int (363)) (Prims.of_int (45)))
                     (FStar_Range.mk_range "Pulse.Main.fst"
                        (Prims.of_int (363)) (Prims.of_int (4))
                        (Prims.of_int (363)) (Prims.of_int (47)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (363)) (Prims.of_int (21))
                              (Prims.of_int (363)) (Prims.of_int (45)))
                           (FStar_Range.mk_range "Pulse.Main.fst"
                              (Prims.of_int (363)) (Prims.of_int (17))
                              (Prims.of_int (363)) (Prims.of_int (45)))
                           (Obj.magic (shift_bvs_in_else_st t1 n))
                           (fun uu___ ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 ->
                                   { Pulse_Syntax_Base.t = uu___ }))))
                     (fun uu___ ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> Pulse_Syntax_Base.Tm_Protect uu___)))))
        (fun t' ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                {
                  Pulse_Syntax_Base.term1 = t';
                  Pulse_Syntax_Base.range = (t.Pulse_Syntax_Base.range)
                }))
let try_seq :
  'b .
    (FStar_Reflection_Types.term ->
       ('b err, unit) FStar_Tactics_Effect.tac_repr)
      Prims.list ->
      FStar_Reflection_Types.term ->
        ('b err, unit) FStar_Tactics_Effect.tac_repr
  =
  fun fs ->
    fun x ->
      let rec aux msgs fs1 =
        match fs1 with
        | [] ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (373))
                 (Prims.of_int (14)) (Prims.of_int (373)) (Prims.of_int (86)))
              (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (373))
                 (Prims.of_int (10)) (Prims.of_int (373)) (Prims.of_int (86)))
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (FStar_Range.mk_range "Pulse.Main.fst"
                       (Prims.of_int (373)) (Prims.of_int (14))
                       (Prims.of_int (373)) (Prims.of_int (86)))
                    (FStar_Range.mk_range "Pulse.Main.fst"
                       (Prims.of_int (373)) (Prims.of_int (14))
                       (Prims.of_int (373)) (Prims.of_int (86)))
                    (Obj.magic
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Range.mk_range "Pulse.Main.fst"
                             (Prims.of_int (373)) (Prims.of_int (60))
                             (Prims.of_int (373)) (Prims.of_int (80)))
                          (FStar_Range.mk_range "FStar.Printf.fst"
                             (Prims.of_int (121)) (Prims.of_int (8))
                             (Prims.of_int (123)) (Prims.of_int (44)))
                          (Obj.magic
                             (FStar_Tactics_Builtins.term_to_string x))
                          (fun uu___ ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 ->
                                  fun x1 ->
                                    Prims.strcat
                                      (Prims.strcat "Failed to parse term "
                                         (Prims.strcat uu___ "\n"))
                                      (Prims.strcat x1 "")))))
                    (fun uu___ ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___1 -> uu___ msgs))))
              (fun uu___ ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 -> FStar_Pervasives.Inr uu___))
        | f::fs2 ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (375))
                 (Prims.of_int (17)) (Prims.of_int (375)) (Prims.of_int (20)))
              (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (375))
                 (Prims.of_int (17)) (Prims.of_int (375)) (Prims.of_int (20)))
              (Obj.magic (f x))
              (fun uu___ ->
                 (fun uu___ ->
                    match uu___ with
                    | FStar_Pervasives.Inl r ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 -> FStar_Pervasives.Inl r)))
                    | FStar_Pervasives.Inr msg ->
                        Obj.magic
                          (Obj.repr
                             (aux
                                (Prims.strcat msg (Prims.strcat " \n " msgs))
                                fs2))) uu___) in
      aux "" fs
let wr :
  'uuuuu . 'uuuuu -> Pulse_Syntax_Base.st_term' -> Pulse_Syntax_Base.st_term
  =
  fun t ->
    fun t0 ->
      {
        Pulse_Syntax_Base.term1 = t0;
        Pulse_Syntax_Base.range =
          (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (381))
             (Prims.of_int (7)) (Prims.of_int (381)) (Prims.of_int (8)))
      }
let (translate_elim :
  FStar_Reflection_Typing.fstar_top_env ->
    FStar_Reflection_Types.term ->
      (Pulse_Syntax_Base.st_term err, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun g ->
         fun t ->
           match FStar_Reflection_Builtins.inspect_ln t with
           | FStar_Reflection_Data.Tv_App (hd, (arg, uu___)) ->
               Obj.magic
                 (Obj.repr
                    (match FStar_Reflection_Builtins.inspect_ln hd with
                     | FStar_Reflection_Data.Tv_UInst (v, uu___1) ->
                         Obj.repr
                           (if
                              (FStar_Reflection_Builtins.inspect_fv v) =
                                elim_fv
                            then
                              Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range "Pulse.Main.fst"
                                      (Prims.of_int (392))
                                      (Prims.of_int (23))
                                      (Prims.of_int (392))
                                      (Prims.of_int (44)))
                                   (FStar_Range.mk_range "Pulse.Main.fst"
                                      (Prims.of_int (392))
                                      (Prims.of_int (13))
                                      (Prims.of_int (393))
                                      (Prims.of_int (48)))
                                   (Obj.magic (translate_vprop g arg))
                                   (fun uu___2 ->
                                      (fun uu___2 ->
                                         Obj.magic
                                           (op_let_Question uu___2
                                              (fun uu___3 ->
                                                 (fun ex ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            FStar_Pervasives.Inl
                                                              (wr t
                                                                 (Pulse_Syntax_Base.Tm_ElimExists
                                                                    {
                                                                    Pulse_Syntax_Base.p
                                                                    = ex
                                                                    })))))
                                                   uu___3))) uu___2))
                            else
                              Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___3 ->
                                      FStar_Pervasives.Inr
                                        "ELIM_EXISTS: Not elim_exists")))
                     | FStar_Reflection_Data.Tv_FVar v ->
                         Obj.repr
                           (if
                              (FStar_Reflection_Builtins.inspect_fv v) =
                                elim_fv
                            then
                              Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range "Pulse.Main.fst"
                                      (Prims.of_int (392))
                                      (Prims.of_int (23))
                                      (Prims.of_int (392))
                                      (Prims.of_int (44)))
                                   (FStar_Range.mk_range "Pulse.Main.fst"
                                      (Prims.of_int (392))
                                      (Prims.of_int (13))
                                      (Prims.of_int (393))
                                      (Prims.of_int (48)))
                                   (Obj.magic (translate_vprop g arg))
                                   (fun uu___1 ->
                                      (fun uu___1 ->
                                         Obj.magic
                                           (op_let_Question uu___1
                                              (fun uu___2 ->
                                                 (fun ex ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___2 ->
                                                            FStar_Pervasives.Inl
                                                              (wr t
                                                                 (Pulse_Syntax_Base.Tm_ElimExists
                                                                    {
                                                                    Pulse_Syntax_Base.p
                                                                    = ex
                                                                    })))))
                                                   uu___2))) uu___1))
                            else
                              Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 ->
                                      FStar_Pervasives.Inr
                                        "ELIM_EXISTS: Not elim_exists")))
                     | uu___1 ->
                         Obj.repr
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 ->
                                 FStar_Pervasives.Inr
                                   "ELIM_EXISTS: Not a fv application"))))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 ->
                          FStar_Pervasives.Inr
                            "ELIM_EXISTS: Not an application")))) uu___1
        uu___
let rec map_err :
  'a 'b .
    ('a -> ('b err, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list ->
        ('b Prims.list err, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun l ->
           match l with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> FStar_Pervasives.Inl [])))
           | hd::tl ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (403)) (Prims.of_int (16))
                          (Prims.of_int (403)) (Prims.of_int (20)))
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (403)) (Prims.of_int (6))
                          (Prims.of_int (405)) (Prims.of_int (20)))
                       (Obj.magic (f hd))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (op_let_Question uu___
                                  (fun hd1 ->
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range "Pulse.Main.fst"
                                          (Prims.of_int (404))
                                          (Prims.of_int (16))
                                          (Prims.of_int (404))
                                          (Prims.of_int (28)))
                                       (FStar_Range.mk_range "Pulse.Main.fst"
                                          (Prims.of_int (404))
                                          (Prims.of_int (6))
                                          (Prims.of_int (405))
                                          (Prims.of_int (20)))
                                       (Obj.magic (map_err f tl))
                                       (fun uu___1 ->
                                          (fun uu___1 ->
                                             Obj.magic
                                               (op_let_Question uu___1
                                                  (fun uu___2 ->
                                                     (fun tl1 ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___2 ->
                                                                FStar_Pervasives.Inl
                                                                  (hd1 ::
                                                                  tl1))))
                                                       uu___2))) uu___1))))
                            uu___)))) uu___1 uu___
let (translate_intro :
  FStar_Reflection_Typing.fstar_top_env ->
    FStar_Reflection_Types.term ->
      (Pulse_Syntax_Base.st_term err, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (410))
           (Prims.of_int (21)) (Prims.of_int (410)) (Prims.of_int (36)))
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (409))
           (Prims.of_int (17)) (Prims.of_int (426)) (Prims.of_int (42)))
        (Obj.magic (FStar_Tactics_SyntaxHelpers.collect_app t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (head, args) ->
                  (match FStar_Reflection_Builtins.inspect_ln head with
                   | FStar_Reflection_Data.Tv_UInst (fv, uu___1) ->
                       Obj.magic
                         (Obj.repr
                            (if
                               (FStar_Reflection_Builtins.inspect_fv fv) =
                                 intro_fv
                             then
                               Obj.repr
                                 (match args with
                                  | (exists_body, uu___2)::witnesses ->
                                      Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "Pulse.Main.fst"
                                              (Prims.of_int (417))
                                              (Prims.of_int (23))
                                              (Prims.of_int (417))
                                              (Prims.of_int (52)))
                                           (FStar_Range.mk_range
                                              "Pulse.Main.fst"
                                              (Prims.of_int (416))
                                              (Prims.of_int (44))
                                              (Prims.of_int (423))
                                              (Prims.of_int (12)))
                                           (Obj.magic
                                              (translate_vprop g exists_body))
                                           (fun uu___3 ->
                                              (fun uu___3 ->
                                                 Obj.magic
                                                   (op_let_Question uu___3
                                                      (fun ex ->
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "Pulse.Main.fst"
                                                              (Prims.of_int (418))
                                                              (Prims.of_int (22))
                                                              (Prims.of_int (418))
                                                              (Prims.of_int (71)))
                                                           (FStar_Range.mk_range
                                                              "Pulse.Main.fst"
                                                              (Prims.of_int (418))
                                                              (Prims.of_int (13))
                                                              (Prims.of_int (422))
                                                              (Prims.of_int (71)))
                                                           (Obj.magic
                                                              (map_err
                                                                 (fun uu___4
                                                                    ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (w,
                                                                    uu___5)
                                                                    ->
                                                                    readback_ty
                                                                    g w)
                                                                 witnesses))
                                                           (fun uu___4 ->
                                                              (fun uu___4 ->
                                                                 Obj.magic
                                                                   (op_let_Question
                                                                    uu___4
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun w ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match ex
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (uu___6,
                                                                    uu___7,
                                                                    uu___8,
                                                                    uu___9)
                                                                    ->
                                                                    FStar_Pervasives.Inl
                                                                    (wr t
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.erased
                                                                    = false;
                                                                    Pulse_Syntax_Base.p1
                                                                    = ex;
                                                                    Pulse_Syntax_Base.witnesses
                                                                    = w
                                                                    }))
                                                                    | 
                                                                    uu___6 ->
                                                                    FStar_Pervasives.Inr
                                                                    "INTRO: Unexpected formula, not an existential")))
                                                                    uu___5)))
                                                                uu___4))))
                                                uu___3))
                                  | uu___2 ->
                                      Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 ->
                                              FStar_Pervasives.Inr
                                                "INTRO: Wrong number of arguments to intro_exists")))
                             else
                               Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___3 ->
                                       FStar_Pervasives.Inr
                                         "INTRO: Not an intro"))))
                   | FStar_Reflection_Data.Tv_FVar fv ->
                       Obj.magic
                         (Obj.repr
                            (if
                               (FStar_Reflection_Builtins.inspect_fv fv) =
                                 intro_fv
                             then
                               Obj.repr
                                 (match args with
                                  | (exists_body, uu___1)::witnesses ->
                                      Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "Pulse.Main.fst"
                                              (Prims.of_int (417))
                                              (Prims.of_int (23))
                                              (Prims.of_int (417))
                                              (Prims.of_int (52)))
                                           (FStar_Range.mk_range
                                              "Pulse.Main.fst"
                                              (Prims.of_int (416))
                                              (Prims.of_int (44))
                                              (Prims.of_int (423))
                                              (Prims.of_int (12)))
                                           (Obj.magic
                                              (translate_vprop g exists_body))
                                           (fun uu___2 ->
                                              (fun uu___2 ->
                                                 Obj.magic
                                                   (op_let_Question uu___2
                                                      (fun ex ->
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "Pulse.Main.fst"
                                                              (Prims.of_int (418))
                                                              (Prims.of_int (22))
                                                              (Prims.of_int (418))
                                                              (Prims.of_int (71)))
                                                           (FStar_Range.mk_range
                                                              "Pulse.Main.fst"
                                                              (Prims.of_int (418))
                                                              (Prims.of_int (13))
                                                              (Prims.of_int (422))
                                                              (Prims.of_int (71)))
                                                           (Obj.magic
                                                              (map_err
                                                                 (fun uu___3
                                                                    ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (w,
                                                                    uu___4)
                                                                    ->
                                                                    readback_ty
                                                                    g w)
                                                                 witnesses))
                                                           (fun uu___3 ->
                                                              (fun uu___3 ->
                                                                 Obj.magic
                                                                   (op_let_Question
                                                                    uu___3
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun w ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match ex
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_ExistsSL
                                                                    (uu___5,
                                                                    uu___6,
                                                                    uu___7,
                                                                    uu___8)
                                                                    ->
                                                                    FStar_Pervasives.Inl
                                                                    (wr t
                                                                    (Pulse_Syntax_Base.Tm_IntroExists
                                                                    {
                                                                    Pulse_Syntax_Base.erased
                                                                    = false;
                                                                    Pulse_Syntax_Base.p1
                                                                    = ex;
                                                                    Pulse_Syntax_Base.witnesses
                                                                    = w
                                                                    }))
                                                                    | 
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Inr
                                                                    "INTRO: Unexpected formula, not an existential")))
                                                                    uu___4)))
                                                                uu___3))))
                                                uu___2))
                                  | uu___1 ->
                                      Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              FStar_Pervasives.Inr
                                                "INTRO: Wrong number of arguments to intro_exists")))
                             else
                               Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       FStar_Pervasives.Inr
                                         "INTRO: Not an intro"))))
                   | uu___1 ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 ->
                                  FStar_Pervasives.Inr
                                    "INTRO: Not an application"))))) uu___)
let (translate_admit :
  FStar_Reflection_Typing.fstar_top_env ->
    FStar_Reflection_Types.term ->
      (Pulse_Syntax_Base.st_term err, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (436))
           (Prims.of_int (13)) (Prims.of_int (436)) (Prims.of_int (17)))
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (436))
           (Prims.of_int (20)) (Prims.of_int (451)) (Prims.of_int (48)))
        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> wr t))
        (fun uu___ ->
           (fun wr1 ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Main.fst"
                      (Prims.of_int (437)) (Prims.of_int (21))
                      (Prims.of_int (437)) (Prims.of_int (36)))
                   (FStar_Range.mk_range "Pulse.Main.fst"
                      (Prims.of_int (436)) (Prims.of_int (20))
                      (Prims.of_int (451)) (Prims.of_int (48)))
                   (Obj.magic (FStar_Tactics_SyntaxHelpers.collect_app t))
                   (fun uu___ ->
                      (fun uu___ ->
                         match uu___ with
                         | (head, args) ->
                             (match ((FStar_Reflection_Builtins.inspect_ln
                                        head), args)
                              with
                              | (FStar_Reflection_Data.Tv_UInst (v, uu___1),
                                 (t1, uu___2)::[]) ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Main.fst"
                                             (Prims.of_int (441))
                                             (Prims.of_int (15))
                                             (Prims.of_int (441))
                                             (Prims.of_int (30)))
                                          (FStar_Range.mk_range
                                             "Pulse.Main.fst"
                                             (Prims.of_int (441))
                                             (Prims.of_int (6))
                                             (Prims.of_int (450))
                                             (Prims.of_int (44)))
                                          (Obj.magic (readback_ty g t1))
                                          (fun uu___3 ->
                                             (fun uu___3 ->
                                                Obj.magic
                                                  (op_let_Question uu___3
                                                     (fun uu___4 ->
                                                        (fun t2 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___4
                                                                   ->
                                                                   if
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    v) =
                                                                    Pulse_Reflection_Util.stt_admit_lid
                                                                   then
                                                                    FStar_Pervasives.Inl
                                                                    (wr1
                                                                    (Pulse_Syntax_Base.Tm_Admit
                                                                    {
                                                                    Pulse_Syntax_Base.ctag1
                                                                    =
                                                                    Pulse_Syntax_Base.STT;
                                                                    Pulse_Syntax_Base.u1
                                                                    =
                                                                    (FStar_Reflection_Builtins.pack_universe
                                                                    FStar_Reflection_Data.Uv_Unk);
                                                                    Pulse_Syntax_Base.typ
                                                                    = t2;
                                                                    Pulse_Syntax_Base.post3
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }))
                                                                   else
                                                                    if
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    v) =
                                                                    Pulse_Reflection_Util.stt_atomic_admit_lid
                                                                    then
                                                                    FStar_Pervasives.Inl
                                                                    (wr1
                                                                    (Pulse_Syntax_Base.Tm_Admit
                                                                    {
                                                                    Pulse_Syntax_Base.ctag1
                                                                    =
                                                                    Pulse_Syntax_Base.STT_Atomic;
                                                                    Pulse_Syntax_Base.u1
                                                                    =
                                                                    (FStar_Reflection_Builtins.pack_universe
                                                                    FStar_Reflection_Data.Uv_Unk);
                                                                    Pulse_Syntax_Base.typ
                                                                    = t2;
                                                                    Pulse_Syntax_Base.post3
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }))
                                                                    else
                                                                    if
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    v) =
                                                                    Pulse_Reflection_Util.stt_ghost_admit_lid
                                                                    then
                                                                    FStar_Pervasives.Inl
                                                                    (wr1
                                                                    (Pulse_Syntax_Base.Tm_Admit
                                                                    {
                                                                    Pulse_Syntax_Base.ctag1
                                                                    =
                                                                    Pulse_Syntax_Base.STT_Ghost;
                                                                    Pulse_Syntax_Base.u1
                                                                    =
                                                                    (FStar_Reflection_Builtins.pack_universe
                                                                    FStar_Reflection_Data.Uv_Unk);
                                                                    Pulse_Syntax_Base.typ
                                                                    = t2;
                                                                    Pulse_Syntax_Base.post3
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }))
                                                                    else
                                                                    FStar_Pervasives.Inr
                                                                    "ADMIT: Unknown admit flavor")))
                                                          uu___4))) uu___3)))
                              | (FStar_Reflection_Data.Tv_FVar v,
                                 (t1, uu___1)::[]) ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "Pulse.Main.fst"
                                             (Prims.of_int (441))
                                             (Prims.of_int (15))
                                             (Prims.of_int (441))
                                             (Prims.of_int (30)))
                                          (FStar_Range.mk_range
                                             "Pulse.Main.fst"
                                             (Prims.of_int (441))
                                             (Prims.of_int (6))
                                             (Prims.of_int (450))
                                             (Prims.of_int (44)))
                                          (Obj.magic (readback_ty g t1))
                                          (fun uu___2 ->
                                             (fun uu___2 ->
                                                Obj.magic
                                                  (op_let_Question uu___2
                                                     (fun uu___3 ->
                                                        (fun t2 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___3
                                                                   ->
                                                                   if
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    v) =
                                                                    Pulse_Reflection_Util.stt_admit_lid
                                                                   then
                                                                    FStar_Pervasives.Inl
                                                                    (wr1
                                                                    (Pulse_Syntax_Base.Tm_Admit
                                                                    {
                                                                    Pulse_Syntax_Base.ctag1
                                                                    =
                                                                    Pulse_Syntax_Base.STT;
                                                                    Pulse_Syntax_Base.u1
                                                                    =
                                                                    (FStar_Reflection_Builtins.pack_universe
                                                                    FStar_Reflection_Data.Uv_Unk);
                                                                    Pulse_Syntax_Base.typ
                                                                    = t2;
                                                                    Pulse_Syntax_Base.post3
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }))
                                                                   else
                                                                    if
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    v) =
                                                                    Pulse_Reflection_Util.stt_atomic_admit_lid
                                                                    then
                                                                    FStar_Pervasives.Inl
                                                                    (wr1
                                                                    (Pulse_Syntax_Base.Tm_Admit
                                                                    {
                                                                    Pulse_Syntax_Base.ctag1
                                                                    =
                                                                    Pulse_Syntax_Base.STT_Atomic;
                                                                    Pulse_Syntax_Base.u1
                                                                    =
                                                                    (FStar_Reflection_Builtins.pack_universe
                                                                    FStar_Reflection_Data.Uv_Unk);
                                                                    Pulse_Syntax_Base.typ
                                                                    = t2;
                                                                    Pulse_Syntax_Base.post3
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }))
                                                                    else
                                                                    if
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    v) =
                                                                    Pulse_Reflection_Util.stt_ghost_admit_lid
                                                                    then
                                                                    FStar_Pervasives.Inl
                                                                    (wr1
                                                                    (Pulse_Syntax_Base.Tm_Admit
                                                                    {
                                                                    Pulse_Syntax_Base.ctag1
                                                                    =
                                                                    Pulse_Syntax_Base.STT_Ghost;
                                                                    Pulse_Syntax_Base.u1
                                                                    =
                                                                    (FStar_Reflection_Builtins.pack_universe
                                                                    FStar_Reflection_Data.Uv_Unk);
                                                                    Pulse_Syntax_Base.typ
                                                                    = t2;
                                                                    Pulse_Syntax_Base.post3
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }))
                                                                    else
                                                                    FStar_Pervasives.Inr
                                                                    "ADMIT: Unknown admit flavor")))
                                                          uu___3))) uu___2)))
                              | uu___1 ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___2 ->
                                             FStar_Pervasives.Inr
                                               "ADMIT: Unrecognized application")))))
                        uu___))) uu___)
let tm_Return :
  'uuuuu .
    'uuuuu ->
      Pulse_Syntax_Base.ctag ->
        Prims.bool -> Pulse_Syntax_Base.term -> Pulse_Syntax_Base.st_term
  =
  fun t0 ->
    fun t ->
      fun b ->
        fun e ->
          wr t0
            (Pulse_Syntax_Base.Tm_Return
               {
                 Pulse_Syntax_Base.ctag = t;
                 Pulse_Syntax_Base.insert_eq = b;
                 Pulse_Syntax_Base.term = e
               })
let tm_STApp :
  'uuuuu .
    'uuuuu ->
      Pulse_Syntax_Base.term ->
        Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option ->
          Pulse_Syntax_Base.term -> Pulse_Syntax_Base.st_term
  =
  fun t0 ->
    fun h ->
      fun q ->
        fun a ->
          wr t0
            (Pulse_Syntax_Base.Tm_STApp
               {
                 Pulse_Syntax_Base.head = h;
                 Pulse_Syntax_Base.arg_qual = q;
                 Pulse_Syntax_Base.arg = a
               })
let (translate_st_app_or_return :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      (Pulse_Syntax_Base.st_term err, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (458))
           (Prims.of_int (13)) (Prims.of_int (458)) (Prims.of_int (17)))
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (458))
           (Prims.of_int (20)) (Prims.of_int (480)) (Prims.of_int (38)))
        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> wr t))
        (fun uu___ ->
           (fun wr1 ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Main.fst"
                      (Prims.of_int (459)) (Prims.of_int (20))
                      (Prims.of_int (459)) (Prims.of_int (31)))
                   (FStar_Range.mk_range "Pulse.Main.fst"
                      (Prims.of_int (459)) (Prims.of_int (34))
                      (Prims.of_int (480)) (Prims.of_int (38)))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> tm_Return t))
                   (fun uu___ ->
                      (fun tm_Return1 ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "Pulse.Main.fst"
                                 (Prims.of_int (460)) (Prims.of_int (19))
                                 (Prims.of_int (460)) (Prims.of_int (29)))
                              (FStar_Range.mk_range "Pulse.Main.fst"
                                 (Prims.of_int (461)) (Prims.of_int (4))
                                 (Prims.of_int (480)) (Prims.of_int (38)))
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___ -> tm_STApp t))
                              (fun uu___ ->
                                 (fun tm_STApp1 ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Range.mk_range
                                            "Pulse.Main.fst"
                                            (Prims.of_int (461))
                                            (Prims.of_int (13))
                                            (Prims.of_int (461))
                                            (Prims.of_int (28)))
                                         (FStar_Range.mk_range
                                            "Pulse.Main.fst"
                                            (Prims.of_int (461))
                                            (Prims.of_int (4))
                                            (Prims.of_int (480))
                                            (Prims.of_int (38)))
                                         (Obj.magic (readback_ty g t))
                                         (fun uu___ ->
                                            (fun uu___ ->
                                               Obj.magic
                                                 (op_let_Question uu___
                                                    (fun uu___1 ->
                                                       (fun t1 ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___1 ->
                                                                  match 
                                                                    Pulse_Syntax_Pure.is_pure_app
                                                                    t1
                                                                  with
                                                                  | FStar_Pervasives_Native.Some
                                                                    (head, q,
                                                                    arg) ->
                                                                    (match 
                                                                    Pulse_Syntax_Pure.is_fvar
                                                                    head
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (l,
                                                                    uu___2)
                                                                    ->
                                                                    if
                                                                    l =
                                                                    Pulse_Reflection_Util.return_stt_lid
                                                                    then
                                                                    FStar_Pervasives.Inl
                                                                    (tm_Return1
                                                                    Pulse_Syntax_Base.STT
                                                                    true arg)
                                                                    else
                                                                    if
                                                                    l =
                                                                    Pulse_Reflection_Util.return_stt_noeq_lid
                                                                    then
                                                                    FStar_Pervasives.Inl
                                                                    (tm_Return1
                                                                    Pulse_Syntax_Base.STT
                                                                    false arg)
                                                                    else
                                                                    if
                                                                    l =
                                                                    Pulse_Reflection_Util.return_stt_atomic_lid
                                                                    then
                                                                    FStar_Pervasives.Inl
                                                                    (tm_Return1
                                                                    Pulse_Syntax_Base.STT_Atomic
                                                                    true arg)
                                                                    else
                                                                    if
                                                                    l =
                                                                    Pulse_Reflection_Util.return_stt_atomic_noeq_lid
                                                                    then
                                                                    FStar_Pervasives.Inl
                                                                    (tm_Return1
                                                                    Pulse_Syntax_Base.STT_Atomic
                                                                    false arg)
                                                                    else
                                                                    if
                                                                    l =
                                                                    Pulse_Reflection_Util.return_stt_ghost_lid
                                                                    then
                                                                    FStar_Pervasives.Inl
                                                                    (tm_Return1
                                                                    Pulse_Syntax_Base.STT_Ghost
                                                                    true arg)
                                                                    else
                                                                    if
                                                                    l =
                                                                    Pulse_Reflection_Util.return_stt_ghost_noeq_lid
                                                                    then
                                                                    FStar_Pervasives.Inl
                                                                    (tm_Return1
                                                                    Pulse_Syntax_Base.STT_Ghost
                                                                    false arg)
                                                                    else
                                                                    FStar_Pervasives.Inl
                                                                    (tm_STApp1
                                                                    head q
                                                                    arg)
                                                                    | 
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Inl
                                                                    (tm_STApp1
                                                                    head q
                                                                    arg))
                                                                  | uu___2 ->
                                                                    FStar_Pervasives.Inl
                                                                    (tm_Return1
                                                                    Pulse_Syntax_Base.STT
                                                                    false t1))))
                                                         uu___1))) uu___)))
                                   uu___))) uu___))) uu___)
let rec (translate_term' :
  FStar_Reflection_Typing.fstar_top_env ->
    FStar_Reflection_Types.term ->
      (Pulse_Syntax_Base.st_term err, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (484))
           (Prims.of_int (35)) (Prims.of_int (484)) (Prims.of_int (72)))
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (485))
           (Prims.of_int (4)) (Prims.of_int (539)) (Prims.of_int (41)))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              fun b ->
                fun q ->
                  fun pre ->
                    fun body ->
                      fun post ->
                        wr t
                          (Pulse_Syntax_Base.Tm_Abs
                             {
                               Pulse_Syntax_Base.b = b;
                               Pulse_Syntax_Base.q = q;
                               Pulse_Syntax_Base.pre1 = pre;
                               Pulse_Syntax_Base.body = body;
                               Pulse_Syntax_Base.post1 = post
                             })))
        (fun uu___ ->
           (fun tm_Abs ->
              match FStar_Reflection_Builtins.inspect_ln t with
              | FStar_Reflection_Data.Tv_Abs (x, body) ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (487)) (Prims.of_int (18))
                          (Prims.of_int (487)) (Prims.of_int (38)))
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (486)) (Prims.of_int (25))
                          (Prims.of_int (536)) (Prims.of_int (5)))
                       (Obj.magic (translate_binder g x))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (op_let_Question uu___
                                  (fun uu___1 ->
                                     match uu___1 with
                                     | (b, q) ->
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "Pulse.Main.fst"
                                              (Prims.of_int (489))
                                              (Prims.of_int (8))
                                              (Prims.of_int (490))
                                              (Prims.of_int (48)))
                                           (FStar_Range.mk_range
                                              "Pulse.Main.fst"
                                              (Prims.of_int (492))
                                              (Prims.of_int (6))
                                              (Prims.of_int (535))
                                              (Prims.of_int (14)))
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 fun uu___3 ->
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "Pulse.Main.fst"
                                                        (Prims.of_int (489))
                                                        (Prims.of_int (20))
                                                        (Prims.of_int (489))
                                                        (Prims.of_int (41)))
                                                     (FStar_Range.mk_range
                                                        "Pulse.Main.fst"
                                                        (Prims.of_int (489))
                                                        (Prims.of_int (8))
                                                        (Prims.of_int (490))
                                                        (Prims.of_int (48)))
                                                     (Obj.magic
                                                        (translate_term g
                                                           body))
                                                     (fun uu___4 ->
                                                        (fun uu___4 ->
                                                           Obj.magic
                                                             (op_let_Question
                                                                uu___4
                                                                (fun uu___5
                                                                   ->
                                                                   (fun body1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Inl
                                                                    (tm_Abs b
                                                                    q
                                                                    (FStar_Pervasives_Native.Some
                                                                    Pulse_Syntax_Base.Tm_Emp)
                                                                    body1
                                                                    FStar_Pervasives_Native.None))))
                                                                    uu___5)))
                                                          uu___4)))
                                           (fun uu___2 ->
                                              (fun aux ->
                                                 match FStar_Reflection_Builtins.inspect_ln
                                                         body
                                                 with
                                                 | FStar_Reflection_Data.Tv_AscribedT
                                                     (body1, t1,
                                                      FStar_Pervasives_Native.None,
                                                      false)
                                                     ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Range.mk_range
                                                             "Pulse.Main.fst"
                                                             (Prims.of_int (494))
                                                             (Prims.of_int (15))
                                                             (Prims.of_int (494))
                                                             (Prims.of_int (30)))
                                                          (FStar_Range.mk_range
                                                             "Pulse.Main.fst"
                                                             (Prims.of_int (494))
                                                             (Prims.of_int (15))
                                                             (Prims.of_int (494))
                                                             (Prims.of_int (30)))
                                                          (Obj.magic
                                                             (readback_comp
                                                                t1))
                                                          (fun uu___2 ->
                                                             (fun uu___2 ->
                                                                Obj.magic
                                                                  (op_let_Question
                                                                    uu___2
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.C_ST
                                                                    st ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (496))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (496))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (496))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (60)))
                                                                    (Obj.magic
                                                                    (translate_st_term
                                                                    g body1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___4
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    body2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Inl
                                                                    (tm_Abs b
                                                                    q
                                                                    (FStar_Pervasives_Native.Some
                                                                    (st.Pulse_Syntax_Base.pre))
                                                                    body2
                                                                    (FStar_Pervasives_Native.Some
                                                                    (st.Pulse_Syntax_Base.post))))))
                                                                    uu___5)))
                                                                    uu___4)
                                                                    | 
                                                                    uu___4 ->
                                                                    aux ())))
                                                               uu___2))
                                                 | FStar_Reflection_Data.Tv_App
                                                     (uu___2, uu___3) ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Range.mk_range
                                                             "Pulse.Main.fst"
                                                             (Prims.of_int (503))
                                                             (Prims.of_int (14))
                                                             (Prims.of_int (503))
                                                             (Prims.of_int (40)))
                                                          (FStar_Range.mk_range
                                                             "Pulse.Main.fst"
                                                             (Prims.of_int (502))
                                                             (Prims.of_int (25))
                                                             (Prims.of_int (532))
                                                             (Prims.of_int (7)))
                                                          (Obj.magic
                                                             (is_head_fv body
                                                                expects_fv))
                                                          (fun uu___4 ->
                                                             (fun uu___4 ->
                                                                match uu___4
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (aux ())
                                                                | FStar_Pervasives_Native.Some
                                                                    args ->
                                                                    (
                                                                    match args
                                                                    with
                                                                    | 
                                                                    (expects_arg,
                                                                    uu___5)::
                                                                    (provides,
                                                                    uu___6)::
                                                                    (body1,
                                                                    uu___7)::[]
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (508))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (508))
                                                                    (Prims.of_int (49)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (507))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (is_head_fv
                                                                    provides
                                                                    provides_fv))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    ((provides_arg,
                                                                    uu___9)::[])
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (54)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (58)))
                                                                    (Obj.magic
                                                                    (translate_vprop
                                                                    g
                                                                    expects_arg))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___10
                                                                    (fun pre
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (84)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (58)))
                                                                    (match 
                                                                    FStar_Reflection_Builtins.inspect_ln
                                                                    provides_arg
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Abs
                                                                    (uu___11,
                                                                    provides_body)
                                                                    ->
                                                                    Obj.magic
                                                                    (translate_vprop
                                                                    g
                                                                    provides_body)
                                                                    | 
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (unexpected_term
                                                                    "'provides' should be an abstraction"
                                                                    provides_arg))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___11
                                                                    (fun post
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (518))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (518))
                                                                    (Prims.of_int (50)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (518))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (58)))
                                                                    (Obj.magic
                                                                    (translate_st_term
                                                                    g body1))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___12
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    body2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pervasives.Inl
                                                                    (tm_Abs b
                                                                    q
                                                                    (FStar_Pervasives_Native.Some
                                                                    pre)
                                                                    body2
                                                                    (FStar_Pervasives_Native.Some
                                                                    post)))))
                                                                    uu___13)))
                                                                    uu___12))))
                                                                    uu___11))))
                                                                    uu___10))
                                                                    | 
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (aux ()))
                                                                    uu___8))
                                                                    | 
                                                                    (expects_arg,
                                                                    uu___5)::
                                                                    (body1,
                                                                    uu___6)::[]
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (525))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (525))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (528))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (readback_ty
                                                                    g
                                                                    expects_arg))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___7
                                                                    (fun pre
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (526))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (526))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (526))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (527))
                                                                    (Prims.of_int (49)))
                                                                    (Obj.magic
                                                                    (translate_st_term
                                                                    g body1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___8
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    body2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pervasives.Inl
                                                                    (tm_Abs b
                                                                    q
                                                                    (FStar_Pervasives_Native.Some
                                                                    pre)
                                                                    body2
                                                                    FStar_Pervasives_Native.None))))
                                                                    uu___9)))
                                                                    uu___8))))
                                                                    uu___7))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (aux ())))
                                                               uu___4))
                                                 | uu___2 ->
                                                     Obj.magic (aux ()))
                                                uu___2)))) uu___))
              | uu___ -> Obj.magic (unexpected_term "translate_term'" t))
             uu___)
and (translate_st_term :
  FStar_Reflection_Typing.fstar_top_env ->
    FStar_Reflection_Types.term ->
      (Pulse_Syntax_Base.st_term err, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      match FStar_Reflection_Builtins.inspect_ln t with
      | FStar_Reflection_Data.Tv_Const uu___ ->
          translate_st_app_or_return g t
      | FStar_Reflection_Data.Tv_App (uu___, uu___1) ->
          try_seq
            [translate_elim g;
            translate_intro g;
            translate_while g;
            translate_par g;
            translate_admit g;
            translate_rewrite g;
            translate_st_app_or_return g] t
      | FStar_Reflection_Data.Tv_Let (false, [], bv, ty, def, body) ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (559))
               (Prims.of_int (8)) (Prims.of_int (566)) (Prims.of_int (25)))
            (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (568))
               (Prims.of_int (6)) (Prims.of_int (588)) (Prims.of_int (15)))
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___ ->
                  fun def1 ->
                    fun qual_fv ->
                      match FStar_Reflection_Builtins.inspect_ln def1 with
                      | FStar_Reflection_Data.Tv_App (hd, arg) ->
                          (match FStar_Reflection_Builtins.inspect_ln hd with
                           | FStar_Reflection_Data.Tv_FVar fv ->
                               if
                                 (FStar_Reflection_Builtins.inspect_fv fv) =
                                   qual_fv
                               then (true, (FStar_Pervasives_Native.fst arg))
                               else (false, def1)
                           | uu___1 -> (false, def1))
                      | uu___1 -> (false, def1)))
            (fun uu___ ->
               (fun def_has_qual ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (568)) (Prims.of_int (18))
                          (Prims.of_int (568)) (Prims.of_int (42)))
                       (FStar_Range.mk_range "Pulse.Main.fst"
                          (Prims.of_int (568)) (Prims.of_int (6))
                          (Prims.of_int (588)) (Prims.of_int (15)))
                       (Obj.magic (translate_st_term g body))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (op_let_Question uu___
                                  (fun body1 ->
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range "Pulse.Main.fst"
                                          (Prims.of_int (569))
                                          (Prims.of_int (14))
                                          (Prims.of_int (569))
                                          (Prims.of_int (47)))
                                       (FStar_Range.mk_range "Pulse.Main.fst"
                                          (Prims.of_int (569))
                                          (Prims.of_int (50))
                                          (Prims.of_int (588))
                                          (Prims.of_int (15)))
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 ->
                                             translate_bv_ty_as_binder g bv
                                               ty))
                                       (fun uu___1 ->
                                          (fun b ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Range.mk_range
                                                     "Pulse.Main.fst"
                                                     (Prims.of_int (570))
                                                     (Prims.of_int (25))
                                                     (Prims.of_int (570))
                                                     (Prims.of_int (50)))
                                                  (FStar_Range.mk_range
                                                     "Pulse.Main.fst"
                                                     (Prims.of_int (569))
                                                     (Prims.of_int (50))
                                                     (Prims.of_int (588))
                                                     (Prims.of_int (15)))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___1 ->
                                                        def_has_qual def
                                                          local_fv))
                                                  (fun uu___1 ->
                                                     (fun uu___1 ->
                                                        match uu___1 with
                                                        | (has_mut, def1) ->
                                                            if has_mut
                                                            then
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (39)))
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (62)))
                                                                   (Obj.magic
                                                                    (readback_ty
                                                                    g def1))
                                                                   (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___2
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun def2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives.Inl
                                                                    (wr t
                                                                    (Pulse_Syntax_Base.Tm_WithLocal
                                                                    {
                                                                    Pulse_Syntax_Base.initializer1
                                                                    = def2;
                                                                    Pulse_Syntax_Base.body4
                                                                    = body1
                                                                    })))))
                                                                    uu___3)))
                                                                    uu___2))
                                                            else
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (574))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (574))
                                                                    (Prims.of_int (53)))
                                                                   (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (574))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (15)))
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    def_has_qual
                                                                    def1
                                                                    tot_fv))
                                                                   (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (has_tot,
                                                                    def2) ->
                                                                    if
                                                                    has_tot
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (44)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (577))
                                                                    (Prims.of_int (55)))
                                                                    (Obj.magic
                                                                    (readback_ty
                                                                    g def2))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___4
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun def3
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Inl
                                                                    (wr t
                                                                    (Pulse_Syntax_Base.Tm_TotBind
                                                                    {
                                                                    Pulse_Syntax_Base.head2
                                                                    = def3;
                                                                    Pulse_Syntax_Base.body2
                                                                    = body1
                                                                    })))))
                                                                    uu___5)))
                                                                    uu___4))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (578))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (578))
                                                                    (Prims.of_int (50)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (578))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (15)))
                                                                    (Obj.magic
                                                                    (translate_st_term
                                                                    g def2))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___5
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun def3
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match 
                                                                    def3.Pulse_Syntax_Base.term1
                                                                    with
                                                                    | 
                                                                    Pulse_Syntax_Base.Tm_IntroExists
                                                                    uu___7 ->
                                                                    FStar_Pervasives.Inl
                                                                    (wr t
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    =
                                                                    (wr t
                                                                    (Pulse_Syntax_Base.Tm_Protect
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    = def3
                                                                    }));
                                                                    Pulse_Syntax_Base.body1
                                                                    =
                                                                    (wr t
                                                                    (Pulse_Syntax_Base.Tm_Protect
                                                                    {
                                                                    Pulse_Syntax_Base.t
                                                                    = body1
                                                                    }))
                                                                    }))
                                                                    | 
                                                                    uu___7 ->
                                                                    FStar_Pervasives.Inl
                                                                    (wr t
                                                                    (Pulse_Syntax_Base.Tm_Bind
                                                                    {
                                                                    Pulse_Syntax_Base.binder
                                                                    = b;
                                                                    Pulse_Syntax_Base.head1
                                                                    = def3;
                                                                    Pulse_Syntax_Base.body1
                                                                    = body1
                                                                    })))))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___3)))
                                                       uu___1))) uu___1))))
                            uu___))) uu___)
      | FStar_Reflection_Data.Tv_Match
          (b, uu___,
           (FStar_Reflection_Data.Pat_Constant
            (FStar_Reflection_Data.C_True), then_)::(FStar_Reflection_Data.Pat_Var
                                                     (uu___1, uu___2), else_)::[])
          ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (592))
               (Prims.of_int (15)) (Prims.of_int (592)) (Prims.of_int (63)))
            (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (592))
               (Prims.of_int (6)) (Prims.of_int (596)) (Prims.of_int (54)))
            (Obj.magic
               (readback_ty g
                  (FStar_Reflection_Builtins.pack_ln
                     (FStar_Reflection_Derived.inspect_ln_unascribe b))))
            (fun uu___3 ->
               (fun uu___3 ->
                  Obj.magic
                    (op_let_Question uu___3
                       (fun b1 ->
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range "Pulse.Main.fst"
                               (Prims.of_int (593)) (Prims.of_int (19))
                               (Prims.of_int (593)) (Prims.of_int (44)))
                            (FStar_Range.mk_range "Pulse.Main.fst"
                               (Prims.of_int (593)) (Prims.of_int (6))
                               (Prims.of_int (596)) (Prims.of_int (54)))
                            (Obj.magic (translate_st_term g then_))
                            (fun uu___4 ->
                               (fun uu___4 ->
                                  Obj.magic
                                    (op_let_Question uu___4
                                       (fun then_1 ->
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "Pulse.Main.fst"
                                               (Prims.of_int (594))
                                               (Prims.of_int (19))
                                               (Prims.of_int (594))
                                               (Prims.of_int (44)))
                                            (FStar_Range.mk_range
                                               "Pulse.Main.fst"
                                               (Prims.of_int (594))
                                               (Prims.of_int (6))
                                               (Prims.of_int (596))
                                               (Prims.of_int (54)))
                                            (Obj.magic
                                               (translate_st_term g else_))
                                            (fun uu___5 ->
                                               (fun uu___5 ->
                                                  Obj.magic
                                                    (op_let_Question uu___5
                                                       (fun else_1 ->
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Range.mk_range
                                                               "Pulse.Main.fst"
                                                               (Prims.of_int (595))
                                                               (Prims.of_int (18))
                                                               (Prims.of_int (595))
                                                               (Prims.of_int (46)))
                                                            (FStar_Range.mk_range
                                                               "Pulse.Main.fst"
                                                               (Prims.of_int (596))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (596))
                                                               (Prims.of_int (54)))
                                                            (Obj.magic
                                                               (shift_bvs_in_else_st
                                                                  else_1
                                                                  Prims.int_zero))
                                                            (fun else_2 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___6
                                                                    ->
                                                                    FStar_Pervasives.Inl
                                                                    (wr t
                                                                    (Pulse_Syntax_Base.Tm_If
                                                                    {
                                                                    Pulse_Syntax_Base.b1
                                                                    = b1;
                                                                    Pulse_Syntax_Base.then_
                                                                    = then_1;
                                                                    Pulse_Syntax_Base.else_
                                                                    = else_2;
                                                                    Pulse_Syntax_Base.post2
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })))))))
                                                 uu___5)))) uu___4)))) uu___3)
      | uu___ -> unexpected_term "st_term" t
and (translate_term :
  FStar_Reflection_Typing.fstar_top_env ->
    FStar_Reflection_Types.term ->
      (Pulse_Syntax_Base.st_term err, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t0 ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (603))
           (Prims.of_int (10)) (Prims.of_int (603)) (Prims.of_int (26)))
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (603))
           (Prims.of_int (4)) (Prims.of_int (605)) (Prims.of_int (31)))
        (Obj.magic (readback_ty g t0))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Pervasives.Inl t ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 ->
                             FStar_Pervasives.Inl
                               (tm_Return t0 Pulse_Syntax_Base.STT false t))))
              | uu___1 -> Obj.magic (Obj.repr (translate_term' g t0))) uu___)
and (translate_while :
  FStar_Reflection_Typing.fstar_top_env ->
    FStar_Reflection_Types.term ->
      (Pulse_Syntax_Base.st_term err, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (610))
           (Prims.of_int (21)) (Prims.of_int (610)) (Prims.of_int (36)))
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (609))
           (Prims.of_int (17)) (Prims.of_int (639)) (Prims.of_int (50)))
        (Obj.magic (FStar_Tactics_SyntaxHelpers.collect_app t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (head, args) ->
                  (match FStar_Reflection_Builtins.inspect_ln head with
                   | FStar_Reflection_Data.Tv_FVar v ->
                       Obj.magic
                         (Obj.repr
                            (if
                               (FStar_Reflection_Builtins.inspect_fv v) =
                                 while_fv
                             then
                               Obj.repr
                                 (match args with
                                  | (inv, uu___1)::(cond, uu___2)::(body,
                                                                    uu___3)::[]
                                      ->
                                      Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "Pulse.Main.fst"
                                              (Prims.of_int (616))
                                              (Prims.of_int (23))
                                              (Prims.of_int (632))
                                              (Prims.of_int (79)))
                                           (FStar_Range.mk_range
                                              "Pulse.Main.fst"
                                              (Prims.of_int (616))
                                              (Prims.of_int (13))
                                              (Prims.of_int (636))
                                              (Prims.of_int (71)))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Range.mk_range
                                                    "Pulse.Main.fst"
                                                    (Prims.of_int (617))
                                                    (Prims.of_int (30))
                                                    (Prims.of_int (617))
                                                    (Prims.of_int (45)))
                                                 (FStar_Range.mk_range
                                                    "Pulse.Main.fst"
                                                    (Prims.of_int (616))
                                                    (Prims.of_int (23))
                                                    (Prims.of_int (632))
                                                    (Prims.of_int (79)))
                                                 (Obj.magic
                                                    (FStar_Tactics_SyntaxHelpers.collect_app
                                                       inv))
                                                 (fun uu___4 ->
                                                    (fun uu___4 ->
                                                       match uu___4 with
                                                       | (hd, args1) ->
                                                           (match ((FStar_Reflection_Builtins.inspect_ln
                                                                    hd),
                                                                    args1)
                                                            with
                                                            | (FStar_Reflection_Data.Tv_FVar
                                                               fv,
                                                               (inv1, uu___5)::[])
                                                                ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (if
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv) <>
                                                                    invariant_fv
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives.Inr
                                                                    "WHILE: Expected while to be decorated with an invariant"))
                                                                    else
                                                                    Obj.repr
                                                                    (match 
                                                                    FStar_Reflection_Builtins.inspect_ln
                                                                    inv1
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Abs
                                                                    (uu___7,
                                                                    body1) ->
                                                                    translate_vprop
                                                                    g body1
                                                                    | 
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (626))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (50)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (626))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (50)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (49)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    inv1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    "WHILE: Expected inv to be an abstraction, got "
                                                                    (Prims.strcat
                                                                    uu___8 "")))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pervasives.Inr
                                                                    uu___8)))))
                                                            | uu___5 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives.Inr
                                                                    "WHILE: Expected while to be decorated with an invariant")))))
                                                      uu___4)))
                                           (fun uu___4 ->
                                              (fun uu___4 ->
                                                 Obj.magic
                                                   (op_let_Question uu___4
                                                      (fun inv1 ->
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "Pulse.Main.fst"
                                                              (Prims.of_int (634))
                                                              (Prims.of_int (30))
                                                              (Prims.of_int (634))
                                                              (Prims.of_int (54)))
                                                           (FStar_Range.mk_range
                                                              "Pulse.Main.fst"
                                                              (Prims.of_int (634))
                                                              (Prims.of_int (13))
                                                              (Prims.of_int (636))
                                                              (Prims.of_int (71)))
                                                           (Obj.magic
                                                              (translate_st_term
                                                                 g cond))
                                                           (fun uu___5 ->
                                                              (fun uu___5 ->
                                                                 Obj.magic
                                                                   (op_let_Question
                                                                    uu___5
                                                                    (fun
                                                                    condition
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (49)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (636))
                                                                    (Prims.of_int (71)))
                                                                    (Obj.magic
                                                                    (translate_st_term
                                                                    g body))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___6
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives.Inl
                                                                    (wr t
                                                                    (Pulse_Syntax_Base.Tm_While
                                                                    {
                                                                    Pulse_Syntax_Base.invariant
                                                                    = inv1;
                                                                    Pulse_Syntax_Base.condition
                                                                    =
                                                                    condition;
                                                                    Pulse_Syntax_Base.body3
                                                                    = body1
                                                                    })))))
                                                                    uu___7)))
                                                                    uu___6))))
                                                                uu___5))))
                                                uu___4))
                                  | uu___1 ->
                                      Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              FStar_Pervasives.Inr
                                                "WHILE: Wrong number of arguments to while")))
                             else
                               Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       FStar_Pervasives.Inr
                                         "WHILE: Not while"))))
                   | uu___1 ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 ->
                                  FStar_Pervasives.Inr
                                    "WHILE: Not a variable at the head")))))
             uu___)
and (translate_rewrite :
  FStar_Reflection_Typing.fstar_top_env ->
    FStar_Reflection_Types.term ->
      (Pulse_Syntax_Base.st_term err, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (645))
           (Prims.of_int (19)) (Prims.of_int (645)) (Prims.of_int (34)))
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (644))
           (Prims.of_int (15)) (Prims.of_int (656)) (Prims.of_int (50)))
        (Obj.magic (FStar_Tactics_SyntaxHelpers.collect_app t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (head, args) ->
                  (match FStar_Reflection_Builtins.inspect_ln head with
                   | FStar_Reflection_Data.Tv_FVar v ->
                       Obj.magic
                         (Obj.repr
                            (if
                               (FStar_Reflection_Builtins.inspect_fv v) =
                                 rewrite_fv
                             then
                               Obj.repr
                                 (match args with
                                  | (p, uu___1)::(q, uu___2)::[] ->
                                      Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "Pulse.Main.fst"
                                              (Prims.of_int (651))
                                              (Prims.of_int (21))
                                              (Prims.of_int (651))
                                              (Prims.of_int (36)))
                                           (FStar_Range.mk_range
                                              "Pulse.Main.fst"
                                              (Prims.of_int (651))
                                              (Prims.of_int (11))
                                              (Prims.of_int (653))
                                              (Prims.of_int (43)))
                                           (Obj.magic (readback_ty g p))
                                           (fun uu___3 ->
                                              (fun uu___3 ->
                                                 Obj.magic
                                                   (op_let_Question uu___3
                                                      (fun t1 ->
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "Pulse.Main.fst"
                                                              (Prims.of_int (652))
                                                              (Prims.of_int (21))
                                                              (Prims.of_int (652))
                                                              (Prims.of_int (36)))
                                                           (FStar_Range.mk_range
                                                              "Pulse.Main.fst"
                                                              (Prims.of_int (652))
                                                              (Prims.of_int (11))
                                                              (Prims.of_int (653))
                                                              (Prims.of_int (43)))
                                                           (Obj.magic
                                                              (readback_ty g
                                                                 q))
                                                           (fun uu___4 ->
                                                              (fun uu___4 ->
                                                                 Obj.magic
                                                                   (op_let_Question
                                                                    uu___4
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun t2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Inl
                                                                    (wr t
                                                                    (Pulse_Syntax_Base.Tm_Rewrite
                                                                    {
                                                                    Pulse_Syntax_Base.t1
                                                                    = t1;
                                                                    Pulse_Syntax_Base.t2
                                                                    = t2
                                                                    })))))
                                                                    uu___5)))
                                                                uu___4))))
                                                uu___3))
                                  | uu___1 ->
                                      Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              FStar_Pervasives.Inr
                                                "REWRITE: Wrong number of arguments to rewrite")))
                             else
                               Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       FStar_Pervasives.Inr
                                         "REWRITE: Not rewrite"))))
                   | uu___1 ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 ->
                                  FStar_Pervasives.Inr
                                    "REWRITE: Not a variable at the head")))))
             uu___)
and (translate_par :
  FStar_Reflection_Typing.fstar_top_env ->
    FStar_Reflection_Types.term ->
      (Pulse_Syntax_Base.st_term err, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (662))
           (Prims.of_int (19)) (Prims.of_int (662)) (Prims.of_int (34)))
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (661))
           (Prims.of_int (15)) (Prims.of_int (687)) (Prims.of_int (46)))
        (Obj.magic (FStar_Tactics_SyntaxHelpers.collect_app t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (head, args) ->
                  (match FStar_Reflection_Builtins.inspect_ln head with
                   | FStar_Reflection_Data.Tv_FVar v ->
                       Obj.magic
                         (Obj.repr
                            (if
                               (FStar_Reflection_Builtins.inspect_fv v) =
                                 par_fv
                             then
                               Obj.repr
                                 (match args with
                                  | (preL, uu___1)::(eL, uu___2)::(postL,
                                                                   uu___3)::
                                      (preR, uu___4)::(eR, uu___5)::(postR,
                                                                    uu___6)::[]
                                      ->
                                      Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "Pulse.Main.fst"
                                              (Prims.of_int (670))
                                              (Prims.of_int (23))
                                              (Prims.of_int (670))
                                              (Prims.of_int (41)))
                                           (FStar_Range.mk_range
                                              "Pulse.Main.fst"
                                              (Prims.of_int (670))
                                              (Prims.of_int (11))
                                              (Prims.of_int (684))
                                              (Prims.of_int (73)))
                                           (Obj.magic (readback_ty g preL))
                                           (fun uu___7 ->
                                              (fun uu___7 ->
                                                 Obj.magic
                                                   (op_let_Question uu___7
                                                      (fun pre1 ->
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "Pulse.Main.fst"
                                                              (Prims.of_int (671))
                                                              (Prims.of_int (24))
                                                              (Prims.of_int (671))
                                                              (Prims.of_int (46)))
                                                           (FStar_Range.mk_range
                                                              "Pulse.Main.fst"
                                                              (Prims.of_int (671))
                                                              (Prims.of_int (11))
                                                              (Prims.of_int (684))
                                                              (Prims.of_int (73)))
                                                           (Obj.magic
                                                              (translate_st_term
                                                                 g eL))
                                                           (fun uu___8 ->
                                                              (fun uu___8 ->
                                                                 Obj.magic
                                                                   (op_let_Question
                                                                    uu___8
                                                                    (fun
                                                                    body1 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (66)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (73)))
                                                                    (match 
                                                                    FStar_Reflection_Builtins.inspect_ln
                                                                    postL
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Abs
                                                                    (uu___9,
                                                                    body) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (readback_ty
                                                                    g body))
                                                                    | 
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pervasives.Inr
                                                                    "par: Expected postL to be an abstraction"))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___9
                                                                    (fun
                                                                    post1 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (73)))
                                                                    (Obj.magic
                                                                    (readback_ty
                                                                    g preR))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___10
                                                                    (fun pre2
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (46)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (73)))
                                                                    (Obj.magic
                                                                    (translate_st_term
                                                                    g eR))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___11
                                                                    (fun
                                                                    body2 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (680))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (682))
                                                                    (Prims.of_int (66)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Main.fst"
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (73)))
                                                                    (match 
                                                                    FStar_Reflection_Builtins.inspect_ln
                                                                    postR
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Abs
                                                                    (uu___12,
                                                                    body) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (readback_ty
                                                                    g body))
                                                                    | 
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pervasives.Inr
                                                                    "par: Expected postR to be an abstraction"))))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___12
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    post2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pervasives.Inl
                                                                    (wr t
                                                                    (Pulse_Syntax_Base.Tm_Par
                                                                    {
                                                                    Pulse_Syntax_Base.pre11
                                                                    = pre1;
                                                                    Pulse_Syntax_Base.body11
                                                                    = body1;
                                                                    Pulse_Syntax_Base.post11
                                                                    = post1;
                                                                    Pulse_Syntax_Base.pre2
                                                                    = pre2;
                                                                    Pulse_Syntax_Base.body21
                                                                    = body2;
                                                                    Pulse_Syntax_Base.post21
                                                                    = post2
                                                                    })))))
                                                                    uu___13)))
                                                                    uu___12))))
                                                                    uu___11))))
                                                                    uu___10))))
                                                                    uu___9))))
                                                                uu___8))))
                                                uu___7))
                                  | uu___1 ->
                                      Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              FStar_Pervasives.Inr
                                                "par: Wrong number of arguments")))
                             else
                               Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       FStar_Pervasives.Inr "par: not a par"))))
                   | uu___1 ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 ->
                                  FStar_Pervasives.Inr
                                    "par: Not a variable at the head")))))
             uu___)
let (check' :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Typing.fstar_top_env ->
      ((FStar_Reflection_Types.term * FStar_Reflection_Types.typ), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun g ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (691))
           (Prims.of_int (10)) (Prims.of_int (691)) (Prims.of_int (28)))
        (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (691))
           (Prims.of_int (4)) (Prims.of_int (695)) (Prims.of_int (21)))
        (Obj.magic (translate_term g t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Pervasives.Inr msg ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Derived.fail
                          (Prims.strcat "Failed to translate term: "
                             (Prims.strcat msg ""))))
              | FStar_Pervasives.Inl t1 ->
                  Obj.magic (Obj.repr (main t1 Pulse_Syntax_Base.Tm_Emp g)))
             uu___)
let (check :
  FStar_Reflection_Types.term -> FStar_Reflection_Typing.dsl_tac_t) =
  fun t -> check' t
let _ =
  FStar_Tactics_Native.register_tactic "Pulse.Main.check" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_InterpFuns.mk_tactic_interpretation_2
             (FStar_Tactics_Native.from_tactic_2 check)
             FStar_Reflection_Embeddings.e_term
             FStar_Reflection_Embeddings.e_env
             (FStar_Syntax_Embeddings.e_tuple2
                FStar_Reflection_Embeddings.e_term
                FStar_Reflection_Embeddings.e_term) psc ncb args)
let (check_pulse :
  Prims.string Prims.list ->
    (Prims.string * Prims.string) Prims.list ->
      Prims.string ->
        Prims.string ->
          Prims.int -> Prims.int -> FStar_Reflection_Typing.dsl_tac_t)
  =
  fun namespaces ->
    fun module_abbrevs ->
      fun content ->
        fun file_name ->
          fun line ->
            fun col ->
              fun env ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (708))
                     (Prims.of_int (12)) (Prims.of_int (708))
                     (Prims.of_int (97)))
                  (FStar_Range.mk_range "Pulse.Main.fst" (Prims.of_int (708))
                     (Prims.of_int (6)) (Prims.of_int (714))
                     (Prims.of_int (22)))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        Pulse_ASTBuilder.parse_pulse env namespaces
                          module_abbrevs content file_name line col))
                  (fun uu___ ->
                     (fun uu___ ->
                        match uu___ with
                        | FStar_Pervasives.Inl st_term ->
                            Obj.magic
                              (main st_term Pulse_Syntax_Base.Tm_Emp env)
                        | FStar_Pervasives.Inr (msg, range) ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range "Pulse.Main.fst"
                                    (Prims.of_int (712)) (Prims.of_int (15))
                                    (Prims.of_int (714)) (Prims.of_int (22)))
                                 (FStar_Range.mk_range "Pulse.Main.fst"
                                    (Prims.of_int (712)) (Prims.of_int (8))
                                    (Prims.of_int (714)) (Prims.of_int (22)))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range "Pulse.Main.fst"
                                          (Prims.of_int (712))
                                          (Prims.of_int (15))
                                          (Prims.of_int (714))
                                          (Prims.of_int (22)))
                                       (FStar_Range.mk_range "Pulse.Main.fst"
                                          (Prims.of_int (712))
                                          (Prims.of_int (15))
                                          (Prims.of_int (714))
                                          (Prims.of_int (22)))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "Pulse.Main.fst"
                                                (Prims.of_int (713))
                                                (Prims.of_int (18))
                                                (Prims.of_int (713))
                                                (Prims.of_int (43)))
                                             (FStar_Range.mk_range
                                                "FStar.Printf.fst"
                                                (Prims.of_int (121))
                                                (Prims.of_int (8))
                                                (Prims.of_int (123))
                                                (Prims.of_int (44)))
                                             (Obj.magic
                                                (FStar_Tactics_Builtins.range_to_string
                                                   range))
                                             (fun uu___1 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     fun x ->
                                                       Prims.strcat
                                                         (Prims.strcat
                                                            "Error @ "
                                                            (Prims.strcat
                                                               uu___1 ": "))
                                                         (Prims.strcat x "")))))
                                       (fun uu___1 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 -> uu___1 msg))))
                                 (fun uu___1 ->
                                    FStar_Tactics_Derived.fail uu___1)))
                       uu___)
let _ =
  FStar_Tactics_Native.register_tactic "Pulse.Main.check_pulse"
    (Prims.of_int (8))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_InterpFuns.mk_tactic_interpretation_7
             (FStar_Tactics_Native.from_tactic_7 check_pulse)
             (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string)
             (FStar_Syntax_Embeddings.e_list
                (FStar_Syntax_Embeddings.e_tuple2
                   FStar_Syntax_Embeddings.e_string
                   FStar_Syntax_Embeddings.e_string))
             FStar_Syntax_Embeddings.e_string
             FStar_Syntax_Embeddings.e_string FStar_Syntax_Embeddings.e_int
             FStar_Syntax_Embeddings.e_int FStar_Reflection_Embeddings.e_env
             (FStar_Syntax_Embeddings.e_tuple2
                FStar_Reflection_Embeddings.e_term
                FStar_Reflection_Embeddings.e_term) psc ncb args)