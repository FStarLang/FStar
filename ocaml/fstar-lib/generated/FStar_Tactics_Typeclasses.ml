open Prims
let (debug :
  (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (29)) (Prims.of_int (5)) (Prims.of_int (29))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (29)) (Prims.of_int (2)) (Prims.of_int (30))
               (Prims.of_int (16)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.debugging ()))
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
                               "FStar.Tactics.Typeclasses.fst"
                               (Prims.of_int (30)) (Prims.of_int (10))
                               (Prims.of_int (30)) (Prims.of_int (16)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.Typeclasses.fst"
                               (Prims.of_int (30)) (Prims.of_int (4))
                               (Prims.of_int (30)) (Prims.of_int (16)))))
                      (Obj.magic (f ()))
                      (fun uu___1 ->
                         (fun uu___1 ->
                            Obj.magic
                              (FStar_Tactics_V2_Builtins.print uu___1))
                           uu___1)))
            else
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))))
           uu___)
let op_At :
  'uuuuu .
    unit -> 'uuuuu Prims.list -> 'uuuuu Prims.list -> 'uuuuu Prims.list
  = fun uu___ -> FStar_List_Tot_Base.op_At
let (fv_eq :
  FStar_Reflection_Types.fv -> FStar_Reflection_Types.fv -> Prims.bool) =
  fun fv1 ->
    fun fv2 ->
      let n1 = FStar_Reflection_V2_Builtins.inspect_fv fv1 in
      let n2 = FStar_Reflection_V2_Builtins.inspect_fv fv2 in n1 = n2
let rec (head_of :
  FStar_Tactics_NamedView.term ->
    (FStar_Reflection_Types.fv FStar_Pervasives_Native.option, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (57)) (Prims.of_int (8)) (Prims.of_int (57))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (57)) (Prims.of_int (2)) (Prims.of_int (61))
               (Prims.of_int (13)))))
      (Obj.magic (FStar_Tactics_NamedView.inspect t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Tactics_NamedView.Tv_FVar fv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> FStar_Pervasives_Native.Some fv)))
            | FStar_Tactics_NamedView.Tv_UInst (fv, uu___1) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> FStar_Pervasives_Native.Some fv)))
            | FStar_Tactics_NamedView.Tv_App (h, uu___1) ->
                Obj.magic (Obj.repr (head_of h))
            | v ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> FStar_Pervasives_Native.None)))) uu___)
let rec (res_typ :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (64)) (Prims.of_int (8)) (Prims.of_int (64))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (64)) (Prims.of_int (2)) (Prims.of_int (70))
               (Prims.of_int (10)))))
      (Obj.magic (FStar_Tactics_NamedView.inspect t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Tactics_NamedView.Tv_Arrow (uu___1, c) ->
                Obj.magic
                  (Obj.repr
                     (match FStar_Tactics_NamedView.inspect_comp c with
                      | FStar_Reflection_V2_Data.C_Total t1 ->
                          Obj.repr (res_typ t1)
                      | uu___2 ->
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 -> t))))
            | uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> t))))
           uu___)
exception NoInst 
let (uu___is_NoInst : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | NoInst -> true | uu___ -> false
let rec first :
  'a 'b .
    ('a -> ('b, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> ('b, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun l ->
           match l with
           | [] -> Obj.magic (Obj.repr (FStar_Tactics_Effect.raise NoInst))
           | x::xs ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_V2_Derived.or_else (fun uu___ -> f x)
                       (fun uu___ -> first f xs)))) uu___1 uu___
let rec (tcresolve' :
  FStar_Tactics_NamedView.term Prims.list ->
    FStar_Reflection_Types.fv Prims.list ->
      Prims.int -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun seen ->
    fun glb ->
      fun fuel ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                   (Prims.of_int (96)) (Prims.of_int (4)) (Prims.of_int (97))
                   (Prims.of_int (18)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                   (Prims.of_int (98)) (Prims.of_int (4))
                   (Prims.of_int (113)) (Prims.of_int (34)))))
          (if fuel <= Prims.int_zero
           then FStar_Tactics_Effect.raise NoInst
           else FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.Typeclasses.fst"
                              (Prims.of_int (98)) (Prims.of_int (4))
                              (Prims.of_int (98)) (Prims.of_int (52)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.Typeclasses.fst"
                              (Prims.of_int (98)) (Prims.of_int (53))
                              (Prims.of_int (113)) (Prims.of_int (34)))))
                     (Obj.magic
                        (debug
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         Prims.strcat "fuel = "
                                           (Prims.string_of_int fuel))))
                                uu___1)))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Typeclasses.fst"
                                         (Prims.of_int (100))
                                         (Prims.of_int (12))
                                         (Prims.of_int (100))
                                         (Prims.of_int (23)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Typeclasses.fst"
                                         (Prims.of_int (103))
                                         (Prims.of_int (4))
                                         (Prims.of_int (113))
                                         (Prims.of_int (34)))))
                                (Obj.magic
                                   (FStar_Tactics_V2_Derived.cur_goal ()))
                                (fun uu___2 ->
                                   (fun g ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.Typeclasses.fst"
                                                    (Prims.of_int (103))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (104))
                                                    (Prims.of_int (18)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.Typeclasses.fst"
                                                    (Prims.of_int (106))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (113))
                                                    (Prims.of_int (34)))))
                                           (if
                                              FStar_List_Tot_Base.existsb
                                                (FStar_Reflection_V2_TermEq.term_eq
                                                   g) seen
                                            then
                                              FStar_Tactics_Effect.raise
                                                NoInst
                                            else
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___3 -> ()))
                                           (fun uu___2 ->
                                              (fun uu___2 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Typeclasses.fst"
                                                               (Prims.of_int (106))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (106))
                                                               (Prims.of_int (19)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Typeclasses.fst"
                                                               (Prims.of_int (106))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (113))
                                                               (Prims.of_int (34)))))
                                                      (Obj.magic (head_of g))
                                                      (fun uu___3 ->
                                                         (fun uu___3 ->
                                                            match uu___3 with
                                                            | FStar_Pervasives_Native.None
                                                                ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "goal does not look like a typeclass"))
                                                            | FStar_Pervasives_Native.Some
                                                                head_fv ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    g :: seen))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    seen1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.or_else
                                                                    (local
                                                                    head_fv
                                                                    seen1 glb
                                                                    fuel)
                                                                    (global
                                                                    head_fv
                                                                    seen1 glb
                                                                    fuel)))
                                                                    uu___4))))
                                                           uu___3))) uu___2)))
                                     uu___2))) uu___1))) uu___)
and (local :
  FStar_Reflection_Types.fv ->
    FStar_Tactics_NamedView.term Prims.list ->
      FStar_Reflection_Types.fv Prims.list ->
        Prims.int -> unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun head_fv ->
    fun seen ->
      fun glb ->
        fun fuel ->
          fun uu___ ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                       (Prims.of_int (116)) (Prims.of_int (13))
                       (Prims.of_int (116)) (Prims.of_int (37)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                       (Prims.of_int (117)) (Prims.of_int (4))
                       (Prims.of_int (119)) (Prims.of_int (12)))))
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.Typeclasses.fst"
                             (Prims.of_int (116)) (Prims.of_int (25))
                             (Prims.of_int (116)) (Prims.of_int (37)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.Typeclasses.fst"
                             (Prims.of_int (116)) (Prims.of_int (13))
                             (Prims.of_int (116)) (Prims.of_int (37)))))
                    (Obj.magic (FStar_Tactics_V2_Derived.cur_env ()))
                    (fun uu___1 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___2 ->
                            FStar_Reflection_V2_Builtins.vars_of_env uu___1))))
              (fun uu___1 ->
                 (fun bs ->
                    Obj.magic
                      (first
                         (fun b ->
                            trywith head_fv seen glb fuel
                              (FStar_Tactics_NamedView.pack
                                 (FStar_Tactics_NamedView.Tv_Var
                                    (FStar_Tactics_V2_SyntaxCoercions.binding_to_namedv
                                       b))) b.FStar_Reflection_V2_Data.sort3)
                         bs)) uu___1)
and (global :
  FStar_Reflection_Types.fv ->
    FStar_Tactics_NamedView.term Prims.list ->
      FStar_Reflection_Types.fv Prims.list ->
        Prims.int -> unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun head_fv ->
    fun seen ->
      fun glb ->
        fun fuel ->
          fun uu___ ->
            first
              (fun fv ->
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.Typeclasses.fst"
                            (Prims.of_int (123)) (Prims.of_int (24))
                            (Prims.of_int (123)) (Prims.of_int (58)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.Typeclasses.fst"
                            (Prims.of_int (124)) (Prims.of_int (14))
                            (Prims.of_int (124)) (Prims.of_int (67)))))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.Typeclasses.fst"
                                  (Prims.of_int (123)) (Prims.of_int (27))
                                  (Prims.of_int (123)) (Prims.of_int (38)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.Typeclasses.fst"
                                  (Prims.of_int (123)) (Prims.of_int (24))
                                  (Prims.of_int (123)) (Prims.of_int (58)))))
                         (Obj.magic (FStar_Tactics_V2_Derived.cur_env ()))
                         (fun uu___1 ->
                            (fun uu___1 ->
                               Obj.magic
                                 (FStar_Tactics_V2_Builtins.tc uu___1
                                    (FStar_Tactics_NamedView.pack
                                       (FStar_Tactics_NamedView.Tv_FVar fv))))
                              uu___1)))
                   (fun uu___1 ->
                      (fun typ ->
                         Obj.magic
                           (trywith head_fv seen glb fuel
                              (FStar_Tactics_NamedView.pack
                                 (FStar_Tactics_NamedView.Tv_FVar fv)) typ))
                        uu___1)) glb
and (trywith :
  FStar_Reflection_Types.fv ->
    FStar_Tactics_NamedView.term Prims.list ->
      FStar_Reflection_Types.fv Prims.list ->
        Prims.int ->
          FStar_Tactics_NamedView.term ->
            FStar_Tactics_NamedView.term ->
              (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun head_fv ->
    fun seen ->
      fun glb ->
        fun fuel ->
          fun t ->
            fun typ ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                         (Prims.of_int (128)) (Prims.of_int (10))
                         (Prims.of_int (128)) (Prims.of_int (31)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                         (Prims.of_int (128)) (Prims.of_int (4))
                         (Prims.of_int (136)) (Prims.of_int (20)))))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.Typeclasses.fst"
                               (Prims.of_int (128)) (Prims.of_int (18))
                               (Prims.of_int (128)) (Prims.of_int (31)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.Typeclasses.fst"
                               (Prims.of_int (128)) (Prims.of_int (10))
                               (Prims.of_int (128)) (Prims.of_int (31)))))
                      (Obj.magic (res_typ typ))
                      (fun uu___ ->
                         (fun uu___ -> Obj.magic (head_of uu___)) uu___)))
                (fun uu___ ->
                   (fun uu___ ->
                      match uu___ with
                      | FStar_Pervasives_Native.None ->
                          Obj.magic
                            (Obj.repr (FStar_Tactics_Effect.raise NoInst))
                      | FStar_Pervasives_Native.Some fv' ->
                          Obj.magic
                            (Obj.repr
                               (if fv_eq fv' head_fv
                                then
                                  Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (133))
                                                (Prims.of_int (8))
                                                (Prims.of_int (133))
                                                (Prims.of_int (84)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (134))
                                                (Prims.of_int (8))
                                                (Prims.of_int (134))
                                                (Prims.of_int (81)))))
                                       (Obj.magic
                                          (debug
                                             (fun uu___1 ->
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Typeclasses.fst"
                                                           (Prims.of_int (133))
                                                           (Prims.of_int (67))
                                                           (Prims.of_int (133))
                                                           (Prims.of_int (83)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "prims.fst"
                                                           (Prims.of_int (590))
                                                           (Prims.of_int (19))
                                                           (Prims.of_int (590))
                                                           (Prims.of_int (31)))))
                                                  (Obj.magic
                                                     (FStar_Tactics_V2_Builtins.term_to_string
                                                        t))
                                                  (fun uu___2 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___3 ->
                                                          Prims.strcat
                                                            "Trying to apply hypothesis/instance: "
                                                            uu___2)))))
                                       (fun uu___1 ->
                                          (fun uu___1 ->
                                             Obj.magic
                                               (FStar_Tactics_V2_Derived.seq
                                                  (fun uu___2 ->
                                                     FStar_Tactics_V2_Derived.apply_noinst
                                                       t)
                                                  (fun uu___2 ->
                                                     tcresolve' seen glb
                                                       (fuel - Prims.int_one))))
                                            uu___1))
                                else
                                  Obj.repr
                                    (FStar_Tactics_Effect.raise NoInst))))
                     uu___)
let rec (maybe_intros : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (140)) (Prims.of_int (10)) (Prims.of_int (140))
               (Prims.of_int (21)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (141)) (Prims.of_int (2)) (Prims.of_int (145))
               (Prims.of_int (11)))))
      (Obj.magic (FStar_Tactics_V2_Derived.cur_goal ()))
      (fun uu___1 ->
         (fun g ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (141)) (Prims.of_int (8))
                          (Prims.of_int (141)) (Prims.of_int (17)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (141)) (Prims.of_int (2))
                          (Prims.of_int (145)) (Prims.of_int (11)))))
                 (Obj.magic (FStar_Tactics_NamedView.inspect g))
                 (fun uu___1 ->
                    (fun uu___1 ->
                       match uu___1 with
                       | FStar_Tactics_NamedView.Tv_Arrow (uu___2, uu___3) ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.Typeclasses.fst"
                                            (Prims.of_int (143))
                                            (Prims.of_int (4))
                                            (Prims.of_int (143))
                                            (Prims.of_int (21)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.Typeclasses.fst"
                                            (Prims.of_int (144))
                                            (Prims.of_int (4))
                                            (Prims.of_int (144))
                                            (Prims.of_int (19)))))
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.Typeclasses.fst"
                                                  (Prims.of_int (143))
                                                  (Prims.of_int (11))
                                                  (Prims.of_int (143))
                                                  (Prims.of_int (21)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.Typeclasses.fst"
                                                  (Prims.of_int (143))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (143))
                                                  (Prims.of_int (21)))))
                                         (Obj.magic
                                            (FStar_Tactics_V2_Builtins.intro
                                               ()))
                                         (fun uu___4 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___5 -> ()))))
                                   (fun uu___4 ->
                                      (fun uu___4 ->
                                         Obj.magic (maybe_intros ())) uu___4)))
                       | uu___2 ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___3 -> ())))) uu___1))) uu___1)
let (tcresolve : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (153)) (Prims.of_int (4)) (Prims.of_int (153))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (153)) (Prims.of_int (20)) (Prims.of_int (166))
               (Prims.of_int (18))))) (Obj.magic (maybe_intros ()))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (158)) (Prims.of_int (14))
                          (Prims.of_int (158)) (Prims.of_int (52)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (159)) (Prims.of_int (4))
                          (Prims.of_int (166)) (Prims.of_int (18)))))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.Typeclasses.fst"
                                (Prims.of_int (158)) (Prims.of_int (40))
                                (Prims.of_int (158)) (Prims.of_int (52)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.Typeclasses.fst"
                                (Prims.of_int (158)) (Prims.of_int (14))
                                (Prims.of_int (158)) (Prims.of_int (52)))))
                       (Obj.magic (FStar_Tactics_V2_Derived.cur_env ()))
                       (fun uu___2 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 ->
                               FStar_Reflection_V2_Builtins.lookup_attr
                                 (FStar_Reflection_V2_Builtins.pack_ln
                                    (FStar_Reflection_V2_Data.Tv_FVar
                                       (FStar_Reflection_V2_Builtins.pack_fv
                                          ["FStar";
                                          "Tactics";
                                          "Typeclasses";
                                          "tcinstance"]))) uu___2))))
                 (fun uu___2 ->
                    (fun glb ->
                       Obj.magic
                         (FStar_Tactics_V2_Derived.try_with
                            (fun uu___2 ->
                               match () with
                               | () -> tcresolve' [] glb (Prims.of_int (16)))
                            (fun uu___2 ->
                               (fun uu___2 ->
                                  match uu___2 with
                                  | NoInst ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.Typeclasses.fst"
                                                       (Prims.of_int (163))
                                                       (Prims.of_int (11))
                                                       (Prims.of_int (163))
                                                       (Prims.of_int (73)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.Typeclasses.fst"
                                                       (Prims.of_int (163))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (163))
                                                       (Prims.of_int (73)))))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.Typeclasses.fst"
                                                             (Prims.of_int (163))
                                                             (Prims.of_int (44))
                                                             (Prims.of_int (163))
                                                             (Prims.of_int (72)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "prims.fst"
                                                             (Prims.of_int (590))
                                                             (Prims.of_int (19))
                                                             (Prims.of_int (590))
                                                             (Prims.of_int (31)))))
                                                    (Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.Typeclasses.fst"
                                                                   (Prims.of_int (163))
                                                                   (Prims.of_int (59))
                                                                   (Prims.of_int (163))
                                                                   (Prims.of_int (72)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.Typeclasses.fst"
                                                                   (Prims.of_int (163))
                                                                   (Prims.of_int (44))
                                                                   (Prims.of_int (163))
                                                                   (Prims.of_int (72)))))
                                                          (Obj.magic
                                                             (FStar_Tactics_V2_Derived.cur_goal
                                                                ()))
                                                          (fun uu___3 ->
                                                             (fun uu___3 ->
                                                                Obj.magic
                                                                  (FStar_Tactics_V2_Builtins.term_to_string
                                                                    uu___3))
                                                               uu___3)))
                                                    (fun uu___3 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___4 ->
                                                            Prims.strcat
                                                              "Could not solve constraint "
                                                              uu___3))))
                                              (fun uu___3 ->
                                                 FStar_Tactics_V2_Derived.fail
                                                   uu___3)))
                                  | FStar_Tactics_Common.TacticFailure s ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_V2_Derived.fail
                                              (Prims.strcat
                                                 "Typeclass resolution failed: "
                                                 s)))
                                  | e ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.raise e)))
                                 uu___2))) uu___2))) uu___1)
let _ =
  FStar_Tactics_Native.register_tactic "FStar.Tactics.Typeclasses.tcresolve"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_V2_InterpFuns.mk_tactic_interpretation_1
             "FStar.Tactics.Typeclasses.tcresolve (plugin)"
             (FStar_Tactics_Native.from_tactic_1 tcresolve)
             FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit
             psc ncb args)
let rec (mk_abs :
  FStar_Tactics_NamedView.binder Prims.list ->
    FStar_Tactics_NamedView.term ->
      (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun bs ->
         fun body ->
           match bs with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> body)))
           | b::bs1 ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.Typeclasses.fst"
                                (Prims.of_int (175)) (Prims.of_int (20))
                                (Prims.of_int (175)) (Prims.of_int (47)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "dummy" Prims.int_zero
                                Prims.int_zero Prims.int_zero Prims.int_zero)))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.Typeclasses.fst"
                                      (Prims.of_int (175))
                                      (Prims.of_int (30))
                                      (Prims.of_int (175))
                                      (Prims.of_int (46)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.Typeclasses.fst"
                                      (Prims.of_int (175))
                                      (Prims.of_int (20))
                                      (Prims.of_int (175))
                                      (Prims.of_int (47)))))
                             (Obj.magic (mk_abs bs1 body))
                             (fun uu___ ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     FStar_Tactics_NamedView.Tv_Abs
                                       (b, uu___)))))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> FStar_Tactics_NamedView.pack uu___)))))
        uu___1 uu___
let rec last : 'a . 'a Prims.list -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___ ->
    (fun l ->
       match l with
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_V2_Derived.fail "last: empty list"))
       | x::[] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> x)))
       | uu___::xs -> Obj.magic (Obj.repr (last xs))) uu___
let (filter_no_method_binders :
  FStar_Tactics_NamedView.binders -> FStar_Tactics_NamedView.binders) =
  fun bs ->
    let has_no_method_attr b =
      let attrs = b.FStar_Tactics_NamedView.attrs in
      let is_no_method t =
        match FStar_Reflection_V2_Builtins.inspect_ln t with
        | FStar_Reflection_V2_Data.Tv_FVar fv ->
            let n =
              FStar_Reflection_V2_Derived.flatten_name
                (FStar_Reflection_V2_Builtins.inspect_fv fv) in
            n = "FStar.Tactics.Typeclasses.no_method"
        | uu___ -> false in
      FStar_List_Tot_Base.existsb is_no_method attrs in
    FStar_List_Tot_Base.filter
      (fun b -> Prims.op_Negation (has_no_method_attr b)) bs
let (binder_set_meta :
  FStar_Tactics_NamedView.binder ->
    FStar_Tactics_NamedView.term -> FStar_Tactics_NamedView.binder)
  =
  fun b ->
    fun t ->
      {
        FStar_Tactics_NamedView.uniq = (b.FStar_Tactics_NamedView.uniq);
        FStar_Tactics_NamedView.ppname = (b.FStar_Tactics_NamedView.ppname);
        FStar_Tactics_NamedView.sort = (b.FStar_Tactics_NamedView.sort);
        FStar_Tactics_NamedView.qual = (FStar_Reflection_V2_Data.Q_Meta t);
        FStar_Tactics_NamedView.attrs = (b.FStar_Tactics_NamedView.attrs)
      }
let (mk_class :
  Prims.string ->
    (FStar_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (208)) (Prims.of_int (13)) (Prims.of_int (208))
               (Prims.of_int (26)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (208)) (Prims.of_int (29)) (Prims.of_int (296))
               (Prims.of_int (35)))))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ -> FStar_Reflection_V2_Builtins.explode_qn nm))
      (fun uu___ ->
         (fun ns ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (209)) (Prims.of_int (12))
                          (Prims.of_int (209)) (Prims.of_int (38)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (210)) (Prims.of_int (4))
                          (Prims.of_int (296)) (Prims.of_int (35)))))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.Typeclasses.fst"
                                (Prims.of_int (209)) (Prims.of_int (23))
                                (Prims.of_int (209)) (Prims.of_int (35)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.Typeclasses.fst"
                                (Prims.of_int (209)) (Prims.of_int (12))
                                (Prims.of_int (209)) (Prims.of_int (38)))))
                       (Obj.magic (FStar_Tactics_V2_Builtins.top_env ()))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               FStar_Reflection_V2_Builtins.lookup_typ uu___
                                 ns))))
                 (fun uu___ ->
                    (fun r ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Typeclasses.fst"
                                     (Prims.of_int (210)) (Prims.of_int (4))
                                     (Prims.of_int (210)) (Prims.of_int (19)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Typeclasses.fst"
                                     (Prims.of_int (210)) (Prims.of_int (20))
                                     (Prims.of_int (296)) (Prims.of_int (35)))))
                            (Obj.magic
                               (FStar_Tactics_V2_Derived.guard
                                  (FStar_Pervasives_Native.uu___is_Some r)))
                            (fun uu___ ->
                               (fun uu___ ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (211))
                                                (Prims.of_int (18))
                                                (Prims.of_int (211))
                                                (Prims.of_int (19)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (210))
                                                (Prims.of_int (20))
                                                (Prims.of_int (296))
                                                (Prims.of_int (35)))))
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> r))
                                       (fun uu___1 ->
                                          (fun uu___1 ->
                                             match uu___1 with
                                             | FStar_Pervasives_Native.Some
                                                 se ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Typeclasses.fst"
                                                               (Prims.of_int (212))
                                                               (Prims.of_int (23))
                                                               (Prims.of_int (212))
                                                               (Prims.of_int (115)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Typeclasses.fst"
                                                               (Prims.of_int (212))
                                                               (Prims.of_int (118))
                                                               (Prims.of_int (296))
                                                               (Prims.of_int (35)))))
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___2 ->
                                                            FStar_List_Tot_Base.filter
                                                              (fun uu___3 ->
                                                                 match uu___3
                                                                 with
                                                                 | FStar_Reflection_V2_Data.Inline_for_extraction
                                                                    -> true
                                                                 | FStar_Reflection_V2_Data.NoExtract
                                                                    -> true
                                                                 | uu___4 ->
                                                                    false)
                                                              (FStar_Reflection_V2_Builtins.sigelt_quals
                                                                 se)))
                                                      (fun uu___2 ->
                                                         (fun to_propagate ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (30)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (35)))))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_NamedView.inspect_sigelt
                                                                    se))
                                                                 (fun uu___2
                                                                    ->
                                                                    (fun sv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.guard
                                                                    (FStar_Tactics_NamedView.uu___is_Sg_Inductive
                                                                    sv)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    sv))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_NamedView.Sg_Inductive
                                                                    {
                                                                    FStar_Tactics_NamedView.nm
                                                                    = name;
                                                                    FStar_Tactics_NamedView.univs1
                                                                    = us;
                                                                    FStar_Tactics_NamedView.params
                                                                    = params;
                                                                    FStar_Tactics_NamedView.typ
                                                                    = ity;
                                                                    FStar_Tactics_NamedView.ctors
                                                                    = ctors;_}
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (last
                                                                    name))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    ctor_name
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.guard
                                                                    ((FStar_List_Tot_Base.length
                                                                    ctors) =
                                                                    Prims.int_one)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ctors))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (c_name,
                                                                    ty)::[]
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (224))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_SyntaxHelpers.collect_arr_bs
                                                                    ty))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (bs, cod)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_NamedView.inspect_comp
                                                                    cod))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun r1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.guard
                                                                    (FStar_Reflection_V2_Data.uu___is_C_Total
                                                                    r1)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    r1))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V2_Data.C_Total
                                                                    cod1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    "__proj__Mk"
                                                                    (Prims.strcat
                                                                    ctor_name
                                                                    "__item__")))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun base
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (fun b ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.name_of_binder
                                                                    b))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun s ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.cur_module
                                                                    ()))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun ns1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Reflection_V2_Builtins.pack_fv
                                                                    ((op_At
                                                                    ()) ns1
                                                                    [s])))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun sfv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.fresh_namedv_named
                                                                    "d"))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun dbv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Typeclasses";
                                                                    "tcresolve"]))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun tcr
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (246))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.fresh
                                                                    ()))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    {
                                                                    FStar_Tactics_NamedView.uniq
                                                                    = uu___9;
                                                                    FStar_Tactics_NamedView.ppname
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "dict");
                                                                    FStar_Tactics_NamedView.sort
                                                                    = cod1;
                                                                    FStar_Tactics_NamedView.qual
                                                                    =
                                                                    (FStar_Reflection_V2_Data.Q_Meta
                                                                    tcr);
                                                                    FStar_Tactics_NamedView.attrs
                                                                    = []
                                                                    }))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    tcdict ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.cur_module
                                                                    ()))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (op_At ())
                                                                    uu___9
                                                                    [
                                                                    Prims.strcat
                                                                    base s]))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    proj_name
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    proj_name))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun proj
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.top_env
                                                                    ()))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Reflection_V2_Builtins.lookup_typ
                                                                    uu___9
                                                                    proj_name))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "mk_class: proj not found?"))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_NamedView.inspect_sigelt
                                                                    se1))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_NamedView.Sg_Let
                                                                    {
                                                                    FStar_Tactics_NamedView.isrec
                                                                    = uu___11;
                                                                    FStar_Tactics_NamedView.lbs
                                                                    = lbs;_}
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_SyntaxHelpers.lookup_lb
                                                                    lbs
                                                                    proj_name))
                                                                    | 
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "mk_class: proj not Sg_Let?")))
                                                                    uu___10))))
                                                                    uu___9)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    proj_lb
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_SyntaxHelpers.collect_arr_bs
                                                                    proj_lb.FStar_Tactics_NamedView.lb_typ))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (bs1,
                                                                    cod2) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_List_Tot_Base.splitAt
                                                                    (FStar_List_Tot_Base.length
                                                                    params)
                                                                    bs1))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    (ps, bs2)
                                                                    ->
                                                                    (match bs2
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "mk_class: impossible, no binders"))
                                                                    | 
                                                                    b1::bs'
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    binder_set_meta
                                                                    b1 tcr))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun b11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_SyntaxHelpers.mk_arr
                                                                    ((op_At
                                                                    ()) ps
                                                                    (b11 ::
                                                                    bs'))
                                                                    cod2))
                                                                    uu___11)))))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun ty1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_SyntaxHelpers.collect_abs
                                                                    proj_lb.FStar_Tactics_NamedView.lb_def))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (bs1,
                                                                    body) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (275))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_List_Tot_Base.splitAt
                                                                    (FStar_List_Tot_Base.length
                                                                    params)
                                                                    bs1))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    (ps, bs2)
                                                                    ->
                                                                    (match bs2
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "mk_class: impossible, no binders"))
                                                                    | 
                                                                    b1::bs'
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    binder_set_meta
                                                                    b1 tcr))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun b11
                                                                    ->
                                                                    Obj.magic
                                                                    (mk_abs
                                                                    ((op_At
                                                                    ()) ps
                                                                    (b11 ::
                                                                    bs'))
                                                                    body))
                                                                    uu___11)))))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun def
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    ty1))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun ty2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    def))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun def1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    sfv))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun sfv1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    {
                                                                    FStar_Tactics_NamedView.lb_fv
                                                                    = sfv1;
                                                                    FStar_Tactics_NamedView.lb_us
                                                                    =
                                                                    (proj_lb.FStar_Tactics_NamedView.lb_us);
                                                                    FStar_Tactics_NamedView.lb_typ
                                                                    = ty2;
                                                                    FStar_Tactics_NamedView.lb_def
                                                                    = def1
                                                                    }))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun lb
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_NamedView.pack_sigelt
                                                                    (FStar_Tactics_NamedView.Sg_Let
                                                                    {
                                                                    FStar_Tactics_NamedView.isrec
                                                                    = false;
                                                                    FStar_Tactics_NamedView.lbs
                                                                    = [lb]
                                                                    })))
                                                                    (fun se1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Reflection_V2_Builtins.set_sigelt_attrs
                                                                    b.FStar_Tactics_NamedView.attrs
                                                                    (FStar_Reflection_V2_Builtins.set_sigelt_quals
                                                                    to_propagate
                                                                    se1)))))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9))
                                                                    (filter_no_method_binders
                                                                    bs)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                           uu___2))) uu___1)))
                                 uu___))) uu___))) uu___)
let _ =
  FStar_Tactics_Native.register_tactic "FStar.Tactics.Typeclasses.mk_class"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_V2_InterpFuns.mk_tactic_interpretation_1
             "FStar.Tactics.Typeclasses.mk_class (plugin)"
             (FStar_Tactics_Native.from_tactic_1 mk_class)
             FStar_Syntax_Embeddings.e_string
             (FStar_Syntax_Embeddings.e_list
                FStar_Reflection_V2_Embeddings.e_sigelt) psc ncb args)
let solve : 'a . 'a -> 'a = fun ev -> ev