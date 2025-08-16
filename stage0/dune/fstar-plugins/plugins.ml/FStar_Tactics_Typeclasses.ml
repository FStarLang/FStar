open Fstarcompiler
open Prims
let op_At :
  'uuuuu .
    unit -> 'uuuuu Prims.list -> 'uuuuu Prims.list -> 'uuuuu Prims.list
  = fun uu___ -> FStar_List_Tot_Base.op_At
let (tc_norm_steps : Fstarcompiler.FStarC_NormSteps.norm_step Prims.list) =
  [Fstarcompiler.FStarC_NormSteps.primops;
  Fstarcompiler.FStarC_NormSteps.iota;
  Fstarcompiler.FStarC_NormSteps.delta_qualifier ["unfold"]]
type st_t =
  {
  seen: FStar_Tactics_NamedView.term Prims.list ;
  glb:
    (FStarC_Reflection_Types.sigelt * FStarC_Reflection_Types.fv) Prims.list ;
  fuel: Prims.int ;
  rng: FStar_Range.range ;
  warned_oof: Prims.bool FStarC_Tactics_Types.tref ;
  dbg: Prims.bool }
let (__proj__Mkst_t__item__seen :
  st_t -> FStar_Tactics_NamedView.term Prims.list) =
  fun projectee ->
    match projectee with | { seen; glb; fuel; rng; warned_oof; dbg;_} -> seen
let (__proj__Mkst_t__item__glb :
  st_t ->
    (FStarC_Reflection_Types.sigelt * FStarC_Reflection_Types.fv) Prims.list)
  =
  fun projectee ->
    match projectee with | { seen; glb; fuel; rng; warned_oof; dbg;_} -> glb
let (__proj__Mkst_t__item__fuel : st_t -> Prims.int) =
  fun projectee ->
    match projectee with | { seen; glb; fuel; rng; warned_oof; dbg;_} -> fuel
let (__proj__Mkst_t__item__rng : st_t -> FStar_Range.range) =
  fun projectee ->
    match projectee with | { seen; glb; fuel; rng; warned_oof; dbg;_} -> rng
let (__proj__Mkst_t__item__warned_oof :
  st_t -> Prims.bool FStarC_Tactics_Types.tref) =
  fun projectee ->
    match projectee with
    | { seen; glb; fuel; rng; warned_oof; dbg;_} -> warned_oof
let (__proj__Mkst_t__item__dbg : st_t -> Prims.bool) =
  fun projectee ->
    match projectee with | { seen; glb; fuel; rng; warned_oof; dbg;_} -> dbg
let (debug :
  st_t ->
    (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun st ->
         fun f ->
           if st.dbg
           then
             Obj.magic
               (Obj.repr
                  (let uu___ = f () in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.Typeclasses.fst"
                              (Prims.of_int (58)) (Prims.of_int (10))
                              (Prims.of_int (58)) (Prims.of_int (16)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.Typeclasses.fst"
                              (Prims.of_int (58)) (Prims.of_int (4))
                              (Prims.of_int (58)) (Prims.of_int (16)))))
                     (Obj.magic uu___)
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStarC_Tactics_V2_Builtins.print uu___1))
                          uu___1)))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
        uu___1 uu___
type tc_goal =
  {
  g: FStar_Tactics_NamedView.term ;
  head_fv: FStarC_Reflection_Types.fv ;
  c_se: FStarC_Reflection_Types.sigelt FStar_Pervasives_Native.option ;
  fundeps: Prims.int Prims.list FStar_Pervasives_Native.option ;
  args_and_uvars: (FStarC_Reflection_V2_Data.argv * Prims.bool) Prims.list }
let (__proj__Mktc_goal__item__g : tc_goal -> FStar_Tactics_NamedView.term) =
  fun projectee ->
    match projectee with
    | { g; head_fv; c_se; fundeps; args_and_uvars;_} -> g
let (__proj__Mktc_goal__item__head_fv :
  tc_goal -> FStarC_Reflection_Types.fv) =
  fun projectee ->
    match projectee with
    | { g; head_fv; c_se; fundeps; args_and_uvars;_} -> head_fv
let (__proj__Mktc_goal__item__c_se :
  tc_goal -> FStarC_Reflection_Types.sigelt FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { g; head_fv; c_se; fundeps; args_and_uvars;_} -> c_se
let (__proj__Mktc_goal__item__fundeps :
  tc_goal -> Prims.int Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { g; head_fv; c_se; fundeps; args_and_uvars;_} -> fundeps
let (__proj__Mktc_goal__item__args_and_uvars :
  tc_goal -> (FStarC_Reflection_V2_Data.argv * Prims.bool) Prims.list) =
  fun projectee ->
    match projectee with
    | { g; head_fv; c_se; fundeps; args_and_uvars;_} -> args_and_uvars
let (fv_eq :
  FStarC_Reflection_Types.fv -> FStarC_Reflection_Types.fv -> Prims.bool) =
  fun fv1 ->
    fun fv2 ->
      let n1 = FStarC_Reflection_V2_Builtins.inspect_fv fv1 in
      let n2 = FStarC_Reflection_V2_Builtins.inspect_fv fv2 in n1 = n2
let rec (head_of :
  FStar_Tactics_NamedView.term ->
    (FStarC_Reflection_Types.fv FStar_Pervasives_Native.option, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Tactics_NamedView.inspect t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (86)) (Prims.of_int (8)) (Prims.of_int (86))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (86)) (Prims.of_int (2)) (Prims.of_int (90))
               (Prims.of_int (13))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Tactics_NamedView.Tv_FVar fv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> FStar_Pervasives_Native.Some fv)))
            | FStar_Tactics_NamedView.Tv_UInst (fv, uu___2) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 -> FStar_Pervasives_Native.Some fv)))
            | FStar_Tactics_NamedView.Tv_App (h, uu___2) ->
                Obj.magic (Obj.repr (head_of h))
            | v ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> FStar_Pervasives_Native.None))))
           uu___1)
let rec (res_typ :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Tactics_NamedView.inspect t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (93)) (Prims.of_int (8)) (Prims.of_int (93))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (93)) (Prims.of_int (2)) (Prims.of_int (99))
               (Prims.of_int (10))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Tactics_NamedView.Tv_Arrow (uu___2, c) ->
                Obj.magic
                  (Obj.repr
                     (match FStar_Tactics_NamedView.inspect_comp c with
                      | FStarC_Reflection_V2_Data.C_Total t1 ->
                          Obj.repr (res_typ t1)
                      | uu___3 ->
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___4 -> t))))
            | uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> t))))
           uu___1)
exception Next 
let (uu___is_Next : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Next -> true | uu___ -> false
let skip :
  'a . st_t -> Prims.string -> ('a, Obj.t) FStar_Tactics_Effect.tac_repr =
  fun uu___1 ->
    fun uu___ ->
      (fun st ->
         fun s ->
           let uu___ =
             if st.dbg
             then
               Obj.magic
                 (Obj.repr
                    (FStarC_Tactics_V2_Builtins.print
                       (Prims.strcat "skip: " s)))
             else
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))) in
           Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                         (Prims.of_int (108)) (Prims.of_int (4))
                         (Prims.of_int (109)) (Prims.of_int (26)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                         (Prims.of_int (110)) (Prims.of_int (4))
                         (Prims.of_int (110)) (Prims.of_int (14)))))
                (Obj.magic uu___)
                (fun uu___1 -> FStar_Tactics_Effect.raise Next))) uu___1
        uu___
let orskip :
  'a .
    st_t ->
      Prims.string ->
        (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
          ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun st ->
    fun s ->
      fun k ->
        FStar_Tactics_V2_Derived.try_with
          (fun uu___ -> match () with | () -> k ())
          (fun uu___ -> (fun uu___ -> Obj.magic (skip st s)) uu___)
let op_Greater_Greater_Greater :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
        unit -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t1 ->
    fun t2 ->
      fun uu___ ->
        FStar_Tactics_V2_Derived.try_with
          (fun uu___1 -> match () with | () -> t1 ())
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | Next -> Obj.magic (Obj.repr (t2 ()))
                | e -> Obj.magic (Obj.repr (FStar_Tactics_Effect.raise e)))
               uu___1)
let run :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      ('a, unit) FStar_Tactics_Effect.tac_repr
  = fun t -> t ()
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
           | [] -> Obj.magic (Obj.repr (FStar_Tactics_Effect.raise Next))
           | x::xs ->
               Obj.magic
                 (Obj.repr
                    (run
                       (op_Greater_Greater_Greater (fun uu___ -> f x)
                          (fun uu___ -> first f xs))))) uu___1 uu___
let rec (maybe_intros : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = FStar_Tactics_V2_Derived.cur_goal () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (132)) (Prims.of_int (10)) (Prims.of_int (132))
               (Prims.of_int (21)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (133)) (Prims.of_int (2)) (Prims.of_int (137))
               (Prims.of_int (11))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun g ->
            let uu___2 = FStar_Tactics_NamedView.inspect g in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (133)) (Prims.of_int (8))
                          (Prims.of_int (133)) (Prims.of_int (17)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (133)) (Prims.of_int (2))
                          (Prims.of_int (137)) (Prims.of_int (11)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun uu___3 ->
                       match uu___3 with
                       | FStar_Tactics_NamedView.Tv_Arrow (uu___4, uu___5) ->
                           Obj.magic
                             (Obj.repr
                                (let uu___6 =
                                   let uu___7 =
                                     FStarC_Tactics_V2_Builtins.intro () in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Typeclasses.fst"
                                              (Prims.of_int (135))
                                              (Prims.of_int (11))
                                              (Prims.of_int (135))
                                              (Prims.of_int (21)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Typeclasses.fst"
                                              (Prims.of_int (135))
                                              (Prims.of_int (4))
                                              (Prims.of_int (135))
                                              (Prims.of_int (21)))))
                                     (Obj.magic uu___7)
                                     (fun uu___8 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___9 -> ())) in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.Typeclasses.fst"
                                            (Prims.of_int (135))
                                            (Prims.of_int (4))
                                            (Prims.of_int (135))
                                            (Prims.of_int (21)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.Typeclasses.fst"
                                            (Prims.of_int (136))
                                            (Prims.of_int (4))
                                            (Prims.of_int (136))
                                            (Prims.of_int (19)))))
                                   (Obj.magic uu___6)
                                   (fun uu___7 ->
                                      (fun uu___7 ->
                                         Obj.magic (maybe_intros ())) uu___7)))
                       | uu___4 ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___5 -> ())))) uu___3))) uu___2)
let (sigelt_name :
  FStarC_Reflection_Types.sigelt -> FStarC_Reflection_Types.fv Prims.list) =
  fun se ->
    match FStarC_Reflection_V2_Builtins.inspect_sigelt se with
    | FStarC_Reflection_V2_Data.Sg_Let (uu___, lbs) ->
        (match lbs with
         | lb::[] ->
             [(FStarC_Reflection_V2_Builtins.inspect_lb lb).FStarC_Reflection_V2_Data.lb_fv]
         | uu___1 -> [])
    | FStarC_Reflection_V2_Data.Sg_Val (nm, uu___, uu___1) ->
        [FStarC_Reflection_V2_Builtins.pack_fv nm]
    | uu___ -> []
let (unembed_int :
  FStar_Tactics_NamedView.term ->
    (Prims.int FStar_Pervasives_Native.option, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               match FStarC_Reflection_V2_Builtins.inspect_ln t with
               | FStarC_Reflection_V2_Data.Tv_Const
                   (FStarC_Reflection_V2_Data.C_Int i) ->
                   FStar_Pervasives_Native.Some i
               | uu___1 -> FStar_Pervasives_Native.None))) uu___
let rec unembed_list :
  'a .
    (FStar_Tactics_NamedView.term ->
       ('a FStar_Pervasives_Native.option, unit)
         FStar_Tactics_Effect.tac_repr)
      ->
      FStar_Tactics_NamedView.term ->
        ('a Prims.list FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr
  =
  fun u ->
    fun t ->
      let uu___ = FStar_Tactics_V2_SyntaxHelpers.hua t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                 (Prims.of_int (156)) (Prims.of_int (8)) (Prims.of_int (156))
                 (Prims.of_int (13)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                 (Prims.of_int (156)) (Prims.of_int (2)) (Prims.of_int (170))
                 (Prims.of_int (8))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | FStar_Pervasives_Native.Some
                  (fv, uu___2,
                   (ty, FStarC_Reflection_V2_Data.Q_Implicit)::(hd,
                                                                FStarC_Reflection_V2_Data.Q_Explicit)::
                   (tl, FStarC_Reflection_V2_Data.Q_Explicit)::[])
                  ->
                  Obj.magic
                    (Obj.repr
                       (if
                          (FStarC_Reflection_V2_Builtins.implode_qn
                             (FStarC_Reflection_V2_Builtins.inspect_fv fv))
                            = "Prims.Cons"
                        then
                          Obj.repr
                            (let uu___3 =
                               let uu___4 = u hd in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.Typeclasses.fst"
                                          (Prims.of_int (159))
                                          (Prims.of_int (12))
                                          (Prims.of_int (159))
                                          (Prims.of_int (16)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.Typeclasses.fst"
                                          (Prims.of_int (159))
                                          (Prims.of_int (12))
                                          (Prims.of_int (159))
                                          (Prims.of_int (35)))))
                                 (Obj.magic uu___4)
                                 (fun uu___5 ->
                                    (fun uu___5 ->
                                       let uu___6 = unembed_list u tl in
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.Typeclasses.fst"
                                                     (Prims.of_int (159))
                                                     (Prims.of_int (18))
                                                     (Prims.of_int (159))
                                                     (Prims.of_int (35)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.Typeclasses.fst"
                                                     (Prims.of_int (159))
                                                     (Prims.of_int (12))
                                                     (Prims.of_int (159))
                                                     (Prims.of_int (35)))))
                                            (Obj.magic uu___6)
                                            (fun uu___7 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___8 ->
                                                    (uu___5, uu___7)))))
                                      uu___5) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.Typeclasses.fst"
                                        (Prims.of_int (159))
                                        (Prims.of_int (12))
                                        (Prims.of_int (159))
                                        (Prims.of_int (35)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.Typeclasses.fst"
                                        (Prims.of_int (159))
                                        (Prims.of_int (6))
                                        (Prims.of_int (161))
                                        (Prims.of_int (17)))))
                               (Obj.magic uu___3)
                               (fun uu___4 ->
                                  match uu___4 with
                                  | (FStar_Pervasives_Native.Some hd1,
                                     FStar_Pervasives_Native.Some tl1) ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___5 ->
                                           FStar_Pervasives_Native.Some (hd1
                                             :: tl1))
                                  | uu___5 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___6 ->
                                           FStar_Pervasives_Native.None)))
                        else
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___4 -> FStar_Pervasives_Native.None))))
              | FStar_Pervasives_Native.Some
                  (fv, uu___2,
                   (ty, FStarC_Reflection_V2_Data.Q_Implicit)::[])
                  ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 ->
                             if
                               (FStarC_Reflection_V2_Builtins.implode_qn
                                  (FStarC_Reflection_V2_Builtins.inspect_fv
                                     fv))
                                 = "Prims.Nil"
                             then FStar_Pervasives_Native.Some []
                             else FStar_Pervasives_Native.None)))
              | uu___2 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> FStar_Pervasives_Native.None))))
             uu___1)
let (extract_fundeps :
  FStarC_Reflection_Types.sigelt ->
    (Prims.int Prims.list FStar_Pervasives_Native.option, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun se ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStarC_Reflection_V2_Builtins.sigelt_attrs se)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (173)) (Prims.of_int (14)) (Prims.of_int (173))
               (Prims.of_int (29)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (173)) (Prims.of_int (32)) (Prims.of_int (187))
               (Prims.of_int (13))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun attrs ->
            let rec aux uu___1 =
              (fun attrs1 ->
                 match attrs1 with
                 | [] ->
                     Obj.magic
                       (Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 -> FStar_Pervasives_Native.None)))
                 | attr::attrs' ->
                     Obj.magic
                       (Obj.repr
                          (let uu___1 =
                             FStar_Tactics_V2_SyntaxHelpers.collect_app attr in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.Typeclasses.fst"
                                      (Prims.of_int (178))
                                      (Prims.of_int (12))
                                      (Prims.of_int (178))
                                      (Prims.of_int (28)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.Typeclasses.fst"
                                      (Prims.of_int (178)) (Prims.of_int (6))
                                      (Prims.of_int (185))
                                      (Prims.of_int (18)))))
                             (Obj.magic uu___1)
                             (fun uu___2 ->
                                (fun uu___2 ->
                                   match uu___2 with
                                   | (hd,
                                      (a0,
                                       FStarC_Reflection_V2_Data.Q_Explicit)::[])
                                       ->
                                       if
                                         FStar_Reflection_TermEq_Simple.term_eq
                                           hd
                                           (FStarC_Reflection_V2_Builtins.pack_ln
                                              (FStarC_Reflection_V2_Data.Tv_FVar
                                                 (FStarC_Reflection_V2_Builtins.pack_fv
                                                    ["FStar";
                                                    "Tactics";
                                                    "Typeclasses";
                                                    "fundeps"])))
                                       then
                                         Obj.magic
                                           (unembed_list unembed_int a0)
                                       else Obj.magic (aux attrs')
                                   | uu___3 -> Obj.magic (aux attrs')) uu___2))))
                uu___1 in
            Obj.magic (aux attrs)) uu___1)
let (trywith :
  st_t ->
    tc_goal ->
      FStar_Tactics_NamedView.term ->
        FStar_Tactics_NamedView.term ->
          FStar_Tactics_NamedView.term Prims.list ->
            (st_t -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
              (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun st ->
    fun g ->
      fun t ->
        fun typ ->
          fun attrs ->
            fun k ->
              let uu___ =
                FStar_Tactics_V2_Derived.try_with
                  (fun uu___1 ->
                     match () with
                     | () ->
                         FStar_Tactics_V2_Derived.norm_term tc_norm_steps typ)
                  (fun uu___1 ->
                     (fun uu___1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 -> typ))) uu___1) in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                         (Prims.of_int (200)) (Prims.of_int (6))
                         (Prims.of_int (201)) (Prims.of_int (16)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                         (Prims.of_int (204)) (Prims.of_int (4))
                         (Prims.of_int (242)) (Prims.of_int (13)))))
                (Obj.magic uu___)
                (fun uu___1 ->
                   (fun typ1 ->
                      let uu___1 =
                        let uu___2 = res_typ typ1 in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Typeclasses.fst"
                                   (Prims.of_int (204)) (Prims.of_int (18))
                                   (Prims.of_int (204)) (Prims.of_int (31)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Typeclasses.fst"
                                   (Prims.of_int (204)) (Prims.of_int (10))
                                   (Prims.of_int (204)) (Prims.of_int (31)))))
                          (Obj.magic uu___2)
                          (fun uu___3 ->
                             (fun uu___3 -> Obj.magic (head_of uu___3))
                               uu___3) in
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.Typeclasses.fst"
                                    (Prims.of_int (204)) (Prims.of_int (10))
                                    (Prims.of_int (204)) (Prims.of_int (31)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.Typeclasses.fst"
                                    (Prims.of_int (204)) (Prims.of_int (4))
                                    (Prims.of_int (242)) (Prims.of_int (13)))))
                           (Obj.magic uu___1)
                           (fun uu___2 ->
                              (fun uu___2 ->
                                 match uu___2 with
                                 | FStar_Pervasives_Native.None ->
                                     let uu___3 =
                                       debug st
                                         (fun uu___4 ->
                                            let uu___5 =
                                              let uu___6 =
                                                FStarC_Tactics_V2_Builtins.term_to_string
                                                  t in
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.Typeclasses.fst"
                                                         (Prims.of_int (206))
                                                         (Prims.of_int (56))
                                                         (Prims.of_int (206))
                                                         (Prims.of_int (72)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.Typeclasses.fst"
                                                         (Prims.of_int (206))
                                                         (Prims.of_int (56))
                                                         (Prims.of_int (206))
                                                         (Prims.of_int (106)))))
                                                (Obj.magic uu___6)
                                                (fun uu___7 ->
                                                   (fun uu___7 ->
                                                      let uu___8 =
                                                        let uu___9 =
                                                          FStarC_Tactics_V2_Builtins.term_to_string
                                                            typ1 in
                                                        FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.Typeclasses.fst"
                                                                   (Prims.of_int (206))
                                                                   (Prims.of_int (88))
                                                                   (Prims.of_int (206))
                                                                   (Prims.of_int (106)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Prims.fst"
                                                                   (Prims.of_int (613))
                                                                   (Prims.of_int (19))
                                                                   (Prims.of_int (613))
                                                                   (Prims.of_int (31)))))
                                                          (Obj.magic uu___9)
                                                          (fun uu___10 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___11
                                                                  ->
                                                                  Prims.strcat
                                                                    "    typ="
                                                                    uu___10)) in
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (106)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (31)))))
                                                           (Obj.magic uu___8)
                                                           (fun uu___9 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___10
                                                                   ->
                                                                   Prims.strcat
                                                                    uu___7
                                                                    uu___9))))
                                                     uu___7) in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.Typeclasses.fst"
                                                       (Prims.of_int (206))
                                                       (Prims.of_int (56))
                                                       (Prims.of_int (206))
                                                       (Prims.of_int (106)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Prims.fst"
                                                       (Prims.of_int (613))
                                                       (Prims.of_int (19))
                                                       (Prims.of_int (613))
                                                       (Prims.of_int (31)))))
                                              (Obj.magic uu___5)
                                              (fun uu___6 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___7 ->
                                                      Prims.strcat
                                                        "no head for typ of this? "
                                                        uu___6))) in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Typeclasses.fst"
                                                   (Prims.of_int (206))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (206))
                                                   (Prims.of_int (107)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Typeclasses.fst"
                                                   (Prims.of_int (207))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (207))
                                                   (Prims.of_int (16)))))
                                          (Obj.magic uu___3)
                                          (fun uu___4 ->
                                             FStar_Tactics_Effect.raise Next))
                                 | FStar_Pervasives_Native.Some fv' ->
                                     let uu___3 =
                                       if
                                         Prims.op_Negation
                                           (fv_eq fv' g.head_fv)
                                       then
                                         Obj.magic (skip st "class mismatch")
                                       else
                                         Obj.magic
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___5 -> ())) in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Typeclasses.fst"
                                                   (Prims.of_int (209))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (213))
                                                   (Prims.of_int (7)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Typeclasses.fst"
                                                   (Prims.of_int (213))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (242))
                                                   (Prims.of_int (13)))))
                                          (Obj.magic uu___3)
                                          (fun uu___4 ->
                                             (fun uu___4 ->
                                                let uu___5 =
                                                  let uu___6 =
                                                    FStar_Tactics_Util.mapi
                                                      (fun uu___8 ->
                                                         fun uu___7 ->
                                                           (fun i ->
                                                              fun uu___7 ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (uu___9,
                                                                    b) ->
                                                                    if b
                                                                    then [i]
                                                                    else [])))
                                                             uu___8 uu___7)
                                                      g.args_and_uvars in
                                                  FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.Typeclasses.fst"
                                                             (Prims.of_int (214))
                                                             (Prims.of_int (28))
                                                             (Prims.of_int (214))
                                                             (Prims.of_int (104)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.Typeclasses.fst"
                                                             (Prims.of_int (214))
                                                             (Prims.of_int (28))
                                                             (Prims.of_int (214))
                                                             (Prims.of_int (124)))))
                                                    (Obj.magic uu___6)
                                                    (fun uu___7 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___8 ->
                                                            FStar_List_Tot_Base.flatten
                                                              uu___7)) in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.Typeclasses.fst"
                                                              (Prims.of_int (214))
                                                              (Prims.of_int (28))
                                                              (Prims.of_int (214))
                                                              (Prims.of_int (124)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.Typeclasses.fst"
                                                              (Prims.of_int (215))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (242))
                                                              (Prims.of_int (13)))))
                                                     (Obj.magic uu___5)
                                                     (fun uu___6 ->
                                                        (fun unresolved_args
                                                           ->
                                                           let uu___6 =
                                                             debug st
                                                               (fun uu___7 ->
                                                                  let uu___8
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.term_to_string
                                                                    t in
                                                                  FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (84)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (31)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___8)
                                                                    (
                                                                    fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Prims.strcat
                                                                    "Trying to apply hypothesis/instance: "
                                                                    uu___9))) in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (85)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (13)))))
                                                                (Obj.magic
                                                                   uu___6)
                                                                (fun uu___7
                                                                   ->
                                                                   (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.seq
                                                                    (fun
                                                                    uu___8 ->
                                                                    if
                                                                    FStar_List_Tot_Base.existsb
                                                                    (FStar_Reflection_TermEq_Simple.term_eq
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Typeclasses";
                                                                    "noinst"]))))
                                                                    attrs
                                                                    then
                                                                    orskip st
                                                                    "apply_noinst"
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_V2_Derived.apply_noinst
                                                                    t)
                                                                    else
                                                                    if
                                                                    Prims.uu___is_Cons
                                                                    unresolved_args
                                                                    then
                                                                    (let uu___10
                                                                    =
                                                                    if
                                                                    FStar_Pervasives_Native.uu___is_None
                                                                    g.fundeps
                                                                    then
                                                                    Obj.magic
                                                                    (skip st
                                                                    "Will not continue as there are unresolved args (and no fundeps)")
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> ())) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    g.fundeps)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    fundeps
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    debug st
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    "checking fundeps")))
                                                                    uu___15) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    if
                                                                    FStar_List_Tot_Base.existsb
                                                                    (fun i ->
                                                                    Prims.op_Negation
                                                                    (FStar_List_Tot_Base.mem
                                                                    i fundeps))
                                                                    unresolved_args
                                                                    then
                                                                    Obj.magic
                                                                    (skip st
                                                                    "fundeps: a non-fundep is unresolved")
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    -> ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Obj.magic
                                                                    (orskip
                                                                    st
                                                                    "apply"
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_V2_Derived.apply
                                                                    t)))
                                                                    uu___17)))
                                                                    uu___15)))
                                                                    uu___13)))
                                                                    uu___11))
                                                                    else
                                                                    orskip st
                                                                    "apply_noinst"
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_V2_Derived.apply_noinst
                                                                    t))
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    debug st
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.dump
                                                                    "next" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (97)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.term_to_string
                                                                    t in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___15
                                                                    " seems to have worked")) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Prims.strcat
                                                                    "apply of "
                                                                    uu___14))))
                                                                    uu___12)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (12)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    {
                                                                    seen =
                                                                    (st.seen);
                                                                    glb =
                                                                    (st.glb);
                                                                    fuel =
                                                                    (st.fuel
                                                                    -
                                                                    Prims.int_one);
                                                                    rng =
                                                                    (st.rng);
                                                                    warned_oof
                                                                    =
                                                                    (st.warned_oof);
                                                                    dbg =
                                                                    (st.dbg)
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (12)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun st1
                                                                    ->
                                                                    Obj.magic
                                                                    (k st1))
                                                                    uu___12)))
                                                                    uu___10))))
                                                                    uu___7)))
                                                          uu___6))) uu___4)))
                                uu___2))) uu___1)
let (local :
  st_t ->
    tc_goal ->
      (st_t -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
        unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun st ->
    fun g ->
      fun k ->
        fun uu___ ->
          let uu___1 =
            debug st
              (fun uu___2 ->
                 let uu___3 = FStarC_Tactics_V2_Builtins.term_to_string g.g in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.Typeclasses.fst"
                            (Prims.of_int (245)) (Prims.of_int (43))
                            (Prims.of_int (245)) (Prims.of_int (61)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (613)) (Prims.of_int (19))
                            (Prims.of_int (613)) (Prims.of_int (31)))))
                   (Obj.magic uu___3)
                   (fun uu___4 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___5 -> Prims.strcat "local, goal = " uu___4))) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                     (Prims.of_int (245)) (Prims.of_int (4))
                     (Prims.of_int (245)) (Prims.of_int (62)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                     (Prims.of_int (245)) (Prims.of_int (63))
                     (Prims.of_int (249)) (Prims.of_int (12)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               (fun uu___2 ->
                  let uu___3 =
                    let uu___4 = FStar_Tactics_V2_Derived.cur_env () in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.Typeclasses.fst"
                               (Prims.of_int (246)) (Prims.of_int (25))
                               (Prims.of_int (246)) (Prims.of_int (37)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.Typeclasses.fst"
                               (Prims.of_int (246)) (Prims.of_int (13))
                               (Prims.of_int (246)) (Prims.of_int (37)))))
                      (Obj.magic uu___4)
                      (fun uu___5 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___6 ->
                              FStarC_Reflection_V2_Builtins.vars_of_env
                                uu___5)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.Typeclasses.fst"
                                (Prims.of_int (246)) (Prims.of_int (13))
                                (Prims.of_int (246)) (Prims.of_int (37)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.Typeclasses.fst"
                                (Prims.of_int (247)) (Prims.of_int (4))
                                (Prims.of_int (249)) (Prims.of_int (12)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          (fun bs ->
                             Obj.magic
                               (first
                                  (fun b ->
                                     trywith st g
                                       (FStar_Tactics_NamedView.pack
                                          (FStar_Tactics_NamedView.Tv_Var
                                             (FStar_Tactics_V2_SyntaxCoercions.binding_to_namedv
                                                b)))
                                       b.FStarC_Reflection_V2_Data.sort3 [] k)
                                  bs)) uu___4))) uu___2)
let (global :
  st_t ->
    tc_goal ->
      (st_t -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
        unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun st ->
    fun g ->
      fun k ->
        fun uu___ ->
          let uu___1 =
            debug st
              (fun uu___2 ->
                 let uu___3 = FStarC_Tactics_V2_Builtins.term_to_string g.g in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.Typeclasses.fst"
                            (Prims.of_int (252)) (Prims.of_int (44))
                            (Prims.of_int (252)) (Prims.of_int (62)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (613)) (Prims.of_int (19))
                            (Prims.of_int (613)) (Prims.of_int (31)))))
                   (Obj.magic uu___3)
                   (fun uu___4 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___5 -> Prims.strcat "global, goal = " uu___4))) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                     (Prims.of_int (252)) (Prims.of_int (4))
                     (Prims.of_int (252)) (Prims.of_int (63)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                     (Prims.of_int (253)) (Prims.of_int (4))
                     (Prims.of_int (257)) (Prims.of_int (16)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               (fun uu___2 ->
                  Obj.magic
                    (first
                       (fun uu___3 ->
                          match uu___3 with
                          | (se, fv) ->
                              let uu___4 =
                                orskip st "tc"
                                  (fun uu___5 ->
                                     let uu___6 =
                                       FStar_Tactics_V2_Derived.cur_env () in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (254))
                                                (Prims.of_int (53))
                                                (Prims.of_int (254))
                                                (Prims.of_int (64)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (254))
                                                (Prims.of_int (50))
                                                (Prims.of_int (254))
                                                (Prims.of_int (84)))))
                                       (Obj.magic uu___6)
                                       (fun uu___7 ->
                                          (fun uu___7 ->
                                             Obj.magic
                                               (FStarC_Tactics_V2_Builtins.tc
                                                  uu___7
                                                  (FStar_Tactics_NamedView.pack
                                                     (FStar_Tactics_NamedView.Tv_FVar
                                                        fv)))) uu___7)) in
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Typeclasses.fst"
                                         (Prims.of_int (254))
                                         (Prims.of_int (24))
                                         (Prims.of_int (254))
                                         (Prims.of_int (85)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Typeclasses.fst"
                                         (Prims.of_int (254))
                                         (Prims.of_int (88))
                                         (Prims.of_int (256))
                                         (Prims.of_int (58)))))
                                (Obj.magic uu___4)
                                (fun uu___5 ->
                                   (fun typ ->
                                      let uu___5 =
                                        Obj.magic
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___6 ->
                                                FStarC_Reflection_V2_Builtins.sigelt_attrs
                                                  se)) in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.Typeclasses.fst"
                                                    (Prims.of_int (255))
                                                    (Prims.of_int (26))
                                                    (Prims.of_int (255))
                                                    (Prims.of_int (41)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.Typeclasses.fst"
                                                    (Prims.of_int (256))
                                                    (Prims.of_int (14))
                                                    (Prims.of_int (256))
                                                    (Prims.of_int (58)))))
                                           (Obj.magic uu___5)
                                           (fun uu___6 ->
                                              (fun attrs ->
                                                 Obj.magic
                                                   (trywith st g
                                                      (FStar_Tactics_NamedView.pack
                                                         (FStar_Tactics_NamedView.Tv_FVar
                                                            fv)) typ attrs k))
                                                uu___6))) uu___5)) st.glb))
                 uu___2)
let rec (unrefine :
  FStar_Tactics_NamedView.named_term_view ->
    (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       match t with
       | FStar_Tactics_NamedView.Tv_Refine (b, t1) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   FStar_Tactics_NamedView.inspect
                     b.FStar_Tactics_NamedView.sort in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.Typeclasses.fst"
                            (Prims.of_int (261)) (Prims.of_int (30))
                            (Prims.of_int (261)) (Prims.of_int (36)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.Typeclasses.fst"
                            (Prims.of_int (261)) (Prims.of_int (21))
                            (Prims.of_int (261)) (Prims.of_int (36)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      (fun uu___1 -> Obj.magic (unrefine uu___1)) uu___1)))
       | FStar_Tactics_NamedView.Tv_AscribedT (e, uu___, uu___1, uu___2) ->
           Obj.magic
             (Obj.repr
                (let uu___3 = FStar_Tactics_NamedView.inspect e in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.Typeclasses.fst"
                            (Prims.of_int (262)) (Prims.of_int (17))
                            (Prims.of_int (262)) (Prims.of_int (18)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.Typeclasses.fst"
                            (Prims.of_int (262)) (Prims.of_int (28))
                            (Prims.of_int (262)) (Prims.of_int (38)))))
                   (Obj.magic uu___3)
                   (fun uu___4 ->
                      (fun uu___4 -> Obj.magic (unrefine uu___4)) uu___4)))
       | FStar_Tactics_NamedView.Tv_AscribedC (e, uu___, uu___1, uu___2) ->
           Obj.magic
             (Obj.repr
                (let uu___3 = FStar_Tactics_NamedView.inspect e in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.Typeclasses.fst"
                            (Prims.of_int (263)) (Prims.of_int (17))
                            (Prims.of_int (263)) (Prims.of_int (18)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.Typeclasses.fst"
                            (Prims.of_int (263)) (Prims.of_int (28))
                            (Prims.of_int (263)) (Prims.of_int (38)))))
                   (Obj.magic uu___3)
                   (fun uu___4 ->
                      (fun uu___4 -> Obj.magic (unrefine uu___4)) uu___4)))
       | uu___ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 -> FStar_Tactics_NamedView.pack t)))) uu___
let (try_trivial :
  FStar_Tactics_NamedView.term ->
    (st_t -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
      unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun g ->
    fun k ->
      fun uu___ ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Tactics_NamedView.inspect g in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                       (Prims.of_int (266)) (Prims.of_int (17))
                       (Prims.of_int (266)) (Prims.of_int (18)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                       (Prims.of_int (267)) (Prims.of_int (12))
                       (Prims.of_int (267)) (Prims.of_int (24)))))
              (Obj.magic uu___3)
              (fun uu___4 ->
                 (fun uu___4 -> Obj.magic (unrefine uu___4)) uu___4) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                     (Prims.of_int (267)) (Prims.of_int (12))
                     (Prims.of_int (267)) (Prims.of_int (24)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                     (Prims.of_int (267)) (Prims.of_int (8))
                     (Prims.of_int (267)) (Prims.of_int (24)))))
            (Obj.magic uu___2)
            (fun uu___3 ->
               (fun uu___3 ->
                  Obj.magic (FStar_Tactics_V2_SyntaxHelpers.hua uu___3))
                 uu___3) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                   (Prims.of_int (267)) (Prims.of_int (8))
                   (Prims.of_int (267)) (Prims.of_int (24)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                   (Prims.of_int (267)) (Prims.of_int (2))
                   (Prims.of_int (275)) (Prims.of_int (19)))))
          (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 ->
                match uu___2 with
                | FStar_Pervasives_Native.Some (fv, u, a) ->
                    Obj.magic
                      (Obj.repr
                         (if
                            (FStarC_Reflection_V2_Builtins.implode_qn
                               (FStarC_Reflection_V2_Builtins.inspect_fv fv))
                              = "Prims.unit"
                          then
                            Obj.repr
                              (FStar_Tactics_V2_Derived.exact
                                 (FStarC_Reflection_V2_Builtins.pack_ln
                                    (FStarC_Reflection_V2_Data.Tv_Const
                                       FStarC_Reflection_V2_Data.C_Unit)))
                          else
                            Obj.repr
                              (if
                                 (FStarC_Reflection_V2_Builtins.implode_qn
                                    (FStarC_Reflection_V2_Builtins.inspect_fv
                                       fv))
                                   = "Prims.squash"
                               then
                                 Obj.repr (FStar_Tactics_V2_Derived.smt ())
                               else
                                 Obj.repr (FStar_Tactics_Effect.raise Next))))
                | uu___3 ->
                    Obj.magic (Obj.repr (FStar_Tactics_Effect.raise Next)))
               uu___2)
let rec (tac_unrefine :
  unit -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = FStar_Tactics_V2_Derived.cur_goal () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (279)) (Prims.of_int (10)) (Prims.of_int (279))
               (Prims.of_int (21)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (281)) (Prims.of_int (2)) (Prims.of_int (295))
               (Prims.of_int (14))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun g ->
            match FStarC_Reflection_V2_Builtins.inspect_ln g with
            | FStarC_Reflection_V2_Data.Tv_Refine (b, ref) ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 =
                        Obj.magic
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 ->
                                (FStarC_Reflection_V2_Builtins.inspect_binder
                                   b).FStarC_Reflection_V2_Data.sort2)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.Typeclasses.fst"
                                 (Prims.of_int (283)) (Prims.of_int (12))
                                 (Prims.of_int (283)) (Prims.of_int (35)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.Typeclasses.fst"
                                 (Prims.of_int (283)) (Prims.of_int (38))
                                 (Prims.of_int (293)) (Prims.of_int (8)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun t ->
                              let uu___3 =
                                FStar_Tactics_V2_Derived.fresh_uvar
                                  (FStar_Pervasives_Native.Some t) in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.Typeclasses.fst"
                                            (Prims.of_int (285))
                                            (Prims.of_int (13))
                                            (Prims.of_int (285))
                                            (Prims.of_int (32)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.Typeclasses.fst"
                                            (Prims.of_int (287))
                                            (Prims.of_int (4))
                                            (Prims.of_int (293))
                                            (Prims.of_int (8)))))
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      (fun uv ->
                                         let uu___4 =
                                           FStar_Tactics_V2_Derived.exact_with_ref
                                             uv in
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.Typeclasses.fst"
                                                       (Prims.of_int (287))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (287))
                                                       (Prims.of_int (21)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.Typeclasses.fst"
                                                       (Prims.of_int (290))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (293))
                                                       (Prims.of_int (8)))))
                                              (Obj.magic uu___4)
                                              (fun uu___5 ->
                                                 (fun uu___5 ->
                                                    let uu___6 =
                                                      FStarC_Tactics_V2_Builtins.unshelve
                                                        uv in
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.Typeclasses.fst"
                                                                  (Prims.of_int (290))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (290))
                                                                  (Prims.of_int (15)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.Typeclasses.fst"
                                                                  (Prims.of_int (292))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (293))
                                                                  (Prims.of_int (8)))))
                                                         (Obj.magic uu___6)
                                                         (fun uu___7 ->
                                                            (fun uu___7 ->
                                                               let uu___8 =
                                                                 let uu___9 =
                                                                   tac_unrefine
                                                                    () in
                                                                 FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (28)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (28)))))
                                                                   (Obj.magic
                                                                    uu___9)
                                                                   (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    -> ())) in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (28)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (8)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___8)
                                                                    (
                                                                    fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> true))))
                                                              uu___7)))
                                                   uu___5))) uu___4))) uu___3)))
            | uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> false))))
           uu___2)
let (try_unrefining :
  st_t ->
    (st_t -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
      unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun st ->
    fun k ->
      fun uu___ ->
        let uu___1 = tac_unrefine () in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                   (Prims.of_int (298)) (Prims.of_int (5))
                   (Prims.of_int (298)) (Prims.of_int (20)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                   (Prims.of_int (298)) (Prims.of_int (2))
                   (Prims.of_int (301)) (Prims.of_int (14)))))
          (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 ->
                if uu___2
                then Obj.magic (Obj.repr (k st))
                else Obj.magic (Obj.repr (FStar_Tactics_Effect.raise Next)))
               uu___2)
let (try_instances :
  st_t ->
    (st_t -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
      unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun st ->
    fun k ->
      fun uu___ ->
        let uu___1 = FStar_Tactics_V2_Derived.cur_goal () in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                   (Prims.of_int (304)) (Prims.of_int (10))
                   (Prims.of_int (304)) (Prims.of_int (21)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                   (Prims.of_int (305)) (Prims.of_int (2))
                   (Prims.of_int (324)) (Prims.of_int (5)))))
          (Obj.magic uu___1)
          (fun uu___2 ->
             (fun g ->
                let uu___2 = FStar_Tactics_V2_SyntaxHelpers.hua g in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.Typeclasses.fst"
                              (Prims.of_int (305)) (Prims.of_int (8))
                              (Prims.of_int (305)) (Prims.of_int (13)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.Typeclasses.fst"
                              (Prims.of_int (305)) (Prims.of_int (2))
                              (Prims.of_int (324)) (Prims.of_int (5)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           match uu___3 with
                           | FStar_Pervasives_Native.None ->
                               let uu___4 =
                                 debug st
                                   (fun uu___5 ->
                                      let uu___6 =
                                        FStarC_Tactics_V2_Builtins.term_to_string
                                          g in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.Typeclasses.fst"
                                                 (Prims.of_int (307))
                                                 (Prims.of_int (66))
                                                 (Prims.of_int (307))
                                                 (Prims.of_int (82)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Prims.fst"
                                                 (Prims.of_int (613))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (613))
                                                 (Prims.of_int (31)))))
                                        (Obj.magic uu___6)
                                        (fun uu___7 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___8 ->
                                                Prims.strcat
                                                  "Goal does not look like a typeclass: "
                                                  uu___7))) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.Typeclasses.fst"
                                             (Prims.of_int (307))
                                             (Prims.of_int (4))
                                             (Prims.of_int (307))
                                             (Prims.of_int (83)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.Typeclasses.fst"
                                             (Prims.of_int (308))
                                             (Prims.of_int (4))
                                             (Prims.of_int (308))
                                             (Prims.of_int (14)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       FStar_Tactics_Effect.raise Next))
                           | FStar_Pervasives_Native.Some (head_fv, us, args)
                               ->
                               let uu___4 =
                                 let uu___5 =
                                   FStar_Tactics_V2_Derived.cur_env () in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.Typeclasses.fst"
                                            (Prims.of_int (312))
                                            (Prims.of_int (26))
                                            (Prims.of_int (312))
                                            (Prims.of_int (38)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.Typeclasses.fst"
                                            (Prims.of_int (312))
                                            (Prims.of_int (15))
                                            (Prims.of_int (312))
                                            (Prims.of_int (59)))))
                                   (Obj.magic uu___5)
                                   (fun uu___6 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___7 ->
                                           FStarC_Reflection_V2_Builtins.lookup_typ
                                             uu___6
                                             (FStarC_Reflection_V2_Builtins.inspect_fv
                                                head_fv))) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.Typeclasses.fst"
                                             (Prims.of_int (312))
                                             (Prims.of_int (15))
                                             (Prims.of_int (312))
                                             (Prims.of_int (59)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.Typeclasses.fst"
                                             (Prims.of_int (312))
                                             (Prims.of_int (62))
                                             (Prims.of_int (324))
                                             (Prims.of_int (5)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       (fun c_se ->
                                          let uu___5 =
                                            match c_se with
                                            | FStar_Pervasives_Native.None ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___6 ->
                                                           FStar_Pervasives_Native.None)))
                                            | FStar_Pervasives_Native.Some se
                                                ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (extract_fundeps se)) in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.Typeclasses.fst"
                                                        (Prims.of_int (313))
                                                        (Prims.of_int (18))
                                                        (Prims.of_int (315))
                                                        (Prims.of_int (37)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.Typeclasses.fst"
                                                        (Prims.of_int (316))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (324))
                                                        (Prims.of_int (5)))))
                                               (Obj.magic uu___5)
                                               (fun uu___6 ->
                                                  (fun fundeps ->
                                                     let uu___6 =
                                                       FStar_Tactics_Util.map
                                                         (fun uu___7 ->
                                                            match uu___7 with
                                                            | (a, q) ->
                                                                let uu___8 =
                                                                  let uu___9
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.free_uvars
                                                                    a in
                                                                  FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (85)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (85)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___9)
                                                                    (
                                                                    fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Prims.uu___is_Cons
                                                                    uu___10)) in
                                                                FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (85)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (85)))))
                                                                  (Obj.magic
                                                                    uu___8)
                                                                  (fun uu___9
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    ((a, q),
                                                                    uu___9))))
                                                         args in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.Typeclasses.fst"
                                                                   (Prims.of_int (318))
                                                                   (Prims.of_int (25))
                                                                   (Prims.of_int (318))
                                                                   (Prims.of_int (86)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.Typeclasses.fst"
                                                                   (Prims.of_int (318))
                                                                   (Prims.of_int (89))
                                                                   (Prims.of_int (324))
                                                                   (Prims.of_int (5)))))
                                                          (Obj.magic uu___6)
                                                          (fun uu___7 ->
                                                             (fun
                                                                args_and_uvars
                                                                ->
                                                                let uu___7 =
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    {
                                                                    seen = (g
                                                                    ::
                                                                    (st.seen));
                                                                    glb =
                                                                    (st.glb);
                                                                    fuel =
                                                                    (st.fuel);
                                                                    rng =
                                                                    (st.rng);
                                                                    warned_oof
                                                                    =
                                                                    (st.warned_oof);
                                                                    dbg =
                                                                    (st.dbg)
                                                                    })) in
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun st1
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    {
                                                                    g;
                                                                    head_fv;
                                                                    c_se;
                                                                    fundeps;
                                                                    args_and_uvars
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun g1
                                                                    ->
                                                                    Obj.magic
                                                                    (run
                                                                    (op_Greater_Greater_Greater
                                                                    (local
                                                                    st1 g1 k)
                                                                    (global
                                                                    st1 g1 k))))
                                                                    uu___9)))
                                                                    uu___8)))
                                                               uu___7)))
                                                    uu___6))) uu___5)))
                          uu___3))) uu___2)
let rec (tcresolve' : st_t -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun st ->
    let uu___ =
      if st.fuel <= Prims.int_zero
      then
        Obj.magic
          (Obj.repr
             (let uu___1 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 -> st.warned_oof)) in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                         (Prims.of_int (333)) (Prims.of_int (14))
                         (Prims.of_int (333)) (Prims.of_int (27)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                         (Prims.of_int (334)) (Prims.of_int (6))
                         (Prims.of_int (342)) (Prims.of_int (16)))))
                (Obj.magic uu___1)
                (fun uu___2 ->
                   (fun r ->
                      let uu___2 =
                        let uu___3 =
                          let uu___4 = FStarC_Tactics_V2_Builtins.read r in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Typeclasses.fst"
                                     (Prims.of_int (334)) (Prims.of_int (13))
                                     (Prims.of_int (334)) (Prims.of_int (21)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Typeclasses.fst"
                                     (Prims.of_int (334)) (Prims.of_int (9))
                                     (Prims.of_int (334)) (Prims.of_int (21)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___6 -> Prims.op_Negation uu___5)) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Typeclasses.fst"
                                   (Prims.of_int (334)) (Prims.of_int (9))
                                   (Prims.of_int (334)) (Prims.of_int (21)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Typeclasses.fst"
                                   (Prims.of_int (334)) (Prims.of_int (6))
                                   (Prims.of_int (341)) (Prims.of_int (7)))))
                          (Obj.magic uu___3)
                          (fun uu___4 ->
                             (fun uu___4 ->
                                if uu___4
                                then
                                  Obj.magic
                                    (Obj.repr
                                       (let uu___5 =
                                          FStarC_Tactics_V2_Builtins.log_issues
                                            [FStar_Issue.mk_issue_doc
                                               "Warning"
                                               [FStar_Pprint.arbitrary_string
                                                  "Warning: fuel exhausted during typeclass resolution.";
                                               FStar_Pprint.arbitrary_string
                                                 "This usually indicates a loop in your instances."]
                                               (FStar_Pervasives_Native.Some
                                                  (st.rng))
                                               FStar_Pervasives_Native.None
                                               []] in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Typeclasses.fst"
                                                   (Prims.of_int (336))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (339))
                                                   (Prims.of_int (32)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Typeclasses.fst"
                                                   (Prims.of_int (340))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (340))
                                                   (Prims.of_int (20)))))
                                          (Obj.magic uu___5)
                                          (fun uu___6 ->
                                             (fun uu___6 ->
                                                Obj.magic
                                                  (FStarC_Tactics_V2_Builtins.write
                                                     r true)) uu___6)))
                                else
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___6 -> ())))) uu___4) in
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.Typeclasses.fst"
                                    (Prims.of_int (334)) (Prims.of_int (6))
                                    (Prims.of_int (341)) (Prims.of_int (7)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.Typeclasses.fst"
                                    (Prims.of_int (342)) (Prims.of_int (6))
                                    (Prims.of_int (342)) (Prims.of_int (16)))))
                           (Obj.magic uu___2)
                           (fun uu___3 -> FStar_Tactics_Effect.raise Next)))
                     uu___2)))
      else
        Obj.magic
          (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (332)) (Prims.of_int (4)) (Prims.of_int (343))
               (Prims.of_int (5)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (344)) (Prims.of_int (4)) (Prims.of_int (359))
               (Prims.of_int (35))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            let uu___2 =
              debug st
                (fun uu___3 ->
                   (fun uu___3 ->
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___4 ->
                              Prims.strcat "fuel = "
                                (Prims.string_of_int st.fuel)))) uu___3) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (344)) (Prims.of_int (4))
                          (Prims.of_int (344)) (Prims.of_int (58)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (346)) (Prims.of_int (4))
                          (Prims.of_int (359)) (Prims.of_int (35)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun uu___3 ->
                       let uu___4 =
                         FStarC_Tactics_V2_Builtins.norm tc_norm_steps in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Typeclasses.fst"
                                     (Prims.of_int (346)) (Prims.of_int (4))
                                     (Prims.of_int (346)) (Prims.of_int (22)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Typeclasses.fst"
                                     (Prims.of_int (347)) (Prims.of_int (4))
                                     (Prims.of_int (359)) (Prims.of_int (35)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               (fun uu___5 ->
                                  let uu___6 = maybe_intros () in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (347))
                                                (Prims.of_int (4))
                                                (Prims.of_int (347))
                                                (Prims.of_int (18)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (347))
                                                (Prims.of_int (19))
                                                (Prims.of_int (359))
                                                (Prims.of_int (35)))))
                                       (Obj.magic uu___6)
                                       (fun uu___7 ->
                                          (fun uu___7 ->
                                             let uu___8 =
                                               FStar_Tactics_V2_Derived.cur_goal
                                                 () in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Typeclasses.fst"
                                                           (Prims.of_int (348))
                                                           (Prims.of_int (12))
                                                           (Prims.of_int (348))
                                                           (Prims.of_int (23)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Typeclasses.fst"
                                                           (Prims.of_int (351))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (359))
                                                           (Prims.of_int (35)))))
                                                  (Obj.magic uu___8)
                                                  (fun uu___9 ->
                                                     (fun g ->
                                                        let uu___9 =
                                                          if
                                                            FStar_List_Tot_Base.existsb
                                                              (FStar_Reflection_TermEq_Simple.term_eq
                                                                 g) st.seen
                                                          then
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (let uu___10
                                                                    =
                                                                    debug st
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> "loop")))
                                                                    uu___11) in
                                                                  FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (33)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (16)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___10)
                                                                    (
                                                                    fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.raise
                                                                    Next)))
                                                          else
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___11
                                                                    -> ()))) in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (5)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (35)))))
                                                             (Obj.magic
                                                                uu___9)
                                                             (fun uu___10 ->
                                                                (fun uu___10
                                                                   ->
                                                                   Obj.magic
                                                                    (run
                                                                    (op_Greater_Greater_Greater
                                                                    (op_Greater_Greater_Greater
                                                                    (try_trivial
                                                                    g
                                                                    tcresolve')
                                                                    (try_instances
                                                                    st
                                                                    tcresolve'))
                                                                    (try_unrefining
                                                                    st
                                                                    tcresolve'))))
                                                                  uu___10)))
                                                       uu___9))) uu___7)))
                                 uu___5))) uu___3))) uu___1)
let (__tcresolve : Prims.bool -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    let uu___ =
      if dbg
      then
        Obj.magic
          (Obj.repr (FStarC_Tactics_V2_Builtins.dump "tcresolve entry point"))
      else
        Obj.magic
          (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (364)) (Prims.of_int (4)) (Prims.of_int (366))
               (Prims.of_int (5)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (366)) (Prims.of_int (6)) (Prims.of_int (401))
               (Prims.of_int (18))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            let uu___2 = FStar_Tactics_V2_Derived.cur_witness () in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (367)) (Prims.of_int (12))
                          (Prims.of_int (367)) (Prims.of_int (26)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (368)) (Prims.of_int (4))
                          (Prims.of_int (401)) (Prims.of_int (18)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun w ->
                       let uu___3 =
                         FStarC_Tactics_V2_Builtins.set_dump_on_failure false in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Typeclasses.fst"
                                     (Prims.of_int (368)) (Prims.of_int (4))
                                     (Prims.of_int (368)) (Prims.of_int (29)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Typeclasses.fst"
                                     (Prims.of_int (371)) (Prims.of_int (4))
                                     (Prims.of_int (401)) (Prims.of_int (18)))))
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               (fun uu___4 ->
                                  let uu___5 = maybe_intros () in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (371))
                                                (Prims.of_int (4))
                                                (Prims.of_int (371))
                                                (Prims.of_int (19)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (371))
                                                (Prims.of_int (20))
                                                (Prims.of_int (401))
                                                (Prims.of_int (18)))))
                                       (Obj.magic uu___5)
                                       (fun uu___6 ->
                                          (fun uu___6 ->
                                             let uu___7 =
                                               let uu___8 =
                                                 FStar_Tactics_V2_Derived.cur_env
                                                   () in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.Typeclasses.fst"
                                                          (Prims.of_int (376))
                                                          (Prims.of_int (44))
                                                          (Prims.of_int (376))
                                                          (Prims.of_int (56)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.Typeclasses.fst"
                                                          (Prims.of_int (376))
                                                          (Prims.of_int (14))
                                                          (Prims.of_int (376))
                                                          (Prims.of_int (56)))))
                                                 (Obj.magic uu___8)
                                                 (fun uu___9 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___10 ->
                                                         FStarC_Reflection_V2_Builtins.lookup_attr_ses
                                                           (FStarC_Reflection_V2_Builtins.pack_ln
                                                              (FStarC_Reflection_V2_Data.Tv_FVar
                                                                 (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Typeclasses";
                                                                    "tcinstance"])))
                                                           uu___9)) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Typeclasses.fst"
                                                           (Prims.of_int (376))
                                                           (Prims.of_int (14))
                                                           (Prims.of_int (376))
                                                           (Prims.of_int (56)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Typeclasses.fst"
                                                           (Prims.of_int (376))
                                                           (Prims.of_int (59))
                                                           (Prims.of_int (401))
                                                           (Prims.of_int (18)))))
                                                  (Obj.magic uu___7)
                                                  (fun uu___8 ->
                                                     (fun glb ->
                                                        let uu___8 =
                                                          FStar_Tactics_Util.concatMap
                                                            (fun se ->
                                                               FStar_Tactics_Util.concatMap
                                                                 (fun uu___9
                                                                    ->
                                                                    (fun fv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    [
                                                                    (se, fv)])))
                                                                    uu___9)
                                                                 (sigelt_name
                                                                    se)) glb in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (379))
                                                                    (Prims.of_int (5)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (18)))))
                                                             (Obj.magic
                                                                uu___8)
                                                             (fun uu___9 ->
                                                                (fun glb1 ->
                                                                   let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    FStar_Tactics_V2_Derived.cur_goal
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.range_of_term
                                                                    uu___12)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (16)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.alloc
                                                                    false in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (16)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    {
                                                                    seen = [];
                                                                    glb =
                                                                    glb1;
                                                                    fuel =
                                                                    (Prims.of_int (16));
                                                                    rng =
                                                                    uu___11;
                                                                    warned_oof
                                                                    = uu___13;
                                                                    dbg
                                                                    }))))
                                                                    uu___11) in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun st0
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.try_with
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    let uu___11
                                                                    =
                                                                    tcresolve'
                                                                    st0 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (390))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (debug
                                                                    st0
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.term_to_string
                                                                    w in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Prims.strcat
                                                                    "Solved to:\n\t"
                                                                    uu___15)))))
                                                                    uu___12))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    Next ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStar_Tactics_V2_Derived.cur_goal
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V2_Builtins.term_to_doc
                                                                    uu___16))
                                                                    uu___16) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Pprint.bquotes
                                                                    uu___15)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (FStar_Pprint.arbitrary_string
                                                                    "Could not solve typeclass constraint")
                                                                    uu___14)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (395))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    [uu___13])) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (395))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (395))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_V2_Derived.fail_doc
                                                                    uu___12)))
                                                                    | 
                                                                    FStarC_Tactics_Common.TacticFailure
                                                                    (msg, r)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail_doc_at
                                                                    ((op_At
                                                                    ())
                                                                    [
                                                                    FStar_Pprint.arbitrary_string
                                                                    "Typeclass resolution failed."]
                                                                    msg) r))
                                                                    | 
                                                                    e ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.raise
                                                                    e)))
                                                                    uu___10)))
                                                                    uu___10)))
                                                                  uu___9)))
                                                       uu___8))) uu___6)))
                                 uu___4))) uu___3))) uu___1)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Typeclasses.__tcresolve" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Typeclasses.__tcresolve (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 __tcresolve)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_bool
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (tcresolve : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = FStarC_Tactics_V2_Builtins.debugging () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (403)) (Prims.of_int (59)) (Prims.of_int (403))
               (Prims.of_int (73)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (403)) (Prims.of_int (47)) (Prims.of_int (403))
               (Prims.of_int (73))))) (Obj.magic uu___1)
      (fun uu___2 -> (fun uu___2 -> Obj.magic (__tcresolve uu___2)) uu___2)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Typeclasses.tcresolve" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Typeclasses.tcresolve (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 tcresolve)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (tcresolve_debug : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> __tcresolve true
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Typeclasses.tcresolve_debug" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Typeclasses.tcresolve_debug (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  tcresolve_debug)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
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
                    (let uu___ =
                       let uu___1 = mk_abs bs1 body in
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.Typeclasses.fst"
                                  (Prims.of_int (413)) (Prims.of_int (30))
                                  (Prims.of_int (413)) (Prims.of_int (46)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.Typeclasses.fst"
                                  (Prims.of_int (413)) (Prims.of_int (20))
                                  (Prims.of_int (413)) (Prims.of_int (47)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___3 ->
                                 FStar_Tactics_NamedView.Tv_Abs (b, uu___2))) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.Typeclasses.fst"
                                (Prims.of_int (413)) (Prims.of_int (20))
                                (Prims.of_int (413)) (Prims.of_int (47)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.Typeclasses.fst"
                                (Prims.of_int (413)) (Prims.of_int (15))
                                (Prims.of_int (413)) (Prims.of_int (47)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               FStar_Tactics_NamedView.pack uu___1)))))
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
      FStar_List_Tot_Base.existsb
        (FStar_Reflection_TermEq_Simple.term_eq
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Typeclasses"; "no_method"]))))
        b.FStar_Tactics_NamedView.attrs in
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
        FStar_Tactics_NamedView.qual = (FStarC_Reflection_V2_Data.Q_Meta t);
        FStar_Tactics_NamedView.attrs = (b.FStar_Tactics_NamedView.attrs)
      }
let (debug' :
  (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    let uu___ = FStarC_Tactics_V2_Builtins.debugging () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (436)) (Prims.of_int (5)) (Prims.of_int (436))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (436)) (Prims.of_int (2)) (Prims.of_int (437))
               (Prims.of_int (16))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            if uu___1
            then
              Obj.magic
                (Obj.repr
                   (let uu___2 = f () in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.Typeclasses.fst"
                               (Prims.of_int (437)) (Prims.of_int (10))
                               (Prims.of_int (437)) (Prims.of_int (16)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.Typeclasses.fst"
                               (Prims.of_int (437)) (Prims.of_int (4))
                               (Prims.of_int (437)) (Prims.of_int (16)))))
                      (Obj.magic uu___2)
                      (fun uu___3 ->
                         (fun uu___3 ->
                            Obj.magic
                              (FStarC_Tactics_V2_Builtins.print uu___3))
                           uu___3)))
            else
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))))
           uu___1)
let (mk_class :
  Prims.string ->
    (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStarC_Reflection_V2_Builtins.explode_qn nm)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (441)) (Prims.of_int (13)) (Prims.of_int (441))
               (Prims.of_int (26)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (441)) (Prims.of_int (29)) (Prims.of_int (535))
               (Prims.of_int (5))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun ns ->
            let uu___1 =
              let uu___2 = FStarC_Tactics_V2_Builtins.top_env () in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                         (Prims.of_int (442)) (Prims.of_int (23))
                         (Prims.of_int (442)) (Prims.of_int (35)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                         (Prims.of_int (442)) (Prims.of_int (12))
                         (Prims.of_int (442)) (Prims.of_int (38)))))
                (Obj.magic uu___2)
                (fun uu___3 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___4 ->
                        FStarC_Reflection_V2_Builtins.lookup_typ uu___3 ns)) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (442)) (Prims.of_int (12))
                          (Prims.of_int (442)) (Prims.of_int (38)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (443)) (Prims.of_int (4))
                          (Prims.of_int (535)) (Prims.of_int (5)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun r ->
                       let uu___2 =
                         FStar_Tactics_V2_Derived.guard
                           (FStar_Pervasives_Native.uu___is_Some r) in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Typeclasses.fst"
                                     (Prims.of_int (443)) (Prims.of_int (4))
                                     (Prims.of_int (443)) (Prims.of_int (19)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Typeclasses.fst"
                                     (Prims.of_int (443)) (Prims.of_int (20))
                                     (Prims.of_int (535)) (Prims.of_int (5)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun uu___3 ->
                                  let uu___4 =
                                    Obj.magic
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___5 -> r)) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (444))
                                                (Prims.of_int (18))
                                                (Prims.of_int (444))
                                                (Prims.of_int (19)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (443))
                                                (Prims.of_int (20))
                                                (Prims.of_int (535))
                                                (Prims.of_int (5)))))
                                       (Obj.magic uu___4)
                                       (fun uu___5 ->
                                          (fun uu___5 ->
                                             match uu___5 with
                                             | FStar_Pervasives_Native.Some
                                                 se ->
                                                 let uu___6 =
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___7 ->
                                                           FStar_List_Tot_Base.filter
                                                             (fun uu___8 ->
                                                                match uu___8
                                                                with
                                                                | FStarC_Reflection_V2_Data.Inline_for_extraction
                                                                    -> true
                                                                | FStarC_Reflection_V2_Data.NoExtract
                                                                    -> true
                                                                | uu___9 ->
                                                                    false)
                                                             (FStarC_Reflection_V2_Builtins.sigelt_quals
                                                                se))) in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Typeclasses.fst"
                                                               (Prims.of_int (445))
                                                               (Prims.of_int (23))
                                                               (Prims.of_int (445))
                                                               (Prims.of_int (115)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Typeclasses.fst"
                                                               (Prims.of_int (445))
                                                               (Prims.of_int (118))
                                                               (Prims.of_int (535))
                                                               (Prims.of_int (5)))))
                                                      (Obj.magic uu___6)
                                                      (fun uu___7 ->
                                                         (fun to_propagate ->
                                                            let uu___7 =
                                                              FStar_Tactics_NamedView.inspect_sigelt
                                                                se in
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (30)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (447))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (5)))))
                                                                 (Obj.magic
                                                                    uu___7)
                                                                 (fun uu___8
                                                                    ->
                                                                    (fun sv
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    FStar_Tactics_V2_Derived.guard
                                                                    (FStar_Tactics_NamedView.uu___is_Sg_Inductive
                                                                    sv) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (447))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (447))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (447))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    -> sv)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (447))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___11
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
                                                                    let uu___12
                                                                    =
                                                                    debug'
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    FStar_Tactics_Util.string_of_list
                                                                    FStar_Tactics_V2_Derived.binder_to_string
                                                                    params in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Prims.strcat
                                                                    "params = "
                                                                    uu___15))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    debug'
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Prims.strcat
                                                                    "got it, name = "
                                                                    (FStarC_Reflection_V2_Builtins.implode_qn
                                                                    name))))
                                                                    uu___15) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    debug'
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.term_to_string
                                                                    ity in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    Prims.strcat
                                                                    "got it, ity = "
                                                                    uu___19))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    last name in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (452))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (452))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    ctor_name
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    FStar_Tactics_V2_Derived.guard
                                                                    ((FStar_List_Tot_Base.length
                                                                    ctors) =
                                                                    Prims.int_one) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    -> ctors)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    match uu___22
                                                                    with
                                                                    | 
                                                                    (c_name,
                                                                    ty)::[]
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    debug'
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.term_to_string
                                                                    ty in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (456))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (456))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    Prims.strcat
                                                                    " of type "
                                                                    uu___28)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (456))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (456))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    Prims.strcat
                                                                    (FStarC_Reflection_V2_Builtins.implode_qn
                                                                    c_name)
                                                                    uu___27)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (456))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (456))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    Prims.strcat
                                                                    "got ctor "
                                                                    uu___26))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (456))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (456))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (456))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStar_Tactics_V2_SyntaxHelpers.collect_arr_bs
                                                                    ty in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (457))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (457))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (456))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    match uu___26
                                                                    with
                                                                    | 
                                                                    (bs, cod)
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Tactics_NamedView.inspect_comp
                                                                    cod)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (458))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (458))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    (fun r1
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStar_Tactics_V2_Derived.guard
                                                                    (FStarC_Reflection_V2_Data.uu___is_C_Total
                                                                    r1) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___31
                                                                    -> r1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (460))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (460))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (459))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    match uu___31
                                                                    with
                                                                    | 
                                                                    FStarC_Reflection_V2_Data.C_Total
                                                                    cod1 ->
                                                                    let uu___32
                                                                    =
                                                                    debug'
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    FStar_Tactics_Util.string_of_list
                                                                    FStar_Tactics_V2_Derived.binder_to_string
                                                                    params in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    Prims.strcat
                                                                    "params = "
                                                                    uu___35))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (462))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___32)
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    debug'
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    Prims.strcat
                                                                    "n_params = "
                                                                    (Prims.string_of_int
                                                                    (FStar_List_Tot_Base.length
                                                                    params)))))
                                                                    uu___35) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (463))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    debug'
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    Prims.strcat
                                                                    "n_univs = "
                                                                    (Prims.string_of_int
                                                                    (FStar_List_Tot_Base.length
                                                                    us)))))
                                                                    uu___37) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (464))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___36)
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    debug'
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    let uu___40
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.term_to_string
                                                                    cod1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___40)
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___42
                                                                    ->
                                                                    Prims.strcat
                                                                    "cod = "
                                                                    uu___41))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (465))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___38)
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    let uu___40
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    Prims.strcat
                                                                    "__proj__Mk"
                                                                    (Prims.strcat
                                                                    ctor_name
                                                                    "__item__"))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (472))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___40)
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    (fun base
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    (fun b ->
                                                                    let uu___41
                                                                    =
                                                                    FStar_Tactics_V2_Derived.name_of_binder
                                                                    b in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___41)
                                                                    (fun
                                                                    uu___42
                                                                    ->
                                                                    (fun s ->
                                                                    let uu___42
                                                                    =
                                                                    debug'
                                                                    (fun
                                                                    uu___43
                                                                    ->
                                                                    (fun
                                                                    uu___43
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___44
                                                                    ->
                                                                    Prims.strcat
                                                                    "processing method "
                                                                    s)))
                                                                    uu___43) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___42)
                                                                    (fun
                                                                    uu___43
                                                                    ->
                                                                    (fun
                                                                    uu___43
                                                                    ->
                                                                    let uu___44
                                                                    =
                                                                    FStar_Tactics_V2_Derived.cur_module
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___44)
                                                                    (fun
                                                                    uu___45
                                                                    ->
                                                                    (fun ns1
                                                                    ->
                                                                    let uu___45
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ((op_At
                                                                    ()) ns1
                                                                    [s]))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___45)
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    (fun sfv
                                                                    ->
                                                                    let uu___46
                                                                    =
                                                                    FStar_Tactics_V2_Derived.fresh_namedv_named
                                                                    "d" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___46)
                                                                    (fun
                                                                    uu___47
                                                                    ->
                                                                    (fun dbv
                                                                    ->
                                                                    let uu___47
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___48
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Typeclasses";
                                                                    "tcresolve"])))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___47)
                                                                    (fun
                                                                    uu___48
                                                                    ->
                                                                    (fun tcr
                                                                    ->
                                                                    let uu___48
                                                                    =
                                                                    let uu___49
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.fresh
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    uu___49)
                                                                    (fun
                                                                    uu___50
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___51
                                                                    ->
                                                                    {
                                                                    FStar_Tactics_NamedView.uniq
                                                                    = uu___50;
                                                                    FStar_Tactics_NamedView.ppname
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "dict");
                                                                    FStar_Tactics_NamedView.sort
                                                                    = cod1;
                                                                    FStar_Tactics_NamedView.qual
                                                                    =
                                                                    (FStarC_Reflection_V2_Data.Q_Meta
                                                                    tcr);
                                                                    FStar_Tactics_NamedView.attrs
                                                                    = []
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___48)
                                                                    (fun
                                                                    uu___49
                                                                    ->
                                                                    (fun
                                                                    tcdict ->
                                                                    let uu___49
                                                                    =
                                                                    let uu___50
                                                                    =
                                                                    FStar_Tactics_V2_Derived.cur_module
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    uu___50)
                                                                    (fun
                                                                    uu___51
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___52
                                                                    ->
                                                                    (op_At ())
                                                                    uu___51
                                                                    [
                                                                    Prims.strcat
                                                                    base s])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___49)
                                                                    (fun
                                                                    uu___50
                                                                    ->
                                                                    (fun
                                                                    proj_name
                                                                    ->
                                                                    let uu___50
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___51
                                                                    ->
                                                                    FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    proj_name)))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___50)
                                                                    (fun
                                                                    uu___51
                                                                    ->
                                                                    (fun proj
                                                                    ->
                                                                    let uu___51
                                                                    =
                                                                    let uu___52
                                                                    =
                                                                    let uu___53
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.top_env
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___53)
                                                                    (fun
                                                                    uu___54
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___55
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.lookup_typ
                                                                    uu___54
                                                                    proj_name)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (23)))))
                                                                    (Obj.magic
                                                                    uu___52)
                                                                    (fun
                                                                    uu___53
                                                                    ->
                                                                    (fun
                                                                    uu___53
                                                                    ->
                                                                    match uu___53
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
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___54
                                                                    -> se1))))
                                                                    uu___53) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___51)
                                                                    (fun
                                                                    uu___52
                                                                    ->
                                                                    (fun
                                                                    proj_se
                                                                    ->
                                                                    let uu___52
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___53
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.sigelt_attrs
                                                                    proj_se)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___52)
                                                                    (fun
                                                                    uu___53
                                                                    ->
                                                                    (fun
                                                                    proj_attrs
                                                                    ->
                                                                    let uu___53
                                                                    =
                                                                    let uu___54
                                                                    =
                                                                    FStar_Tactics_NamedView.inspect_sigelt
                                                                    proj_se in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (500))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    uu___54)
                                                                    (fun
                                                                    uu___55
                                                                    ->
                                                                    (fun
                                                                    uu___55
                                                                    ->
                                                                    match uu___55
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_NamedView.Sg_Let
                                                                    {
                                                                    FStar_Tactics_NamedView.isrec
                                                                    = uu___56;
                                                                    FStar_Tactics_NamedView.lbs
                                                                    = lbs;_}
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_SyntaxHelpers.lookup_lb
                                                                    lbs
                                                                    proj_name)
                                                                    | 
                                                                    uu___56
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "mk_class: proj not Sg_Let?"))
                                                                    uu___55) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (500))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___53)
                                                                    (fun
                                                                    uu___54
                                                                    ->
                                                                    (fun
                                                                    proj_lb
                                                                    ->
                                                                    let uu___54
                                                                    =
                                                                    debug'
                                                                    (fun
                                                                    uu___55
                                                                    ->
                                                                    let uu___56
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.term_to_string
                                                                    proj_lb.FStar_Tactics_NamedView.lb_typ in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___56)
                                                                    (fun
                                                                    uu___57
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___58
                                                                    ->
                                                                    Prims.strcat
                                                                    "proj_ty = "
                                                                    uu___57))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___54)
                                                                    (fun
                                                                    uu___55
                                                                    ->
                                                                    (fun
                                                                    uu___55
                                                                    ->
                                                                    let uu___56
                                                                    =
                                                                    let uu___57
                                                                    =
                                                                    FStar_Tactics_V2_SyntaxHelpers.collect_arr_bs
                                                                    proj_lb.FStar_Tactics_NamedView.lb_typ in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (504))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    uu___57)
                                                                    (fun
                                                                    uu___58
                                                                    ->
                                                                    (fun
                                                                    uu___58
                                                                    ->
                                                                    match uu___58
                                                                    with
                                                                    | 
                                                                    (bs1,
                                                                    cod2) ->
                                                                    let uu___59
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___60
                                                                    ->
                                                                    FStar_List_Tot_Base.splitAt
                                                                    (FStar_List_Tot_Base.length
                                                                    params)
                                                                    bs1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    uu___59)
                                                                    (fun
                                                                    uu___60
                                                                    ->
                                                                    (fun
                                                                    uu___60
                                                                    ->
                                                                    match uu___60
                                                                    with
                                                                    | 
                                                                    (ps, bs2)
                                                                    ->
                                                                    (match bs2
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "mk_class: impossible, no binders")
                                                                    | 
                                                                    b1::bs'
                                                                    ->
                                                                    let uu___61
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___62
                                                                    ->
                                                                    binder_set_meta
                                                                    b1 tcr)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    uu___61)
                                                                    (fun
                                                                    uu___62
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
                                                                    uu___62))))
                                                                    uu___60)))
                                                                    uu___58) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (504))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___56)
                                                                    (fun
                                                                    uu___57
                                                                    ->
                                                                    (fun ty1
                                                                    ->
                                                                    let uu___57
                                                                    =
                                                                    let uu___58
                                                                    =
                                                                    FStar_Tactics_V2_SyntaxHelpers.collect_abs
                                                                    proj_lb.FStar_Tactics_NamedView.lb_def in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (520))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___58)
                                                                    (fun
                                                                    uu___59
                                                                    ->
                                                                    (fun
                                                                    uu___59
                                                                    ->
                                                                    match uu___59
                                                                    with
                                                                    | 
                                                                    (bs1,
                                                                    body) ->
                                                                    let uu___60
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___61
                                                                    ->
                                                                    FStar_List_Tot_Base.splitAt
                                                                    (FStar_List_Tot_Base.length
                                                                    params)
                                                                    bs1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (520))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___60)
                                                                    (fun
                                                                    uu___61
                                                                    ->
                                                                    (fun
                                                                    uu___61
                                                                    ->
                                                                    match uu___61
                                                                    with
                                                                    | 
                                                                    (ps, bs2)
                                                                    ->
                                                                    (match bs2
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "mk_class: impossible, no binders")
                                                                    | 
                                                                    b1::bs'
                                                                    ->
                                                                    let uu___62
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___63
                                                                    ->
                                                                    binder_set_meta
                                                                    b1 tcr)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (520))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (520))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___62)
                                                                    (fun
                                                                    uu___63
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
                                                                    uu___63))))
                                                                    uu___61)))
                                                                    uu___59) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (520))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___57)
                                                                    (fun
                                                                    uu___58
                                                                    ->
                                                                    (fun def
                                                                    ->
                                                                    let uu___58
                                                                    =
                                                                    debug'
                                                                    (fun
                                                                    uu___59
                                                                    ->
                                                                    let uu___60
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.term_to_string
                                                                    def in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___60)
                                                                    (fun
                                                                    uu___61
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___62
                                                                    ->
                                                                    Prims.strcat
                                                                    "def = "
                                                                    uu___61))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___58)
                                                                    (fun
                                                                    uu___59
                                                                    ->
                                                                    (fun
                                                                    uu___59
                                                                    ->
                                                                    let uu___60
                                                                    =
                                                                    debug'
                                                                    (fun
                                                                    uu___61
                                                                    ->
                                                                    let uu___62
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.term_to_string
                                                                    ty1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (613))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___62)
                                                                    (fun
                                                                    uu___63
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___64
                                                                    ->
                                                                    Prims.strcat
                                                                    "ty  = "
                                                                    uu___63))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___60)
                                                                    (fun
                                                                    uu___61
                                                                    ->
                                                                    (fun
                                                                    uu___61
                                                                    ->
                                                                    let uu___62
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___63
                                                                    -> ty1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (525))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (525))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (525))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___62)
                                                                    (fun
                                                                    uu___63
                                                                    ->
                                                                    (fun ty2
                                                                    ->
                                                                    let uu___63
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___64
                                                                    -> def)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (526))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (526))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (526))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___63)
                                                                    (fun
                                                                    uu___64
                                                                    ->
                                                                    (fun def1
                                                                    ->
                                                                    let uu___64
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___65
                                                                    -> sfv)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (527))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (527))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (527))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___64)
                                                                    (fun
                                                                    uu___65
                                                                    ->
                                                                    (fun sfv1
                                                                    ->
                                                                    let uu___65
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___66
                                                                    ->
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
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (529))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (529))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (529))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___65)
                                                                    (fun
                                                                    uu___66
                                                                    ->
                                                                    (fun lb
                                                                    ->
                                                                    let uu___66
                                                                    =
                                                                    FStar_Tactics_NamedView.pack_sigelt
                                                                    (FStar_Tactics_NamedView.Sg_Let
                                                                    {
                                                                    FStar_Tactics_NamedView.isrec
                                                                    = false;
                                                                    FStar_Tactics_NamedView.lbs
                                                                    = [lb]
                                                                    }) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (532))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (532))
                                                                    (Prims.of_int (72)))))
                                                                    (Obj.magic
                                                                    uu___66)
                                                                    (fun se1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___67
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.set_sigelt_attrs
                                                                    ((op_At
                                                                    ())
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Typeclasses";
                                                                    "tcmethod"])))
                                                                    ::
                                                                    proj_attrs)
                                                                    b.FStar_Tactics_NamedView.attrs)
                                                                    (FStarC_Reflection_V2_Builtins.set_sigelt_quals
                                                                    to_propagate
                                                                    se1)))))
                                                                    uu___66)))
                                                                    uu___65)))
                                                                    uu___64)))
                                                                    uu___63)))
                                                                    uu___61)))
                                                                    uu___59)))
                                                                    uu___58)))
                                                                    uu___57)))
                                                                    uu___55)))
                                                                    uu___54)))
                                                                    uu___53)))
                                                                    uu___52)))
                                                                    uu___51)))
                                                                    uu___50)))
                                                                    uu___49)))
                                                                    uu___48)))
                                                                    uu___47)))
                                                                    uu___46)))
                                                                    uu___45)))
                                                                    uu___43)))
                                                                    uu___42))
                                                                    (filter_no_method_binders
                                                                    bs)))
                                                                    uu___41)))
                                                                    uu___39)))
                                                                    uu___37)))
                                                                    uu___35)))
                                                                    uu___33)))
                                                                    uu___31)))
                                                                    uu___29)))
                                                                    uu___28)))
                                                                    uu___26)))
                                                                    uu___24)))
                                                                    uu___22)))
                                                                    uu___20)))
                                                                    uu___19)))
                                                                    uu___17)))
                                                                    uu___15)))
                                                                    uu___13)))
                                                                    uu___11)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                           uu___7))) uu___5)))
                                 uu___3))) uu___2))) uu___1)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Typeclasses.mk_class" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Typeclasses.mk_class (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 mk_class)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_sigelt) psc
               ncb us args)
let solve : 'a . 'a -> 'a = fun ev -> ev
let solve_debug : 'a . 'a -> 'a = fun ev -> ev
