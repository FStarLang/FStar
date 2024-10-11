open Prims
let (debug :
  (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    let uu___ = FStarC_Tactics_V2_Builtins.debugging () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (30)) (Prims.of_int (5)) (Prims.of_int (30))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (30)) (Prims.of_int (2)) (Prims.of_int (31))
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
                               (Prims.of_int (31)) (Prims.of_int (10))
                               (Prims.of_int (31)) (Prims.of_int (16)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.Typeclasses.fst"
                               (Prims.of_int (31)) (Prims.of_int (4))
                               (Prims.of_int (31)) (Prims.of_int (16)))))
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
let op_At :
  'uuuuu .
    unit -> 'uuuuu Prims.list -> 'uuuuu Prims.list -> 'uuuuu Prims.list
  = fun uu___ -> FStar_List_Tot_Base.op_At
type st_t =
  {
  seen: FStar_Tactics_NamedView.term Prims.list ;
  glb:
    (FStarC_Reflection_Types.sigelt * FStarC_Reflection_Types.fv) Prims.list ;
  fuel: Prims.int }
let (__proj__Mkst_t__item__seen :
  st_t -> FStar_Tactics_NamedView.term Prims.list) =
  fun projectee -> match projectee with | { seen; glb; fuel;_} -> seen
let (__proj__Mkst_t__item__glb :
  st_t ->
    (FStarC_Reflection_Types.sigelt * FStarC_Reflection_Types.fv) Prims.list)
  = fun projectee -> match projectee with | { seen; glb; fuel;_} -> glb
let (__proj__Mkst_t__item__fuel : st_t -> Prims.int) =
  fun projectee -> match projectee with | { seen; glb; fuel;_} -> fuel
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
let rec (maybe_intros : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = FStar_Tactics_V2_Derived.cur_goal () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (114)) (Prims.of_int (10)) (Prims.of_int (114))
               (Prims.of_int (21)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (115)) (Prims.of_int (2)) (Prims.of_int (119))
               (Prims.of_int (11))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun g ->
            let uu___2 = FStar_Tactics_NamedView.inspect g in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (115)) (Prims.of_int (8))
                          (Prims.of_int (115)) (Prims.of_int (17)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (115)) (Prims.of_int (2))
                          (Prims.of_int (119)) (Prims.of_int (11)))))
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
                                              (Prims.of_int (117))
                                              (Prims.of_int (11))
                                              (Prims.of_int (117))
                                              (Prims.of_int (21)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Typeclasses.fst"
                                              (Prims.of_int (117))
                                              (Prims.of_int (4))
                                              (Prims.of_int (117))
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
                                            (Prims.of_int (117))
                                            (Prims.of_int (4))
                                            (Prims.of_int (117))
                                            (Prims.of_int (21)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.Typeclasses.fst"
                                            (Prims.of_int (118))
                                            (Prims.of_int (4))
                                            (Prims.of_int (118))
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
                 (Prims.of_int (138)) (Prims.of_int (8)) (Prims.of_int (138))
                 (Prims.of_int (13)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                 (Prims.of_int (138)) (Prims.of_int (2)) (Prims.of_int (152))
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
                                          (Prims.of_int (141))
                                          (Prims.of_int (12))
                                          (Prims.of_int (141))
                                          (Prims.of_int (16)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.Typeclasses.fst"
                                          (Prims.of_int (141))
                                          (Prims.of_int (12))
                                          (Prims.of_int (141))
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
                                                     (Prims.of_int (141))
                                                     (Prims.of_int (18))
                                                     (Prims.of_int (141))
                                                     (Prims.of_int (35)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.Typeclasses.fst"
                                                     (Prims.of_int (141))
                                                     (Prims.of_int (12))
                                                     (Prims.of_int (141))
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
                                        (Prims.of_int (141))
                                        (Prims.of_int (12))
                                        (Prims.of_int (141))
                                        (Prims.of_int (35)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.Typeclasses.fst"
                                        (Prims.of_int (141))
                                        (Prims.of_int (6))
                                        (Prims.of_int (143))
                                        (Prims.of_int (17)))))
                               (Obj.magic uu___3)
                               (fun uu___4 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___5 ->
                                       match uu___4 with
                                       | (FStar_Pervasives_Native.Some hd1,
                                          FStar_Pervasives_Native.Some tl1)
                                           ->
                                           FStar_Pervasives_Native.Some (hd1
                                             :: tl1)
                                       | uu___6 ->
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
               (Prims.of_int (155)) (Prims.of_int (14)) (Prims.of_int (155))
               (Prims.of_int (29)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (155)) (Prims.of_int (32)) (Prims.of_int (169))
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
                                      (Prims.of_int (160))
                                      (Prims.of_int (12))
                                      (Prims.of_int (160))
                                      (Prims.of_int (28)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.Typeclasses.fst"
                                      (Prims.of_int (160)) (Prims.of_int (6))
                                      (Prims.of_int (167))
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
          (st_t -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
            (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun st ->
    fun g ->
      fun t ->
        fun typ ->
          fun k ->
            let uu___ =
              let uu___1 =
                FStar_Tactics_Util.mapi
                  (fun uu___3 ->
                     fun uu___2 ->
                       (fun i ->
                          fun uu___2 ->
                            Obj.magic
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___3 ->
                                    match uu___2 with
                                    | (uu___4, b) -> if b then [i] else [])))
                         uu___3 uu___2) g.args_and_uvars in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                         (Prims.of_int (174)) (Prims.of_int (26))
                         (Prims.of_int (174)) (Prims.of_int (102)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                         (Prims.of_int (174)) (Prims.of_int (26))
                         (Prims.of_int (174)) (Prims.of_int (122)))))
                (Obj.magic uu___1)
                (fun uu___2 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___3 -> FStar_List_Tot_Base.flatten uu___2)) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                       (Prims.of_int (174)) (Prims.of_int (26))
                       (Prims.of_int (174)) (Prims.of_int (122)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                       (Prims.of_int (177)) (Prims.of_int (4))
                       (Prims.of_int (199)) (Prims.of_int (13)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun unresolved_args ->
                    let uu___1 =
                      let uu___2 = res_typ typ in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.Typeclasses.fst"
                                 (Prims.of_int (177)) (Prims.of_int (18))
                                 (Prims.of_int (177)) (Prims.of_int (31)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.Typeclasses.fst"
                                 (Prims.of_int (177)) (Prims.of_int (10))
                                 (Prims.of_int (177)) (Prims.of_int (31)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun uu___3 -> Obj.magic (head_of uu___3)) uu___3) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.Typeclasses.fst"
                                  (Prims.of_int (177)) (Prims.of_int (10))
                                  (Prims.of_int (177)) (Prims.of_int (31)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.Typeclasses.fst"
                                  (Prims.of_int (177)) (Prims.of_int (4))
                                  (Prims.of_int (199)) (Prims.of_int (13)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            (fun uu___2 ->
                               match uu___2 with
                               | FStar_Pervasives_Native.None ->
                                   let uu___3 =
                                     debug
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
                                                       (Prims.of_int (179))
                                                       (Prims.of_int (53))
                                                       (Prims.of_int (179))
                                                       (Prims.of_int (69)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.Typeclasses.fst"
                                                       (Prims.of_int (179))
                                                       (Prims.of_int (53))
                                                       (Prims.of_int (179))
                                                       (Prims.of_int (103)))))
                                              (Obj.magic uu___6)
                                              (fun uu___7 ->
                                                 (fun uu___7 ->
                                                    let uu___8 =
                                                      let uu___9 =
                                                        FStarC_Tactics_V2_Builtins.term_to_string
                                                          typ in
                                                      FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.Typeclasses.fst"
                                                                 (Prims.of_int (179))
                                                                 (Prims.of_int (85))
                                                                 (Prims.of_int (179))
                                                                 (Prims.of_int (103)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Prims.fst"
                                                                 (Prims.of_int (611))
                                                                 (Prims.of_int (19))
                                                                 (Prims.of_int (611))
                                                                 (Prims.of_int (31)))))
                                                        (Obj.magic uu___9)
                                                        (fun uu___10 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___11 ->
                                                                Prims.strcat
                                                                  "    typ="
                                                                  uu___10)) in
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.Typeclasses.fst"
                                                                  (Prims.of_int (179))
                                                                  (Prims.of_int (72))
                                                                  (Prims.of_int (179))
                                                                  (Prims.of_int (103)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Prims.fst"
                                                                  (Prims.of_int (611))
                                                                  (Prims.of_int (19))
                                                                  (Prims.of_int (611))
                                                                  (Prims.of_int (31)))))
                                                         (Obj.magic uu___8)
                                                         (fun uu___9 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___10 ->
                                                                 Prims.strcat
                                                                   uu___7
                                                                   uu___9))))
                                                   uu___7) in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.Typeclasses.fst"
                                                     (Prims.of_int (179))
                                                     (Prims.of_int (53))
                                                     (Prims.of_int (179))
                                                     (Prims.of_int (103)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Prims.fst"
                                                     (Prims.of_int (611))
                                                     (Prims.of_int (19))
                                                     (Prims.of_int (611))
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
                                                 (Prims.of_int (179))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (179))
                                                 (Prims.of_int (104)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.Typeclasses.fst"
                                                 (Prims.of_int (180))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (180))
                                                 (Prims.of_int (18)))))
                                        (Obj.magic uu___3)
                                        (fun uu___4 ->
                                           FStar_Tactics_Effect.raise NoInst))
                               | FStar_Pervasives_Native.Some fv' ->
                                   let uu___3 =
                                     if
                                       Prims.op_Negation
                                         (fv_eq fv' g.head_fv)
                                     then
                                       Obj.magic
                                         (FStar_Tactics_Effect.raise NoInst)
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
                                                 (Prims.of_int (182))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (183))
                                                 (Prims.of_int (20)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.Typeclasses.fst"
                                                 (Prims.of_int (184))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (199))
                                                 (Prims.of_int (13)))))
                                        (Obj.magic uu___3)
                                        (fun uu___4 ->
                                           (fun uu___4 ->
                                              let uu___5 =
                                                debug
                                                  (fun uu___6 ->
                                                     let uu___7 =
                                                       FStarC_Tactics_V2_Builtins.term_to_string
                                                         t in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.Typeclasses.fst"
                                                                (Prims.of_int (184))
                                                                (Prims.of_int (65))
                                                                (Prims.of_int (184))
                                                                (Prims.of_int (81)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Prims.fst"
                                                                (Prims.of_int (611))
                                                                (Prims.of_int (19))
                                                                (Prims.of_int (611))
                                                                (Prims.of_int (31)))))
                                                       (Obj.magic uu___7)
                                                       (fun uu___8 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___9 ->
                                                               Prims.strcat
                                                                 "Trying to apply hypothesis/instance: "
                                                                 uu___8))) in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.Typeclasses.fst"
                                                            (Prims.of_int (184))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (184))
                                                            (Prims.of_int (82)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.Typeclasses.fst"
                                                            (Prims.of_int (185))
                                                            (Prims.of_int (6))
                                                            (Prims.of_int (199))
                                                            (Prims.of_int (13)))))
                                                   (Obj.magic uu___5)
                                                   (fun uu___6 ->
                                                      (fun uu___6 ->
                                                         Obj.magic
                                                           (FStar_Tactics_V2_Derived.seq
                                                              (fun uu___7 ->
                                                                 (fun uu___7
                                                                    ->
                                                                    if
                                                                    (Prims.uu___is_Cons
                                                                    unresolved_args)
                                                                    &&
                                                                    (FStar_Pervasives_Native.uu___is_None
                                                                    g.fundeps)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Will not continue as there are unresolved args (and no fundeps)"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    (Prims.uu___is_Cons
                                                                    unresolved_args)
                                                                    &&
                                                                    (FStar_Pervasives_Native.uu___is_Some
                                                                    g.fundeps)
                                                                    then
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    g.fundeps)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (193))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    fundeps
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    debug
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    "checking fundeps")))
                                                                    uu___12) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (190))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (54)))))
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
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_List_Tot_Base.for_all
                                                                    (fun i ->
                                                                    FStar_List_Tot_Base.mem
                                                                    i fundeps)
                                                                    unresolved_args)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (191))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    all_good
                                                                    ->
                                                                    if
                                                                    all_good
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.apply
                                                                    t))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "fundeps")))
                                                                    uu___14)))
                                                                    uu___12)))
                                                                    uu___10)
                                                                    else
                                                                    FStar_Tactics_V2_Derived.apply_noinst
                                                                    t)))
                                                                   uu___7)
                                                              (fun uu___7 ->
                                                                 let uu___8 =
                                                                   debug
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___10
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.dump
                                                                    "next" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    "apply seems to have worked"))) in
                                                                 FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (67)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (12)))))
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
                                                                    ->
                                                                    {
                                                                    seen =
                                                                    (st.seen);
                                                                    glb =
                                                                    (st.glb);
                                                                    fuel =
                                                                    (st.fuel
                                                                    -
                                                                    Prims.int_one)
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (12)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun st1
                                                                    ->
                                                                    Obj.magic
                                                                    (k st1))
                                                                    uu___11)))
                                                                    uu___9))))
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
            debug
              (fun uu___2 ->
                 let uu___3 = FStarC_Tactics_V2_Builtins.term_to_string g.g in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.Typeclasses.fst"
                            (Prims.of_int (202)) (Prims.of_int (40))
                            (Prims.of_int (202)) (Prims.of_int (58)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___3)
                   (fun uu___4 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___5 -> Prims.strcat "local, goal = " uu___4))) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                     (Prims.of_int (202)) (Prims.of_int (4))
                     (Prims.of_int (202)) (Prims.of_int (59)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                     (Prims.of_int (202)) (Prims.of_int (60))
                     (Prims.of_int (206)) (Prims.of_int (12)))))
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
                               (Prims.of_int (203)) (Prims.of_int (25))
                               (Prims.of_int (203)) (Prims.of_int (37)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.Typeclasses.fst"
                               (Prims.of_int (203)) (Prims.of_int (13))
                               (Prims.of_int (203)) (Prims.of_int (37)))))
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
                                (Prims.of_int (203)) (Prims.of_int (13))
                                (Prims.of_int (203)) (Prims.of_int (37)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.Typeclasses.fst"
                                (Prims.of_int (204)) (Prims.of_int (4))
                                (Prims.of_int (206)) (Prims.of_int (12)))))
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
                                       b.FStarC_Reflection_V2_Data.sort3 k)
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
            debug
              (fun uu___2 ->
                 let uu___3 = FStarC_Tactics_V2_Builtins.term_to_string g.g in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.Typeclasses.fst"
                            (Prims.of_int (209)) (Prims.of_int (41))
                            (Prims.of_int (209)) (Prims.of_int (59)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___3)
                   (fun uu___4 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___5 -> Prims.strcat "global, goal = " uu___4))) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                     (Prims.of_int (209)) (Prims.of_int (4))
                     (Prims.of_int (209)) (Prims.of_int (60)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                     (Prims.of_int (210)) (Prims.of_int (4))
                     (Prims.of_int (213)) (Prims.of_int (16)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               (fun uu___2 ->
                  Obj.magic
                    (first
                       (fun uu___3 ->
                          match uu___3 with
                          | (se, fv) ->
                              let uu___4 =
                                let uu___5 =
                                  FStar_Tactics_V2_Derived.cur_env () in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Typeclasses.fst"
                                           (Prims.of_int (211))
                                           (Prims.of_int (27))
                                           (Prims.of_int (211))
                                           (Prims.of_int (38)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Typeclasses.fst"
                                           (Prims.of_int (211))
                                           (Prims.of_int (24))
                                           (Prims.of_int (211))
                                           (Prims.of_int (58)))))
                                  (Obj.magic uu___5)
                                  (fun uu___6 ->
                                     (fun uu___6 ->
                                        Obj.magic
                                          (FStarC_Tactics_V2_Builtins.tc
                                             uu___6
                                             (FStar_Tactics_NamedView.pack
                                                (FStar_Tactics_NamedView.Tv_FVar
                                                   fv)))) uu___6) in
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Typeclasses.fst"
                                         (Prims.of_int (211))
                                         (Prims.of_int (24))
                                         (Prims.of_int (211))
                                         (Prims.of_int (58)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Typeclasses.fst"
                                         (Prims.of_int (212))
                                         (Prims.of_int (14))
                                         (Prims.of_int (212))
                                         (Prims.of_int (52)))))
                                (Obj.magic uu___4)
                                (fun uu___5 ->
                                   (fun typ ->
                                      Obj.magic
                                        (trywith st g
                                           (FStar_Tactics_NamedView.pack
                                              (FStar_Tactics_NamedView.Tv_FVar
                                                 fv)) typ k)) uu___5)) 
                       st.glb)) uu___2)
exception Next 
let (uu___is_Next : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Next -> true | uu___ -> false
let (try_trivial :
  st_t ->
    tc_goal ->
      (st_t -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
        unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun st ->
    fun g ->
      fun k ->
        fun uu___ ->
          let uu___1 = FStar_Tactics_NamedView.inspect g.g in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                     (Prims.of_int (217)) (Prims.of_int (8))
                     (Prims.of_int (217)) (Prims.of_int (11)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                     (Prims.of_int (217)) (Prims.of_int (2))
                     (Prims.of_int (222)) (Prims.of_int (19)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               (fun uu___2 ->
                  match uu___2 with
                  | FStar_Tactics_NamedView.Tv_FVar fv ->
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
                            else Obj.repr (FStar_Tactics_Effect.raise Next)))
                  | uu___3 ->
                      Obj.magic (Obj.repr (FStar_Tactics_Effect.raise Next)))
                 uu___2)
let op_Less_Bar_Greater :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
        unit -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t1 ->
    fun t2 ->
      fun uu___ ->
        FStar_Tactics_V2_Derived.try_with
          (fun uu___1 -> match () with | () -> t1 ()) (fun uu___1 -> t2 ())
let rec (tcresolve' : st_t -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun st ->
    let uu___ =
      if st.fuel <= Prims.int_zero
      then Obj.magic (FStar_Tactics_Effect.raise NoInst)
      else Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ())) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (234)) (Prims.of_int (4)) (Prims.of_int (235))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (236)) (Prims.of_int (4)) (Prims.of_int (265))
               (Prims.of_int (33))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            let uu___2 =
              debug
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
                          (Prims.of_int (236)) (Prims.of_int (4))
                          (Prims.of_int (236)) (Prims.of_int (55)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (238)) (Prims.of_int (4))
                          (Prims.of_int (265)) (Prims.of_int (33)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun uu___3 ->
                       let uu___4 = maybe_intros () in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Typeclasses.fst"
                                     (Prims.of_int (238)) (Prims.of_int (4))
                                     (Prims.of_int (238)) (Prims.of_int (18)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Typeclasses.fst"
                                     (Prims.of_int (238)) (Prims.of_int (19))
                                     (Prims.of_int (265)) (Prims.of_int (33)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               (fun uu___5 ->
                                  let uu___6 =
                                    FStar_Tactics_V2_Derived.cur_goal () in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (239))
                                                (Prims.of_int (12))
                                                (Prims.of_int (239))
                                                (Prims.of_int (23)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (242))
                                                (Prims.of_int (4))
                                                (Prims.of_int (265))
                                                (Prims.of_int (33)))))
                                       (Obj.magic uu___6)
                                       (fun uu___7 ->
                                          (fun g ->
                                             let uu___7 =
                                               if
                                                 FStar_List_Tot_Base.existsb
                                                   (FStar_Reflection_TermEq_Simple.term_eq
                                                      g) st.seen
                                               then
                                                 Obj.magic
                                                   (Obj.repr
                                                      (let uu___8 =
                                                         debug
                                                           (fun uu___9 ->
                                                              (fun uu___9 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> "loop")))
                                                                uu___9) in
                                                       FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.Typeclasses.fst"
                                                                  (Prims.of_int (243))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (243))
                                                                  (Prims.of_int (30)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.Typeclasses.fst"
                                                                  (Prims.of_int (244))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (244))
                                                                  (Prims.of_int (18)))))
                                                         (Obj.magic uu___8)
                                                         (fun uu___9 ->
                                                            FStar_Tactics_Effect.raise
                                                              NoInst)))
                                               else
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___9 -> ()))) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Typeclasses.fst"
                                                           (Prims.of_int (242))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (245))
                                                           (Prims.of_int (5)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Typeclasses.fst"
                                                           (Prims.of_int (247))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (265))
                                                           (Prims.of_int (33)))))
                                                  (Obj.magic uu___7)
                                                  (fun uu___8 ->
                                                     (fun uu___8 ->
                                                        let uu___9 =
                                                          FStar_Tactics_V2_SyntaxHelpers.hua
                                                            g in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (15)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (33)))))
                                                             (Obj.magic
                                                                uu___9)
                                                             (fun uu___10 ->
                                                                (fun uu___10
                                                                   ->
                                                                   match uu___10
                                                                   with
                                                                   | 
                                                                   FStar_Pervasives_Native.None
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    debug
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    "Goal does not look like a typeclass")))
                                                                    uu___12) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.raise
                                                                    NoInst))
                                                                   | 
                                                                   FStar_Pervasives_Native.Some
                                                                    (head_fv,
                                                                    us, args)
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    FStar_Tactics_V2_Derived.cur_env
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.lookup_typ
                                                                    uu___13
                                                                    (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                    head_fv))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun c_se
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    match c_se
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Pervasives_Native.None)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    se ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (extract_fundeps
                                                                    se)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    fundeps
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    FStar_Tactics_Util.map
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    match uu___14
                                                                    with
                                                                    | 
                                                                    (a, q) ->
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.free_uvars
                                                                    a in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    Prims.uu___is_Cons
                                                                    uu___17)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    ((a, q),
                                                                    uu___16))))
                                                                    args in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (260))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    args_and_uvars
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    {
                                                                    seen = (g
                                                                    ::
                                                                    (st.seen));
                                                                    glb =
                                                                    (st.glb);
                                                                    fuel =
                                                                    (st.fuel)
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun st1
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
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
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun g1
                                                                    ->
                                                                    Obj.magic
                                                                    (op_Less_Bar_Greater
                                                                    (op_Less_Bar_Greater
                                                                    (try_trivial
                                                                    st1 g1
                                                                    tcresolve')
                                                                    (local
                                                                    st1 g1
                                                                    tcresolve'))
                                                                    (global
                                                                    st1 g1
                                                                    tcresolve')
                                                                    ()))
                                                                    uu___16)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                  uu___10)))
                                                       uu___8))) uu___7)))
                                 uu___5))) uu___3))) uu___1)
let (tcresolve : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 =
      debug
        (fun uu___2 ->
           let uu___3 = FStarC_Tactics_V2_Builtins.dump "" in
           FStar_Tactics_Effect.tac_bind
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                      (Prims.of_int (270)) (Prims.of_int (21))
                      (Prims.of_int (270)) (Prims.of_int (28)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                      (Prims.of_int (270)) (Prims.of_int (30))
                      (Prims.of_int (270)) (Prims.of_int (53)))))
             (Obj.magic uu___3)
             (fun uu___4 ->
                FStar_Tactics_Effect.lift_div_tac
                  (fun uu___5 -> "tcresolve entry point"))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (270)) (Prims.of_int (4)) (Prims.of_int (270))
               (Prims.of_int (54)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (271)) (Prims.of_int (4)) (Prims.of_int (303))
               (Prims.of_int (18))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            let uu___3 = FStarC_Tactics_V2_Builtins.norm [] in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (271)) (Prims.of_int (4))
                          (Prims.of_int (271)) (Prims.of_int (11)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (271)) (Prims.of_int (12))
                          (Prims.of_int (303)) (Prims.of_int (18)))))
                 (Obj.magic uu___3)
                 (fun uu___4 ->
                    (fun uu___4 ->
                       let uu___5 = FStar_Tactics_V2_Derived.cur_witness () in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Typeclasses.fst"
                                     (Prims.of_int (272)) (Prims.of_int (12))
                                     (Prims.of_int (272)) (Prims.of_int (26)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Typeclasses.fst"
                                     (Prims.of_int (273)) (Prims.of_int (4))
                                     (Prims.of_int (303)) (Prims.of_int (18)))))
                            (Obj.magic uu___5)
                            (fun uu___6 ->
                               (fun w ->
                                  let uu___6 =
                                    FStarC_Tactics_V2_Builtins.set_dump_on_failure
                                      false in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (273))
                                                (Prims.of_int (4))
                                                (Prims.of_int (273))
                                                (Prims.of_int (29)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (276))
                                                (Prims.of_int (4))
                                                (Prims.of_int (303))
                                                (Prims.of_int (18)))))
                                       (Obj.magic uu___6)
                                       (fun uu___7 ->
                                          (fun uu___7 ->
                                             let uu___8 = maybe_intros () in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Typeclasses.fst"
                                                           (Prims.of_int (276))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (276))
                                                           (Prims.of_int (19)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Typeclasses.fst"
                                                           (Prims.of_int (276))
                                                           (Prims.of_int (20))
                                                           (Prims.of_int (303))
                                                           (Prims.of_int (18)))))
                                                  (Obj.magic uu___8)
                                                  (fun uu___9 ->
                                                     (fun uu___9 ->
                                                        let uu___10 =
                                                          let uu___11 =
                                                            FStar_Tactics_V2_Derived.cur_env
                                                              () in
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (56)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (56)))))
                                                            (Obj.magic
                                                               uu___11)
                                                            (fun uu___12 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___13
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.lookup_attr_ses
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Typeclasses";
                                                                    "tcinstance"])))
                                                                    uu___12)) in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (56)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (281))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (18)))))
                                                             (Obj.magic
                                                                uu___10)
                                                             (fun uu___11 ->
                                                                (fun glb ->
                                                                   let uu___11
                                                                    =
                                                                    FStar_Tactics_Util.concatMap
                                                                    (fun se
                                                                    ->
                                                                    FStar_Tactics_Util.concatMap
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun fv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    [
                                                                    (se, fv)])))
                                                                    uu___12)
                                                                    (sigelt_name
                                                                    se)) glb in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (284))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun glb1
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    {
                                                                    seen = [];
                                                                    glb =
                                                                    glb1;
                                                                    fuel =
                                                                    (Prims.of_int (16))
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun st0
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.try_with
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    let uu___14
                                                                    =
                                                                    tcresolve'
                                                                    st0 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (debug
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.term_to_string
                                                                    w in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    Prims.strcat
                                                                    "Solved to:\n\t"
                                                                    uu___18)))))
                                                                    uu___15))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    NoInst ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    FStar_Tactics_V2_Derived.cur_goal
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V2_Builtins.term_to_doc
                                                                    uu___19))
                                                                    uu___19) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStarC_Pprint.bquotes
                                                                    uu___18)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStarC_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (FStarC_Pprint.arbitrary_string
                                                                    "Could not solve typeclass constraint")
                                                                    uu___17)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    [uu___16])) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (300))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_V2_Derived.fail_doc
                                                                    uu___15)))
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
                                                                    FStarC_Pprint.arbitrary_string
                                                                    "Typeclass resolution failed."]
                                                                    msg) r))
                                                                    | 
                                                                    e ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.raise
                                                                    e)))
                                                                    uu___13)))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                  uu___11)))
                                                       uu___9))) uu___7)))
                                 uu___6))) uu___4))) uu___2)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.Typeclasses.tcresolve"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Typeclasses.tcresolve (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 tcresolve)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
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
                                  (Prims.of_int (312)) (Prims.of_int (30))
                                  (Prims.of_int (312)) (Prims.of_int (46)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.Typeclasses.fst"
                                  (Prims.of_int (312)) (Prims.of_int (20))
                                  (Prims.of_int (312)) (Prims.of_int (47)))))
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
                                (Prims.of_int (312)) (Prims.of_int (20))
                                (Prims.of_int (312)) (Prims.of_int (47)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "dummy" Prims.int_zero
                                Prims.int_zero Prims.int_zero Prims.int_zero)))
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
               (Prims.of_int (336)) (Prims.of_int (13)) (Prims.of_int (336))
               (Prims.of_int (26)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (336)) (Prims.of_int (29)) (Prims.of_int (426))
               (Prims.of_int (5))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun ns ->
            let uu___1 =
              let uu___2 = FStarC_Tactics_V2_Builtins.top_env () in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                         (Prims.of_int (337)) (Prims.of_int (23))
                         (Prims.of_int (337)) (Prims.of_int (35)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                         (Prims.of_int (337)) (Prims.of_int (12))
                         (Prims.of_int (337)) (Prims.of_int (38)))))
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
                          (Prims.of_int (337)) (Prims.of_int (12))
                          (Prims.of_int (337)) (Prims.of_int (38)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (338)) (Prims.of_int (4))
                          (Prims.of_int (426)) (Prims.of_int (5)))))
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
                                     (Prims.of_int (338)) (Prims.of_int (4))
                                     (Prims.of_int (338)) (Prims.of_int (19)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Typeclasses.fst"
                                     (Prims.of_int (338)) (Prims.of_int (20))
                                     (Prims.of_int (426)) (Prims.of_int (5)))))
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
                                                (Prims.of_int (339))
                                                (Prims.of_int (18))
                                                (Prims.of_int (339))
                                                (Prims.of_int (19)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (338))
                                                (Prims.of_int (20))
                                                (Prims.of_int (426))
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
                                                               (Prims.of_int (340))
                                                               (Prims.of_int (23))
                                                               (Prims.of_int (340))
                                                               (Prims.of_int (115)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Typeclasses.fst"
                                                               (Prims.of_int (340))
                                                               (Prims.of_int (118))
                                                               (Prims.of_int (426))
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
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (30)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (426))
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
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (426))
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
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (426))
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
                                                                    debug
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
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
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
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (426))
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
                                                                    debug
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
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (426))
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
                                                                    debug
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
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
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
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (346))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (426))
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
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (347))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (426))
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
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (426))
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
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (426))
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
                                                                    debug
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
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
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
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
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
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
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
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (426))
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
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (426))
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
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (426))
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
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (426))
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
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (426))
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
                                                                    debug
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
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
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
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (426))
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
                                                                    debug
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
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (426))
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
                                                                    debug
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
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (426))
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
                                                                    debug
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
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
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
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (426))
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
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (364))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (426))
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
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___41)
                                                                    (fun
                                                                    uu___42
                                                                    ->
                                                                    (fun s ->
                                                                    let uu___42
                                                                    =
                                                                    debug
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
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (425))
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
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (425))
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
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (425))
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
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (425))
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
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (425))
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
                                                                    (Prims.of_int (378))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (378))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (380))
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
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (425))
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
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (382))
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
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (425))
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
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (425))
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
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (386))
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
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (50)))))
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
                                                                    (let uu___54
                                                                    =
                                                                    FStar_Tactics_NamedView.inspect_sigelt
                                                                    se1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (50)))))
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
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_SyntaxHelpers.lookup_lb
                                                                    lbs
                                                                    proj_name))
                                                                    | 
                                                                    uu___56
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "mk_class: proj not Sg_Let?")))
                                                                    uu___55))))
                                                                    uu___53) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___51)
                                                                    (fun
                                                                    uu___52
                                                                    ->
                                                                    (fun
                                                                    proj_lb
                                                                    ->
                                                                    let uu___52
                                                                    =
                                                                    debug
                                                                    (fun
                                                                    uu___53
                                                                    ->
                                                                    let uu___54
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.term_to_string
                                                                    proj_lb.FStar_Tactics_NamedView.lb_typ in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___54)
                                                                    (fun
                                                                    uu___55
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___56
                                                                    ->
                                                                    Prims.strcat
                                                                    "proj_ty = "
                                                                    uu___55))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___52)
                                                                    (fun
                                                                    uu___53
                                                                    ->
                                                                    (fun
                                                                    uu___53
                                                                    ->
                                                                    let uu___54
                                                                    =
                                                                    let uu___55
                                                                    =
                                                                    FStar_Tactics_V2_SyntaxHelpers.collect_arr_bs
                                                                    proj_lb.FStar_Tactics_NamedView.lb_typ in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (395))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    uu___55)
                                                                    (fun
                                                                    uu___56
                                                                    ->
                                                                    (fun
                                                                    uu___56
                                                                    ->
                                                                    match uu___56
                                                                    with
                                                                    | 
                                                                    (bs1,
                                                                    cod2) ->
                                                                    let uu___57
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___58
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
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (402))
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
                                                                    (let uu___59
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___60
                                                                    ->
                                                                    binder_set_meta
                                                                    b1 tcr)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    uu___59)
                                                                    (fun
                                                                    uu___60
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
                                                                    uu___60)))))
                                                                    uu___58)))
                                                                    uu___56) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (395))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (403))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___54)
                                                                    (fun
                                                                    uu___55
                                                                    ->
                                                                    (fun ty1
                                                                    ->
                                                                    let uu___55
                                                                    =
                                                                    let uu___56
                                                                    =
                                                                    FStar_Tactics_V2_SyntaxHelpers.collect_abs
                                                                    proj_lb.FStar_Tactics_NamedView.lb_def in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___56)
                                                                    (fun
                                                                    uu___57
                                                                    ->
                                                                    (fun
                                                                    uu___57
                                                                    ->
                                                                    match uu___57
                                                                    with
                                                                    | 
                                                                    (bs1,
                                                                    body) ->
                                                                    let uu___58
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___59
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
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (411))
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
                                                                    (let uu___60
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___61
                                                                    ->
                                                                    binder_set_meta
                                                                    b1 tcr)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___60)
                                                                    (fun
                                                                    uu___61
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
                                                                    uu___61)))))
                                                                    uu___59)))
                                                                    uu___57) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___55)
                                                                    (fun
                                                                    uu___56
                                                                    ->
                                                                    (fun def
                                                                    ->
                                                                    let uu___56
                                                                    =
                                                                    debug
                                                                    (fun
                                                                    uu___57
                                                                    ->
                                                                    let uu___58
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.term_to_string
                                                                    def in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___58)
                                                                    (fun
                                                                    uu___59
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___60
                                                                    ->
                                                                    Prims.strcat
                                                                    "def = "
                                                                    uu___59))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___56)
                                                                    (fun
                                                                    uu___57
                                                                    ->
                                                                    (fun
                                                                    uu___57
                                                                    ->
                                                                    let uu___58
                                                                    =
                                                                    debug
                                                                    (fun
                                                                    uu___59
                                                                    ->
                                                                    let uu___60
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.term_to_string
                                                                    ty1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
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
                                                                    "ty  = "
                                                                    uu___61))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (425))
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
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___61
                                                                    -> ty1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___60)
                                                                    (fun
                                                                    uu___61
                                                                    ->
                                                                    (fun ty2
                                                                    ->
                                                                    let uu___61
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___62
                                                                    -> def)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___61)
                                                                    (fun
                                                                    uu___62
                                                                    ->
                                                                    (fun def1
                                                                    ->
                                                                    let uu___62
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___63
                                                                    -> sfv)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (418))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (418))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (418))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___62)
                                                                    (fun
                                                                    uu___63
                                                                    ->
                                                                    (fun sfv1
                                                                    ->
                                                                    let uu___63
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___64
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
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___63)
                                                                    (fun
                                                                    uu___64
                                                                    ->
                                                                    (fun lb
                                                                    ->
                                                                    let uu___64
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
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___64)
                                                                    (fun se1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___65
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.set_sigelt_attrs
                                                                    b.FStar_Tactics_NamedView.attrs
                                                                    (FStarC_Reflection_V2_Builtins.set_sigelt_quals
                                                                    to_propagate
                                                                    se1)))))
                                                                    uu___64)))
                                                                    uu___63)))
                                                                    uu___62)))
                                                                    uu___61)))
                                                                    uu___59)))
                                                                    uu___57)))
                                                                    uu___56)))
                                                                    uu___55)))
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
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.Typeclasses.mk_class"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Typeclasses.mk_class (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 mk_class)
               FStarC_Syntax_Embeddings.e_string
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Reflection_V2_Embeddings.e_sigelt) psc ncb us args)
let solve : 'a . 'a -> 'a = fun ev -> ev