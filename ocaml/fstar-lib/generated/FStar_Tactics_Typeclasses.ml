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
               (Prims.of_int (30)) (Prims.of_int (5)) (Prims.of_int (30))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (30)) (Prims.of_int (2)) (Prims.of_int (31))
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
                               (Prims.of_int (31)) (Prims.of_int (10))
                               (Prims.of_int (31)) (Prims.of_int (16)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.Typeclasses.fst"
                               (Prims.of_int (31)) (Prims.of_int (4))
                               (Prims.of_int (31)) (Prims.of_int (16)))))
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
type st_t =
  {
  seen: FStar_Tactics_NamedView.term Prims.list ;
  glb: (FStar_Reflection_Types.sigelt * FStar_Reflection_Types.fv) Prims.list ;
  fuel: Prims.int }
let (__proj__Mkst_t__item__seen :
  st_t -> FStar_Tactics_NamedView.term Prims.list) =
  fun projectee -> match projectee with | { seen; glb; fuel;_} -> seen
let (__proj__Mkst_t__item__glb :
  st_t ->
    (FStar_Reflection_Types.sigelt * FStar_Reflection_Types.fv) Prims.list)
  = fun projectee -> match projectee with | { seen; glb; fuel;_} -> glb
let (__proj__Mkst_t__item__fuel : st_t -> Prims.int) =
  fun projectee -> match projectee with | { seen; glb; fuel;_} -> fuel
type tc_goal =
  {
  g: FStar_Tactics_NamedView.term ;
  head_fv: FStar_Reflection_Types.fv ;
  c_se: FStar_Reflection_Types.sigelt FStar_Pervasives_Native.option ;
  fundeps: Prims.int Prims.list FStar_Pervasives_Native.option ;
  args_and_uvars: (FStar_Reflection_V2_Data.argv * Prims.bool) Prims.list }
let (__proj__Mktc_goal__item__g : tc_goal -> FStar_Tactics_NamedView.term) =
  fun projectee ->
    match projectee with
    | { g; head_fv; c_se; fundeps; args_and_uvars;_} -> g
let (__proj__Mktc_goal__item__head_fv : tc_goal -> FStar_Reflection_Types.fv)
  =
  fun projectee ->
    match projectee with
    | { g; head_fv; c_se; fundeps; args_and_uvars;_} -> head_fv
let (__proj__Mktc_goal__item__c_se :
  tc_goal -> FStar_Reflection_Types.sigelt FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { g; head_fv; c_se; fundeps; args_and_uvars;_} -> c_se
let (__proj__Mktc_goal__item__fundeps :
  tc_goal -> Prims.int Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { g; head_fv; c_se; fundeps; args_and_uvars;_} -> fundeps
let (__proj__Mktc_goal__item__args_and_uvars :
  tc_goal -> (FStar_Reflection_V2_Data.argv * Prims.bool) Prims.list) =
  fun projectee ->
    match projectee with
    | { g; head_fv; c_se; fundeps; args_and_uvars;_} -> args_and_uvars
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
               (Prims.of_int (86)) (Prims.of_int (8)) (Prims.of_int (86))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (86)) (Prims.of_int (2)) (Prims.of_int (90))
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
               (Prims.of_int (93)) (Prims.of_int (8)) (Prims.of_int (93))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (93)) (Prims.of_int (2)) (Prims.of_int (99))
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
let rec (maybe_intros : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
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
               (Prims.of_int (11)))))
      (Obj.magic (FStar_Tactics_V2_Derived.cur_goal ()))
      (fun uu___1 ->
         (fun g ->
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
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
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
let (sigelt_name :
  FStar_Reflection_Types.sigelt -> FStar_Reflection_Types.fv Prims.list) =
  fun se ->
    match FStar_Reflection_V2_Builtins.inspect_sigelt se with
    | FStar_Reflection_V2_Data.Sg_Let (uu___, lbs) ->
        (match lbs with
         | lb::[] ->
             [(FStar_Reflection_V2_Builtins.inspect_lb lb).FStar_Reflection_V2_Data.lb_fv]
         | uu___1 -> [])
    | FStar_Reflection_V2_Data.Sg_Val (nm, uu___, uu___1) ->
        [FStar_Reflection_V2_Builtins.pack_fv nm]
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
               match FStar_Reflection_V2_Builtins.inspect_ln t with
               | FStar_Reflection_V2_Data.Tv_Const
                   (FStar_Reflection_V2_Data.C_Int i) ->
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
                 (Prims.of_int (8)))))
        (Obj.magic (FStar_Tactics_V2_SyntaxHelpers.hua t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Pervasives_Native.Some
                  (fv, uu___1,
                   (ty, FStar_Reflection_V2_Data.Q_Implicit)::(hd,
                                                               FStar_Reflection_V2_Data.Q_Explicit)::
                   (tl, FStar_Reflection_V2_Data.Q_Explicit)::[])
                  ->
                  Obj.magic
                    (Obj.repr
                       (if
                          (FStar_Reflection_V2_Builtins.implode_qn
                             (FStar_Reflection_V2_Builtins.inspect_fv fv))
                            = "Prims.Cons"
                        then
                          Obj.repr
                            (FStar_Tactics_Effect.tac_bind
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
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
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
                                     (Obj.magic (u hd))
                                     (fun uu___2 ->
                                        (fun uu___2 ->
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
                                                (Obj.magic
                                                   (unembed_list u tl))
                                                (fun uu___3 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___4 ->
                                                        (uu___2, uu___3)))))
                                          uu___2)))
                               (fun uu___2 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___3 ->
                                       match uu___2 with
                                       | (FStar_Pervasives_Native.Some hd1,
                                          FStar_Pervasives_Native.Some tl1)
                                           ->
                                           FStar_Pervasives_Native.Some (hd1
                                             :: tl1)
                                       | uu___4 ->
                                           FStar_Pervasives_Native.None)))
                        else
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 -> FStar_Pervasives_Native.None))))
              | FStar_Pervasives_Native.Some
                  (fv, uu___1, (ty, FStar_Reflection_V2_Data.Q_Implicit)::[])
                  ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             if
                               (FStar_Reflection_V2_Builtins.implode_qn
                                  (FStar_Reflection_V2_Builtins.inspect_fv fv))
                                 = "Prims.Nil"
                             then FStar_Pervasives_Native.Some []
                             else FStar_Pervasives_Native.None)))
              | uu___1 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> FStar_Pervasives_Native.None))))
             uu___)
let (extract_fundeps :
  FStar_Reflection_Types.sigelt ->
    (Prims.int Prims.list FStar_Pervasives_Native.option, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun se ->
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
               (Prims.of_int (13)))))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ -> FStar_Reflection_V2_Builtins.sigelt_attrs se))
      (fun uu___ ->
         (fun attrs ->
            let rec aux uu___ =
              (fun attrs1 ->
                 match attrs1 with
                 | [] ->
                     Obj.magic
                       (Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___ -> FStar_Pervasives_Native.None)))
                 | attr::attrs' ->
                     Obj.magic
                       (Obj.repr
                          (FStar_Tactics_Effect.tac_bind
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
                             (Obj.magic
                                (FStar_Tactics_V2_SyntaxHelpers.collect_app
                                   attr))
                             (fun uu___ ->
                                (fun uu___ ->
                                   match uu___ with
                                   | (hd,
                                      (a0,
                                       FStar_Reflection_V2_Data.Q_Explicit)::[])
                                       ->
                                       if
                                         FStar_Reflection_TermEq_Simple.term_eq
                                           hd
                                           (FStar_Reflection_V2_Builtins.pack_ln
                                              (FStar_Reflection_V2_Data.Tv_FVar
                                                 (FStar_Reflection_V2_Builtins.pack_fv
                                                    ["FStar";
                                                    "Tactics";
                                                    "Typeclasses";
                                                    "fundeps"])))
                                       then
                                         Obj.magic
                                           (unembed_list unembed_int a0)
                                       else Obj.magic (aux attrs')
                                   | uu___1 -> Obj.magic (aux attrs')) uu___))))
                uu___ in
            Obj.magic (aux attrs)) uu___)
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
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.Typeclasses.fst"
                             (Prims.of_int (174)) (Prims.of_int (26))
                             (Prims.of_int (174)) (Prims.of_int (102)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.Typeclasses.fst"
                             (Prims.of_int (174)) (Prims.of_int (26))
                             (Prims.of_int (174)) (Prims.of_int (122)))))
                    (Obj.magic
                       (FStar_Tactics_Util.mapi
                          (fun uu___1 ->
                             fun uu___ ->
                               (fun i ->
                                  fun uu___ ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            match uu___ with
                                            | (uu___2, b) ->
                                                if b then [i] else [])))
                                 uu___1 uu___) g.args_and_uvars))
                    (fun uu___ ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___1 -> FStar_List_Tot_Base.flatten uu___))))
              (fun uu___ ->
                 (fun unresolved_args ->
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
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.Typeclasses.fst"
                                        (Prims.of_int (177))
                                        (Prims.of_int (18))
                                        (Prims.of_int (177))
                                        (Prims.of_int (31)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.Typeclasses.fst"
                                        (Prims.of_int (177))
                                        (Prims.of_int (10))
                                        (Prims.of_int (177))
                                        (Prims.of_int (31)))))
                               (Obj.magic (res_typ typ))
                               (fun uu___ ->
                                  (fun uu___ -> Obj.magic (head_of uu___))
                                    uu___)))
                         (fun uu___ ->
                            (fun uu___ ->
                               match uu___ with
                               | FStar_Pervasives_Native.None ->
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
                                        (Obj.magic
                                           (debug
                                              (fun uu___1 ->
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
                                                         (Obj.magic
                                                            (FStar_Tactics_V2_Builtins.term_to_string
                                                               t))
                                                         (fun uu___2 ->
                                                            (fun uu___2 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (103)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
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
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_string
                                                                    typ))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "    typ="
                                                                    uu___3))))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    uu___2
                                                                    uu___3))))
                                                              uu___2)))
                                                   (fun uu___2 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___3 ->
                                                           Prims.strcat
                                                             "no head for typ of this? "
                                                             uu___2)))))
                                        (fun uu___1 ->
                                           FStar_Tactics_Effect.raise NoInst))
                               | FStar_Pervasives_Native.Some fv' ->
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
                                        (if
                                           Prims.op_Negation
                                             (fv_eq fv' g.head_fv)
                                         then
                                           FStar_Tactics_Effect.raise NoInst
                                         else
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 -> ()))
                                        (fun uu___1 ->
                                           (fun uu___1 ->
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
                                                   (Obj.magic
                                                      (debug
                                                         (fun uu___2 ->
                                                            FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (81)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))))
                                                              (Obj.magic
                                                                 (FStar_Tactics_V2_Builtins.term_to_string
                                                                    t))
                                                              (fun uu___3 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "Trying to apply hypothesis/instance: "
                                                                    uu___3)))))
                                                   (fun uu___2 ->
                                                      (fun uu___2 ->
                                                         Obj.magic
                                                           (FStar_Tactics_V2_Derived.seq
                                                              (fun uu___3 ->
                                                                 (fun uu___3
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
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    g.fundeps))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    fundeps
                                                                    ->
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
                                                                    (debug
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    "checking fundeps")))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
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
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_List_Tot_Base.for_all
                                                                    (fun i ->
                                                                    FStar_List_Tot_Base.mem
                                                                    i fundeps)
                                                                    unresolved_args))
                                                                    (fun
                                                                    uu___7 ->
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
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___5)
                                                                    else
                                                                    FStar_Tactics_V2_Derived.apply_noinst
                                                                    t)))
                                                                   uu___3)
                                                              (fun uu___3 ->
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
                                                                    (debug
                                                                    (fun
                                                                    uu___4 ->
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
                                                                    (FStar_Tactics_V2_Builtins.dump
                                                                    "next"))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    "apply seems to have worked")))))
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
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    {
                                                                    seen =
                                                                    (st.seen);
                                                                    glb =
                                                                    (st.glb);
                                                                    fuel =
                                                                    (st.fuel
                                                                    -
                                                                    Prims.int_one)
                                                                    }))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun st1
                                                                    ->
                                                                    Obj.magic
                                                                    (k st1))
                                                                    uu___5)))
                                                                    uu___4))))
                                                        uu___2))) uu___1)))
                              uu___))) uu___)
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
            (Obj.magic
               (debug
                  (fun uu___1 ->
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.Typeclasses.fst"
                                (Prims.of_int (202)) (Prims.of_int (40))
                                (Prims.of_int (202)) (Prims.of_int (58)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "prims.fst"
                                (Prims.of_int (590)) (Prims.of_int (19))
                                (Prims.of_int (590)) (Prims.of_int (31)))))
                       (Obj.magic
                          (FStar_Tactics_V2_Builtins.term_to_string g.g))
                       (fun uu___2 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 ->
                               Prims.strcat "local, goal = " uu___2)))))
            (fun uu___1 ->
               (fun uu___1 ->
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
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.Typeclasses.fst"
                                      (Prims.of_int (203))
                                      (Prims.of_int (25))
                                      (Prims.of_int (203))
                                      (Prims.of_int (37)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.Typeclasses.fst"
                                      (Prims.of_int (203))
                                      (Prims.of_int (13))
                                      (Prims.of_int (203))
                                      (Prims.of_int (37)))))
                             (Obj.magic (FStar_Tactics_V2_Derived.cur_env ()))
                             (fun uu___2 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 ->
                                     FStar_Reflection_V2_Builtins.vars_of_env
                                       uu___2))))
                       (fun uu___2 ->
                          (fun bs ->
                             Obj.magic
                               (first
                                  (fun b ->
                                     trywith st g
                                       (FStar_Tactics_NamedView.pack
                                          (FStar_Tactics_NamedView.Tv_Var
                                             (FStar_Tactics_V2_SyntaxCoercions.binding_to_namedv
                                                b)))
                                       b.FStar_Reflection_V2_Data.sort3 k) bs))
                            uu___2))) uu___1)
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
            (Obj.magic
               (debug
                  (fun uu___1 ->
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.Typeclasses.fst"
                                (Prims.of_int (209)) (Prims.of_int (41))
                                (Prims.of_int (209)) (Prims.of_int (59)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "prims.fst"
                                (Prims.of_int (590)) (Prims.of_int (19))
                                (Prims.of_int (590)) (Prims.of_int (31)))))
                       (Obj.magic
                          (FStar_Tactics_V2_Builtins.term_to_string g.g))
                       (fun uu___2 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 ->
                               Prims.strcat "global, goal = " uu___2)))))
            (fun uu___1 ->
               (fun uu___1 ->
                  Obj.magic
                    (first
                       (fun uu___2 ->
                          match uu___2 with
                          | (se, fv) ->
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
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
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
                                      (Obj.magic
                                         (FStar_Tactics_V2_Derived.cur_env ()))
                                      (fun uu___3 ->
                                         (fun uu___3 ->
                                            Obj.magic
                                              (FStar_Tactics_V2_Builtins.tc
                                                 uu___3
                                                 (FStar_Tactics_NamedView.pack
                                                    (FStar_Tactics_NamedView.Tv_FVar
                                                       fv)))) uu___3)))
                                (fun uu___3 ->
                                   (fun typ ->
                                      Obj.magic
                                        (trywith st g
                                           (FStar_Tactics_NamedView.pack
                                              (FStar_Tactics_NamedView.Tv_FVar
                                                 fv)) typ k)) uu___3)) 
                       st.glb)) uu___1)
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
            (Obj.magic (FStar_Tactics_NamedView.inspect g.g))
            (fun uu___1 ->
               (fun uu___1 ->
                  match uu___1 with
                  | FStar_Tactics_NamedView.Tv_FVar fv ->
                      Obj.magic
                        (Obj.repr
                           (if
                              (FStar_Reflection_V2_Builtins.implode_qn
                                 (FStar_Reflection_V2_Builtins.inspect_fv fv))
                                = "Prims.unit"
                            then
                              Obj.repr
                                (FStar_Tactics_V2_Derived.exact
                                   (FStar_Reflection_V2_Builtins.pack_ln
                                      (FStar_Reflection_V2_Data.Tv_Const
                                         FStar_Reflection_V2_Data.C_Unit)))
                            else Obj.repr (FStar_Tactics_Effect.raise Next)))
                  | uu___2 ->
                      Obj.magic (Obj.repr (FStar_Tactics_Effect.raise Next)))
                 uu___1)
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
               (Prims.of_int (33)))))
      (if st.fuel <= Prims.int_zero
       then FStar_Tactics_Effect.raise NoInst
       else FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))
      (fun uu___ ->
         (fun uu___ ->
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
                 (Obj.magic
                    (debug
                       (fun uu___1 ->
                          (fun uu___1 ->
                             Obj.magic
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 ->
                                     Prims.strcat "fuel = "
                                       (Prims.string_of_int st.fuel))))
                            uu___1)))
                 (fun uu___1 ->
                    (fun uu___1 ->
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
                            (Obj.magic (maybe_intros ()))
                            (fun uu___2 ->
                               (fun uu___2 ->
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
                                       (Obj.magic
                                          (FStar_Tactics_V2_Derived.cur_goal
                                             ()))
                                       (fun uu___3 ->
                                          (fun g ->
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
                                                  (if
                                                     FStar_List_Tot_Base.existsb
                                                       (FStar_Reflection_TermEq_Simple.term_eq
                                                          g) st.seen
                                                   then
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_Effect.tac_bind
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
                                                             (Obj.magic
                                                                (debug
                                                                   (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    "loop")))
                                                                    uu___3)))
                                                             (fun uu___3 ->
                                                                FStar_Tactics_Effect.raise
                                                                  NoInst)))
                                                   else
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___4 ->
                                                                ()))))
                                                  (fun uu___3 ->
                                                     (fun uu___3 ->
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
                                                                (FStar_Tactics_V2_SyntaxHelpers.hua
                                                                   g))
                                                             (fun uu___4 ->
                                                                (fun uu___4
                                                                   ->
                                                                   match uu___4
                                                                   with
                                                                   | 
                                                                   FStar_Pervasives_Native.None
                                                                    ->
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
                                                                    (debug
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    "Goal does not look like a typeclass")))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.raise
                                                                    NoInst))
                                                                   | 
                                                                   FStar_Pervasives_Native.Some
                                                                    (head_fv,
                                                                    us, args)
                                                                    ->
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
                                                                    (FStar_Tactics_Effect.tac_bind
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
                                                                    (FStar_Tactics_V2_Derived.cur_env
                                                                    ()))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Reflection_V2_Builtins.lookup_typ
                                                                    uu___5
                                                                    (FStar_Reflection_V2_Builtins.inspect_fv
                                                                    head_fv)))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun c_se
                                                                    ->
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
                                                                    (match c_se
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives_Native.None)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    se ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (extract_fundeps
                                                                    se)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    fundeps
                                                                    ->
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
                                                                    (FStar_Tactics_Util.map
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (a, q) ->
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
                                                                    (FStar_Tactics_Effect.tac_bind
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
                                                                    (FStar_Tactics_V2_Builtins.free_uvars
                                                                    a))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.uu___is_Cons
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    ((a, q),
                                                                    uu___6))))
                                                                    args))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    args_and_uvars
                                                                    ->
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
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    {
                                                                    seen = (g
                                                                    ::
                                                                    (st.seen));
                                                                    glb =
                                                                    (st.glb);
                                                                    fuel =
                                                                    (st.fuel)
                                                                    }))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun st1
                                                                    ->
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
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    {
                                                                    g;
                                                                    head_fv;
                                                                    c_se;
                                                                    fundeps;
                                                                    args_and_uvars
                                                                    }))
                                                                    (fun
                                                                    uu___5 ->
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
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                  uu___4)))
                                                       uu___3))) uu___3)))
                                 uu___2))) uu___1))) uu___)
let rec concatMap :
  'a 'b .
    ('a -> ('b Prims.list, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> ('b Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun l ->
           match l with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> [])))
           | x::xs ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.Typeclasses.fst"
                                (Prims.of_int (270)) (Prims.of_int (13))
                                (Prims.of_int (270)) (Prims.of_int (16)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.Typeclasses.fst"
                                (Prims.of_int (270)) (Prims.of_int (13))
                                (Prims.of_int (270)) (Prims.of_int (33)))))
                       (Obj.magic (f x))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Typeclasses.fst"
                                           (Prims.of_int (270))
                                           (Prims.of_int (19))
                                           (Prims.of_int (270))
                                           (Prims.of_int (33)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Typeclasses.fst"
                                           (Prims.of_int (270))
                                           (Prims.of_int (13))
                                           (Prims.of_int (270))
                                           (Prims.of_int (33)))))
                                  (Obj.magic (concatMap f xs))
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 -> (op_At ()) uu___ uu___1))))
                            uu___)))) uu___1 uu___
let (tcresolve : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (275)) (Prims.of_int (4)) (Prims.of_int (275))
               (Prims.of_int (54)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
               (Prims.of_int (276)) (Prims.of_int (4)) (Prims.of_int (309))
               (Prims.of_int (18)))))
      (Obj.magic
         (debug
            (fun uu___1 ->
               FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (275)) (Prims.of_int (21))
                          (Prims.of_int (275)) (Prims.of_int (28)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (275)) (Prims.of_int (30))
                          (Prims.of_int (275)) (Prims.of_int (53)))))
                 (Obj.magic (FStar_Tactics_V2_Builtins.dump ""))
                 (fun uu___2 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___3 -> "tcresolve entry point")))))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (276)) (Prims.of_int (4))
                          (Prims.of_int (276)) (Prims.of_int (11)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Typeclasses.fst"
                          (Prims.of_int (276)) (Prims.of_int (12))
                          (Prims.of_int (309)) (Prims.of_int (18)))))
                 (Obj.magic (FStar_Tactics_V2_Builtins.norm []))
                 (fun uu___2 ->
                    (fun uu___2 ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Typeclasses.fst"
                                     (Prims.of_int (277)) (Prims.of_int (12))
                                     (Prims.of_int (277)) (Prims.of_int (26)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Typeclasses.fst"
                                     (Prims.of_int (278)) (Prims.of_int (4))
                                     (Prims.of_int (309)) (Prims.of_int (18)))))
                            (Obj.magic
                               (FStar_Tactics_V2_Derived.cur_witness ()))
                            (fun uu___3 ->
                               (fun w ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (278))
                                                (Prims.of_int (4))
                                                (Prims.of_int (278))
                                                (Prims.of_int (29)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Typeclasses.fst"
                                                (Prims.of_int (281))
                                                (Prims.of_int (4))
                                                (Prims.of_int (309))
                                                (Prims.of_int (18)))))
                                       (Obj.magic
                                          (FStar_Tactics_V2_Builtins.set_dump_on_failure
                                             false))
                                       (fun uu___3 ->
                                          (fun uu___3 ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Typeclasses.fst"
                                                           (Prims.of_int (281))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (281))
                                                           (Prims.of_int (19)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Typeclasses.fst"
                                                           (Prims.of_int (281))
                                                           (Prims.of_int (20))
                                                           (Prims.of_int (309))
                                                           (Prims.of_int (18)))))
                                                  (Obj.magic
                                                     (maybe_intros ()))
                                                  (fun uu___4 ->
                                                     (fun uu___4 ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (56)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (18)))))
                                                             (Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (56)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (286))
                                                                    (Prims.of_int (56)))))
                                                                   (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.cur_env
                                                                    ()))
                                                                   (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Reflection_V2_Builtins.lookup_attr_ses
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Typeclasses";
                                                                    "tcinstance"])))
                                                                    uu___5))))
                                                             (fun uu___5 ->
                                                                (fun glb ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (287))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (5)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    (concatMap
                                                                    (fun se
                                                                    ->
                                                                    concatMap
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun fv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    [
                                                                    (se, fv)])))
                                                                    uu___5)
                                                                    (sigelt_name
                                                                    se)) glb))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun glb1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (309))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    {
                                                                    seen = [];
                                                                    glb =
                                                                    glb1;
                                                                    fuel =
                                                                    (Prims.of_int (16))
                                                                    }))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun st0
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.try_with
                                                                    (fun
                                                                    uu___5 ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (20)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    (tcresolve'
                                                                    st0))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (debug
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (58)))))
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
                                                                    w))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    "Solved to:\n\t"
                                                                    uu___8)))))
                                                                    uu___6))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    NoInst ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (304))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Typeclasses.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.cur_goal
                                                                    ()))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.term_to_doc
                                                                    uu___6))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pprint.prefix
                                                                    (Prims.of_int (2))
                                                                    Prims.int_one
                                                                    (FStar_Pprint.arbitrary_string
                                                                    "Could not solve constraint")
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    [uu___6]))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (FStar_Pprint.arbitrary_string
                                                                    "Typeclass resolution failed.")
                                                                    :: uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_V2_Derived.fail_doc
                                                                    uu___6)))
                                                                    | 
                                                                    FStar_Tactics_Common.TacticFailure
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
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                  uu___5)))
                                                       uu___4))) uu___3)))
                                 uu___3))) uu___2))) uu___1)
let _ =
  FStar_Tactics_Native.register_tactic "FStar.Tactics.Typeclasses.tcresolve"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Typeclasses.tcresolve (plugin)"
               (FStar_Tactics_Native.from_tactic_1 tcresolve)
               FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit
               psc ncb us args)
let solve : 'a . 'a -> 'a = fun ev -> ev