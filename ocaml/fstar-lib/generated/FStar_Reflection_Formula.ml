open Prims
let (fresh_bv :
  FStar_Reflection_Types.typ ->
    (FStar_Reflection_Types.bv, unit) FStar_Tactics_Effect.tac_repr)
  = FStar_Tactics_Builtins.fresh_bv_named "x"
let (bv_to_string :
  FStar_Reflection_Types.bv ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bv ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Reflection.Formula.fst" (Prims.of_int (29))
         (Prims.of_int (14)) (Prims.of_int (29)) (Prims.of_int (27)))
      (Prims.mk_range "FStar.Reflection.Formula.fst" (Prims.of_int (30))
         (Prims.of_int (4)) (Prims.of_int (30)) (Prims.of_int (26)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ -> FStar_Reflection_Builtins.inspect_bv bv))
      (fun uu___ ->
         (fun bvv ->
            Obj.magic
              (FStar_Tactics_Builtins.unseal
                 bvv.FStar_Reflection_Data.bv_ppname)) uu___)
type comparison =
  | Eq of FStar_Reflection_Types.typ FStar_Pervasives_Native.option 
  | BoolEq of FStar_Reflection_Types.typ FStar_Pervasives_Native.option 
  | Lt 
  | Le 
  | Gt 
  | Ge 
let (uu___is_Eq : comparison -> Prims.bool) =
  fun projectee -> match projectee with | Eq _0 -> true | uu___ -> false
let (__proj__Eq__item___0 :
  comparison -> FStar_Reflection_Types.typ FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | Eq _0 -> _0
let (uu___is_BoolEq : comparison -> Prims.bool) =
  fun projectee -> match projectee with | BoolEq _0 -> true | uu___ -> false
let (__proj__BoolEq__item___0 :
  comparison -> FStar_Reflection_Types.typ FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | BoolEq _0 -> _0
let (uu___is_Lt : comparison -> Prims.bool) =
  fun projectee -> match projectee with | Lt -> true | uu___ -> false
let (uu___is_Le : comparison -> Prims.bool) =
  fun projectee -> match projectee with | Le -> true | uu___ -> false
let (uu___is_Gt : comparison -> Prims.bool) =
  fun projectee -> match projectee with | Gt -> true | uu___ -> false
let (uu___is_Ge : comparison -> Prims.bool) =
  fun projectee -> match projectee with | Ge -> true | uu___ -> false
type formula =
  | True_ 
  | False_ 
  | Comp of comparison * FStar_Reflection_Types.term *
  FStar_Reflection_Types.term 
  | And of FStar_Reflection_Types.term * FStar_Reflection_Types.term 
  | Or of FStar_Reflection_Types.term * FStar_Reflection_Types.term 
  | Not of FStar_Reflection_Types.term 
  | Implies of FStar_Reflection_Types.term * FStar_Reflection_Types.term 
  | Iff of FStar_Reflection_Types.term * FStar_Reflection_Types.term 
  | Forall of FStar_Reflection_Types.bv * FStar_Reflection_Types.term 
  | Exists of FStar_Reflection_Types.bv * FStar_Reflection_Types.term 
  | App of FStar_Reflection_Types.term * FStar_Reflection_Types.term 
  | Name of FStar_Reflection_Types.bv 
  | FV of FStar_Reflection_Types.fv 
  | IntLit of Prims.int 
  | F_Unknown 
let (uu___is_True_ : formula -> Prims.bool) =
  fun projectee -> match projectee with | True_ -> true | uu___ -> false
let (uu___is_False_ : formula -> Prims.bool) =
  fun projectee -> match projectee with | False_ -> true | uu___ -> false
let (uu___is_Comp : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Comp (_0, _1, _2) -> true | uu___ -> false
let (__proj__Comp__item___0 : formula -> comparison) =
  fun projectee -> match projectee with | Comp (_0, _1, _2) -> _0
let (__proj__Comp__item___1 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Comp (_0, _1, _2) -> _1
let (__proj__Comp__item___2 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Comp (_0, _1, _2) -> _2
let (uu___is_And : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | And (_0, _1) -> true | uu___ -> false
let (__proj__And__item___0 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | And (_0, _1) -> _0
let (__proj__And__item___1 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | And (_0, _1) -> _1
let (uu___is_Or : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Or (_0, _1) -> true | uu___ -> false
let (__proj__Or__item___0 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Or (_0, _1) -> _0
let (__proj__Or__item___1 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Or (_0, _1) -> _1
let (uu___is_Not : formula -> Prims.bool) =
  fun projectee -> match projectee with | Not _0 -> true | uu___ -> false
let (__proj__Not__item___0 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Not _0 -> _0
let (uu___is_Implies : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Implies (_0, _1) -> true | uu___ -> false
let (__proj__Implies__item___0 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Implies (_0, _1) -> _0
let (__proj__Implies__item___1 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Implies (_0, _1) -> _1
let (uu___is_Iff : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Iff (_0, _1) -> true | uu___ -> false
let (__proj__Iff__item___0 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Iff (_0, _1) -> _0
let (__proj__Iff__item___1 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Iff (_0, _1) -> _1
let (uu___is_Forall : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Forall (_0, _1) -> true | uu___ -> false
let (__proj__Forall__item___0 : formula -> FStar_Reflection_Types.bv) =
  fun projectee -> match projectee with | Forall (_0, _1) -> _0
let (__proj__Forall__item___1 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Forall (_0, _1) -> _1
let (uu___is_Exists : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | Exists (_0, _1) -> true | uu___ -> false
let (__proj__Exists__item___0 : formula -> FStar_Reflection_Types.bv) =
  fun projectee -> match projectee with | Exists (_0, _1) -> _0
let (__proj__Exists__item___1 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | Exists (_0, _1) -> _1
let (uu___is_App : formula -> Prims.bool) =
  fun projectee ->
    match projectee with | App (_0, _1) -> true | uu___ -> false
let (__proj__App__item___0 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | App (_0, _1) -> _0
let (__proj__App__item___1 : formula -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | App (_0, _1) -> _1
let (uu___is_Name : formula -> Prims.bool) =
  fun projectee -> match projectee with | Name _0 -> true | uu___ -> false
let (__proj__Name__item___0 : formula -> FStar_Reflection_Types.bv) =
  fun projectee -> match projectee with | Name _0 -> _0
let (uu___is_FV : formula -> Prims.bool) =
  fun projectee -> match projectee with | FV _0 -> true | uu___ -> false
let (__proj__FV__item___0 : formula -> FStar_Reflection_Types.fv) =
  fun projectee -> match projectee with | FV _0 -> _0
let (uu___is_IntLit : formula -> Prims.bool) =
  fun projectee -> match projectee with | IntLit _0 -> true | uu___ -> false
let (__proj__IntLit__item___0 : formula -> Prims.int) =
  fun projectee -> match projectee with | IntLit _0 -> _0
let (uu___is_F_Unknown : formula -> Prims.bool) =
  fun projectee -> match projectee with | F_Unknown -> true | uu___ -> false
let (mk_Forall :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      (formula, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun typ ->
         fun pred ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   Forall
                     ((FStar_Reflection_Builtins.pack_bv
                         {
                           FStar_Reflection_Data.bv_ppname =
                             (FStar_Reflection_Data.as_ppname "x");
                           FStar_Reflection_Data.bv_index = Prims.int_zero;
                           FStar_Reflection_Data.bv_sort = typ
                         }),
                       (FStar_Reflection_Builtins.pack_ln
                          (FStar_Reflection_Data.Tv_App
                             (pred,
                               ((FStar_Reflection_Builtins.pack_ln
                                   (FStar_Reflection_Data.Tv_BVar
                                      (FStar_Reflection_Builtins.pack_bv
                                         {
                                           FStar_Reflection_Data.bv_ppname =
                                             (FStar_Reflection_Data.as_ppname
                                                "x");
                                           FStar_Reflection_Data.bv_index =
                                             Prims.int_zero;
                                           FStar_Reflection_Data.bv_sort =
                                             typ
                                         }))),
                                 FStar_Reflection_Data.Q_Explicit))))))))
        uu___1 uu___
let (mk_Exists :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      (formula, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun typ ->
         fun pred ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   Exists
                     ((FStar_Reflection_Builtins.pack_bv
                         {
                           FStar_Reflection_Data.bv_ppname =
                             (FStar_Reflection_Data.as_ppname "x");
                           FStar_Reflection_Data.bv_index = Prims.int_zero;
                           FStar_Reflection_Data.bv_sort = typ
                         }),
                       (FStar_Reflection_Builtins.pack_ln
                          (FStar_Reflection_Data.Tv_App
                             (pred,
                               ((FStar_Reflection_Builtins.pack_ln
                                   (FStar_Reflection_Data.Tv_BVar
                                      (FStar_Reflection_Builtins.pack_bv
                                         {
                                           FStar_Reflection_Data.bv_ppname =
                                             (FStar_Reflection_Data.as_ppname
                                                "x");
                                           FStar_Reflection_Data.bv_index =
                                             Prims.int_zero;
                                           FStar_Reflection_Data.bv_sort =
                                             typ
                                         }))),
                                 FStar_Reflection_Data.Q_Explicit))))))))
        uu___1 uu___
let (term_as_formula' :
  FStar_Reflection_Types.term ->
    (formula, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       match FStar_Reflection_Derived.inspect_ln_unascribe t with
       | FStar_Reflection_Data.Tv_Var n ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> Name n)))
       | FStar_Reflection_Data.Tv_FVar fv ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      if
                        (FStar_Reflection_Builtins.inspect_fv fv) =
                          FStar_Reflection_Const.true_qn
                      then True_
                      else
                        if
                          (FStar_Reflection_Builtins.inspect_fv fv) =
                            FStar_Reflection_Const.false_qn
                        then False_
                        else FV fv)))
       | FStar_Reflection_Data.Tv_UInst (fv, uu___) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      if
                        (FStar_Reflection_Builtins.inspect_fv fv) =
                          FStar_Reflection_Const.true_qn
                      then True_
                      else
                        if
                          (FStar_Reflection_Builtins.inspect_fv fv) =
                            FStar_Reflection_Const.false_qn
                        then False_
                        else FV fv)))
       | FStar_Reflection_Data.Tv_App (h0, t1) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Reflection.Formula.fst"
                      (Prims.of_int (83)) (Prims.of_int (22))
                      (Prims.of_int (83)) (Prims.of_int (36)))
                   (Prims.mk_range "FStar.Reflection.Formula.fst"
                      (Prims.of_int (83)) (Prims.of_int (8))
                      (Prims.of_int (116)) (Prims.of_int (26)))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> FStar_Reflection_Derived.collect_app h0))
                   (fun uu___ ->
                      (fun uu___ ->
                         match uu___ with
                         | (h, ts) ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (Prims.mk_range
                                     "FStar.Reflection.Formula.fst"
                                     (Prims.of_int (84)) (Prims.of_int (16))
                                     (Prims.of_int (84)) (Prims.of_int (26)))
                                  (Prims.mk_range
                                     "FStar.Reflection.Formula.fst"
                                     (Prims.of_int (85)) (Prims.of_int (8))
                                     (Prims.of_int (116)) (Prims.of_int (26)))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 ->
                                        FStar_Reflection_Derived.un_uinst h))
                                  (fun uu___1 ->
                                     (fun h1 ->
                                        match ((FStar_Reflection_Builtins.inspect_ln
                                                  h1),
                                                (FStar_List_Tot_Base.op_At ts
                                                   [t1]))
                                        with
                                        | (FStar_Reflection_Data.Tv_FVar fv,
                                           (a1,
                                            FStar_Reflection_Data.Q_Implicit)::
                                           (a2,
                                            FStar_Reflection_Data.Q_Explicit)::
                                           (a3,
                                            FStar_Reflection_Data.Q_Explicit)::[])
                                            ->
                                            Obj.magic
                                              (Obj.repr
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___1 ->
                                                       if
                                                         (FStar_Reflection_Builtins.inspect_fv
                                                            fv)
                                                           =
                                                           FStar_Reflection_Const.eq2_qn
                                                       then
                                                         Comp
                                                           ((Eq
                                                               (FStar_Pervasives_Native.Some
                                                                  a1)), a2,
                                                             a3)
                                                       else
                                                         if
                                                           (FStar_Reflection_Builtins.inspect_fv
                                                              fv)
                                                             =
                                                             FStar_Reflection_Const.eq1_qn
                                                         then
                                                           Comp
                                                             ((BoolEq
                                                                 (FStar_Pervasives_Native.Some
                                                                    a1)), a2,
                                                               a3)
                                                         else
                                                           if
                                                             (FStar_Reflection_Builtins.inspect_fv
                                                                fv)
                                                               =
                                                               FStar_Reflection_Const.lt_qn
                                                           then
                                                             Comp
                                                               (Lt, a2, a3)
                                                           else
                                                             if
                                                               (FStar_Reflection_Builtins.inspect_fv
                                                                  fv)
                                                                 =
                                                                 FStar_Reflection_Const.lte_qn
                                                             then
                                                               Comp
                                                                 (Le, a2, a3)
                                                             else
                                                               if
                                                                 (FStar_Reflection_Builtins.inspect_fv
                                                                    fv)
                                                                   =
                                                                   FStar_Reflection_Const.gt_qn
                                                               then
                                                                 Comp
                                                                   (Gt, a2,
                                                                    a3)
                                                               else
                                                                 if
                                                                   (FStar_Reflection_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.gte_qn
                                                                 then
                                                                   Comp
                                                                    (Ge, a2,
                                                                    a3)
                                                                 else
                                                                   App
                                                                    (h0,
                                                                    (FStar_Pervasives_Native.fst
                                                                    t1)))))
                                        | (FStar_Reflection_Data.Tv_FVar fv,
                                           (a1,
                                            FStar_Reflection_Data.Q_Explicit)::
                                           (a2,
                                            FStar_Reflection_Data.Q_Explicit)::[])
                                            ->
                                            Obj.magic
                                              (Obj.repr
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___1 ->
                                                       if
                                                         (FStar_Reflection_Builtins.inspect_fv
                                                            fv)
                                                           =
                                                           FStar_Reflection_Const.imp_qn
                                                       then Implies (a1, a2)
                                                       else
                                                         if
                                                           (FStar_Reflection_Builtins.inspect_fv
                                                              fv)
                                                             =
                                                             FStar_Reflection_Const.and_qn
                                                         then And (a1, a2)
                                                         else
                                                           if
                                                             (FStar_Reflection_Builtins.inspect_fv
                                                                fv)
                                                               =
                                                               FStar_Reflection_Const.iff_qn
                                                           then Iff (a1, a2)
                                                           else
                                                             if
                                                               (FStar_Reflection_Builtins.inspect_fv
                                                                  fv)
                                                                 =
                                                                 FStar_Reflection_Const.or_qn
                                                             then Or (a1, a2)
                                                             else
                                                               if
                                                                 (FStar_Reflection_Builtins.inspect_fv
                                                                    fv)
                                                                   =
                                                                   FStar_Reflection_Const.eq2_qn
                                                               then
                                                                 Comp
                                                                   ((Eq
                                                                    FStar_Pervasives_Native.None),
                                                                    a1, a2)
                                                               else
                                                                 if
                                                                   (FStar_Reflection_Builtins.inspect_fv
                                                                    fv) =
                                                                    FStar_Reflection_Const.eq1_qn
                                                                 then
                                                                   Comp
                                                                    ((BoolEq
                                                                    FStar_Pervasives_Native.None),
                                                                    a1, a2)
                                                                 else
                                                                   App
                                                                    (h0,
                                                                    (FStar_Pervasives_Native.fst
                                                                    t1)))))
                                        | (FStar_Reflection_Data.Tv_FVar fv,
                                           (a1,
                                            FStar_Reflection_Data.Q_Implicit)::
                                           (a2,
                                            FStar_Reflection_Data.Q_Explicit)::[])
                                            ->
                                            Obj.magic
                                              (Obj.repr
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (Prims.mk_range
                                                       "FStar.Reflection.Formula.fst"
                                                       (Prims.of_int (107))
                                                       (Prims.of_int (21))
                                                       (Prims.of_int (107))
                                                       (Prims.of_int (34)))
                                                    (Prims.mk_range
                                                       "FStar.Reflection.Formula.fst"
                                                       (Prims.of_int (108))
                                                       (Prims.of_int (17))
                                                       (Prims.of_int (110))
                                                       (Prims.of_int (31)))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___1 ->
                                                          FStar_Reflection_Builtins.inspect_fv
                                                            fv))
                                                    (fun uu___1 ->
                                                       (fun qn ->
                                                          if
                                                            qn =
                                                              FStar_Reflection_Const.forall_qn
                                                          then
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (mk_Forall
                                                                    a1 a2))
                                                          else
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (if
                                                                    qn =
                                                                    FStar_Reflection_Const.exists_qn
                                                                  then
                                                                    Obj.repr
                                                                    (mk_Exists
                                                                    a1 a2)
                                                                  else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    App
                                                                    (h0,
                                                                    (FStar_Pervasives_Native.fst
                                                                    t1)))))))
                                                         uu___1)))
                                        | (FStar_Reflection_Data.Tv_FVar fv,
                                           (a,
                                            FStar_Reflection_Data.Q_Explicit)::[])
                                            ->
                                            Obj.magic
                                              (Obj.repr
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___1 ->
                                                       if
                                                         (FStar_Reflection_Builtins.inspect_fv
                                                            fv)
                                                           =
                                                           FStar_Reflection_Const.not_qn
                                                       then Not a
                                                       else
                                                         App
                                                           (h0,
                                                             (FStar_Pervasives_Native.fst
                                                                t1)))))
                                        | uu___1 ->
                                            Obj.magic
                                              (Obj.repr
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___2 ->
                                                       App
                                                         (h0,
                                                           (FStar_Pervasives_Native.fst
                                                              t1)))))) uu___1)))
                        uu___)))
       | FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_Int i) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> IntLit i)))
       | FStar_Reflection_Data.Tv_Let (uu___, uu___1, uu___2, uu___3, uu___4)
           ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___5 -> F_Unknown)))
       | FStar_Reflection_Data.Tv_Match (uu___, uu___1, uu___2) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> F_Unknown)))
       | FStar_Reflection_Data.Tv_Type uu___ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> F_Unknown)))
       | FStar_Reflection_Data.Tv_Abs (uu___, uu___1) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> F_Unknown)))
       | FStar_Reflection_Data.Tv_Arrow (uu___, uu___1) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> F_Unknown)))
       | FStar_Reflection_Data.Tv_Uvar (uu___, uu___1) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> F_Unknown)))
       | FStar_Reflection_Data.Tv_Unknown ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> F_Unknown)))
       | FStar_Reflection_Data.Tv_Refine (uu___, uu___1) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> F_Unknown)))
       | FStar_Reflection_Data.Tv_Const uu___ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> F_Unknown)))
       | FStar_Reflection_Data.Tv_BVar uu___ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> F_Unknown))))
      uu___
let (term_as_formula :
  FStar_Reflection_Types.term ->
    (formula, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       match FStar_Reflection_Derived.unsquash_term t with
       | FStar_Pervasives_Native.None ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> F_Unknown)))
       | FStar_Pervasives_Native.Some t1 ->
           Obj.magic (Obj.repr (term_as_formula' t1))) uu___
let (term_as_formula_total :
  FStar_Reflection_Types.term ->
    (formula, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t -> term_as_formula' (FStar_Reflection_Derived.maybe_unsquash_term t)
let (formula_as_term_view : formula -> FStar_Reflection_Data.term_view) =
  fun f ->
    let mk_app' tv args =
      FStar_List_Tot_Base.fold_left
        (fun tv1 ->
           fun a ->
             FStar_Reflection_Data.Tv_App
               ((FStar_Reflection_Builtins.pack_ln tv1), a)) tv args in
    let e = FStar_Reflection_Data.Q_Explicit in
    let i = FStar_Reflection_Data.Q_Implicit in
    match f with
    | True_ ->
        FStar_Reflection_Data.Tv_FVar
          (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.true_qn)
    | False_ ->
        FStar_Reflection_Data.Tv_FVar
          (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.false_qn)
    | Comp (Eq (FStar_Pervasives_Native.None), l, r) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.eq2_qn))
          [(l, e); (r, e)]
    | Comp (Eq (FStar_Pervasives_Native.Some t), l, r) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.eq2_qn))
          [(t, i); (l, e); (r, e)]
    | Comp (BoolEq (FStar_Pervasives_Native.None), l, r) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.eq1_qn))
          [(l, e); (r, e)]
    | Comp (BoolEq (FStar_Pervasives_Native.Some t), l, r) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.eq1_qn))
          [(t, i); (l, e); (r, e)]
    | Comp (Lt, l, r) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.lt_qn))
          [(l, e); (r, e)]
    | Comp (Le, l, r) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.lte_qn))
          [(l, e); (r, e)]
    | Comp (Gt, l, r) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.gt_qn))
          [(l, e); (r, e)]
    | Comp (Ge, l, r) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.gte_qn))
          [(l, e); (r, e)]
    | And (p, q) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.and_qn))
          [(p, e); (q, e)]
    | Or (p, q) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.or_qn))
          [(p, e); (q, e)]
    | Implies (p, q) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.imp_qn))
          [(p, e); (q, e)]
    | Not p ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.not_qn))
          [(p, e)]
    | Iff (p, q) ->
        mk_app'
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv FStar_Reflection_Const.iff_qn))
          [(p, e); (q, e)]
    | Forall (b, t) -> FStar_Reflection_Data.Tv_Unknown
    | Exists (b, t) -> FStar_Reflection_Data.Tv_Unknown
    | App (p, q) ->
        FStar_Reflection_Data.Tv_App
          (p, (q, FStar_Reflection_Data.Q_Explicit))
    | Name b -> FStar_Reflection_Data.Tv_Var b
    | FV fv -> FStar_Reflection_Data.Tv_FVar fv
    | IntLit i1 ->
        FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_Int i1)
    | F_Unknown -> FStar_Reflection_Data.Tv_Unknown
let (formula_as_term : formula -> FStar_Reflection_Types.term) =
  fun f -> FStar_Reflection_Builtins.pack_ln (formula_as_term_view f)
let (formula_to_string :
  formula -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    (fun f ->
       match f with
       | True_ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "True_")))
       | False_ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "False_")))
       | Comp (Eq mt, l, r) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Reflection.Formula.fst"
                      (Prims.of_int (194)) (Prims.of_int (24))
                      (Prims.of_int (197)) (Prims.of_int (80)))
                   (Prims.mk_range "prims.fst" (Prims.of_int (606))
                      (Prims.of_int (19)) (Prims.of_int (606))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (194)) (Prims.of_int (24))
                            (Prims.of_int (196)) (Prims.of_int (67)))
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (194)) (Prims.of_int (24))
                            (Prims.of_int (197)) (Prims.of_int (80)))
                         (match mt with
                          | FStar_Pervasives_Native.None ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___ -> "")))
                          | FStar_Pervasives_Native.Some t ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.tac_bind
                                      (Prims.mk_range
                                         "FStar.Reflection.Formula.fst"
                                         (Prims.of_int (196))
                                         (Prims.of_int (44))
                                         (Prims.of_int (196))
                                         (Prims.of_int (66)))
                                      (Prims.mk_range "prims.fst"
                                         (Prims.of_int (606))
                                         (Prims.of_int (19))
                                         (Prims.of_int (606))
                                         (Prims.of_int (31)))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (Prims.mk_range
                                               "FStar.Reflection.Formula.fst"
                                               (Prims.of_int (196))
                                               (Prims.of_int (44))
                                               (Prims.of_int (196))
                                               (Prims.of_int (60)))
                                            (Prims.mk_range "prims.fst"
                                               (Prims.of_int (606))
                                               (Prims.of_int (19))
                                               (Prims.of_int (606))
                                               (Prims.of_int (31)))
                                            (Obj.magic
                                               (FStar_Tactics_Builtins.term_to_string
                                                  t))
                                            (fun uu___ ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___1 ->
                                                    Prims.strcat uu___ ")"))))
                                      (fun uu___ ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              Prims.strcat " (" uu___)))))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.Reflection.Formula.fst"
                                       (Prims.of_int (197))
                                       (Prims.of_int (24))
                                       (Prims.of_int (197))
                                       (Prims.of_int (80)))
                                    (Prims.mk_range "prims.fst"
                                       (Prims.of_int (606))
                                       (Prims.of_int (19))
                                       (Prims.of_int (606))
                                       (Prims.of_int (31)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (Prims.mk_range
                                             "FStar.Reflection.Formula.fst"
                                             (Prims.of_int (197))
                                             (Prims.of_int (31))
                                             (Prims.of_int (197))
                                             (Prims.of_int (80)))
                                          (Prims.mk_range "prims.fst"
                                             (Prims.of_int (606))
                                             (Prims.of_int (19))
                                             (Prims.of_int (606))
                                             (Prims.of_int (31)))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (Prims.mk_range
                                                   "FStar.Reflection.Formula.fst"
                                                   (Prims.of_int (197))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (197))
                                                   (Prims.of_int (47)))
                                                (Prims.mk_range
                                                   "FStar.Reflection.Formula.fst"
                                                   (Prims.of_int (197))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (197))
                                                   (Prims.of_int (80)))
                                                (Obj.magic
                                                   (FStar_Tactics_Builtins.term_to_string
                                                      l))
                                                (fun uu___1 ->
                                                   (fun uu___1 ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (Prims.mk_range
                                                              "FStar.Reflection.Formula.fst"
                                                              (Prims.of_int (197))
                                                              (Prims.of_int (50))
                                                              (Prims.of_int (197))
                                                              (Prims.of_int (80)))
                                                           (Prims.mk_range
                                                              "prims.fst"
                                                              (Prims.of_int (606))
                                                              (Prims.of_int (19))
                                                              (Prims.of_int (606))
                                                              (Prims.of_int (31)))
                                                           (Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (Prims.mk_range
                                                                    "FStar.Reflection.Formula.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (80)))
                                                                 (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Reflection.Formula.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (74)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    r))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    uu___2
                                                                    ")"))))
                                                                 (fun uu___2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    ") ("
                                                                    uu___2))))
                                                           (fun uu___2 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___3
                                                                   ->
                                                                   Prims.strcat
                                                                    uu___1
                                                                    uu___2))))
                                                     uu___1)))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat " (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Eq" uu___))))
       | Comp (BoolEq mt, l, r) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Reflection.Formula.fst"
                      (Prims.of_int (199)) (Prims.of_int (24))
                      (Prims.of_int (202)) (Prims.of_int (80)))
                   (Prims.mk_range "prims.fst" (Prims.of_int (606))
                      (Prims.of_int (19)) (Prims.of_int (606))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (199)) (Prims.of_int (24))
                            (Prims.of_int (201)) (Prims.of_int (67)))
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (199)) (Prims.of_int (24))
                            (Prims.of_int (202)) (Prims.of_int (80)))
                         (match mt with
                          | FStar_Pervasives_Native.None ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___ -> "")))
                          | FStar_Pervasives_Native.Some t ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.tac_bind
                                      (Prims.mk_range
                                         "FStar.Reflection.Formula.fst"
                                         (Prims.of_int (201))
                                         (Prims.of_int (44))
                                         (Prims.of_int (201))
                                         (Prims.of_int (66)))
                                      (Prims.mk_range "prims.fst"
                                         (Prims.of_int (606))
                                         (Prims.of_int (19))
                                         (Prims.of_int (606))
                                         (Prims.of_int (31)))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (Prims.mk_range
                                               "FStar.Reflection.Formula.fst"
                                               (Prims.of_int (201))
                                               (Prims.of_int (44))
                                               (Prims.of_int (201))
                                               (Prims.of_int (60)))
                                            (Prims.mk_range "prims.fst"
                                               (Prims.of_int (606))
                                               (Prims.of_int (19))
                                               (Prims.of_int (606))
                                               (Prims.of_int (31)))
                                            (Obj.magic
                                               (FStar_Tactics_Builtins.term_to_string
                                                  t))
                                            (fun uu___ ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___1 ->
                                                    Prims.strcat uu___ ")"))))
                                      (fun uu___ ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              Prims.strcat " (" uu___)))))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.Reflection.Formula.fst"
                                       (Prims.of_int (202))
                                       (Prims.of_int (24))
                                       (Prims.of_int (202))
                                       (Prims.of_int (80)))
                                    (Prims.mk_range "prims.fst"
                                       (Prims.of_int (606))
                                       (Prims.of_int (19))
                                       (Prims.of_int (606))
                                       (Prims.of_int (31)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (Prims.mk_range
                                             "FStar.Reflection.Formula.fst"
                                             (Prims.of_int (202))
                                             (Prims.of_int (31))
                                             (Prims.of_int (202))
                                             (Prims.of_int (80)))
                                          (Prims.mk_range "prims.fst"
                                             (Prims.of_int (606))
                                             (Prims.of_int (19))
                                             (Prims.of_int (606))
                                             (Prims.of_int (31)))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (Prims.mk_range
                                                   "FStar.Reflection.Formula.fst"
                                                   (Prims.of_int (202))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (202))
                                                   (Prims.of_int (47)))
                                                (Prims.mk_range
                                                   "FStar.Reflection.Formula.fst"
                                                   (Prims.of_int (202))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (202))
                                                   (Prims.of_int (80)))
                                                (Obj.magic
                                                   (FStar_Tactics_Builtins.term_to_string
                                                      l))
                                                (fun uu___1 ->
                                                   (fun uu___1 ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (Prims.mk_range
                                                              "FStar.Reflection.Formula.fst"
                                                              (Prims.of_int (202))
                                                              (Prims.of_int (50))
                                                              (Prims.of_int (202))
                                                              (Prims.of_int (80)))
                                                           (Prims.mk_range
                                                              "prims.fst"
                                                              (Prims.of_int (606))
                                                              (Prims.of_int (19))
                                                              (Prims.of_int (606))
                                                              (Prims.of_int (31)))
                                                           (Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (Prims.mk_range
                                                                    "FStar.Reflection.Formula.fst"
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (80)))
                                                                 (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.Reflection.Formula.fst"
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (74)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    r))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    uu___2
                                                                    ")"))))
                                                                 (fun uu___2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    ") ("
                                                                    uu___2))))
                                                           (fun uu___2 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___3
                                                                   ->
                                                                   Prims.strcat
                                                                    uu___1
                                                                    uu___2))))
                                                     uu___1)))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat " (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "BoolEq" uu___))))
       | Comp (Lt, l, r) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Reflection.Formula.fst"
                      (Prims.of_int (203)) (Prims.of_int (30))
                      (Prims.of_int (203)) (Prims.of_int (79)))
                   (Prims.mk_range "prims.fst" (Prims.of_int (606))
                      (Prims.of_int (19)) (Prims.of_int (606))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (203)) (Prims.of_int (30))
                            (Prims.of_int (203)) (Prims.of_int (46)))
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (203)) (Prims.of_int (30))
                            (Prims.of_int (203)) (Prims.of_int (79)))
                         (Obj.magic (FStar_Tactics_Builtins.term_to_string l))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.Reflection.Formula.fst"
                                       (Prims.of_int (203))
                                       (Prims.of_int (49))
                                       (Prims.of_int (203))
                                       (Prims.of_int (79)))
                                    (Prims.mk_range "prims.fst"
                                       (Prims.of_int (606))
                                       (Prims.of_int (19))
                                       (Prims.of_int (606))
                                       (Prims.of_int (31)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (Prims.mk_range
                                             "FStar.Reflection.Formula.fst"
                                             (Prims.of_int (203))
                                             (Prims.of_int (57))
                                             (Prims.of_int (203))
                                             (Prims.of_int (79)))
                                          (Prims.mk_range "prims.fst"
                                             (Prims.of_int (606))
                                             (Prims.of_int (19))
                                             (Prims.of_int (606))
                                             (Prims.of_int (31)))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (Prims.mk_range
                                                   "FStar.Reflection.Formula.fst"
                                                   (Prims.of_int (203))
                                                   (Prims.of_int (57))
                                                   (Prims.of_int (203))
                                                   (Prims.of_int (73)))
                                                (Prims.mk_range "prims.fst"
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (31)))
                                                (Obj.magic
                                                   (FStar_Tactics_Builtins.term_to_string
                                                      r))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat uu___1
                                                          ")"))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat ") (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Lt (" uu___))))
       | Comp (Le, l, r) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Reflection.Formula.fst"
                      (Prims.of_int (204)) (Prims.of_int (30))
                      (Prims.of_int (204)) (Prims.of_int (79)))
                   (Prims.mk_range "prims.fst" (Prims.of_int (606))
                      (Prims.of_int (19)) (Prims.of_int (606))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (204)) (Prims.of_int (30))
                            (Prims.of_int (204)) (Prims.of_int (46)))
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (204)) (Prims.of_int (30))
                            (Prims.of_int (204)) (Prims.of_int (79)))
                         (Obj.magic (FStar_Tactics_Builtins.term_to_string l))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.Reflection.Formula.fst"
                                       (Prims.of_int (204))
                                       (Prims.of_int (49))
                                       (Prims.of_int (204))
                                       (Prims.of_int (79)))
                                    (Prims.mk_range "prims.fst"
                                       (Prims.of_int (606))
                                       (Prims.of_int (19))
                                       (Prims.of_int (606))
                                       (Prims.of_int (31)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (Prims.mk_range
                                             "FStar.Reflection.Formula.fst"
                                             (Prims.of_int (204))
                                             (Prims.of_int (57))
                                             (Prims.of_int (204))
                                             (Prims.of_int (79)))
                                          (Prims.mk_range "prims.fst"
                                             (Prims.of_int (606))
                                             (Prims.of_int (19))
                                             (Prims.of_int (606))
                                             (Prims.of_int (31)))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (Prims.mk_range
                                                   "FStar.Reflection.Formula.fst"
                                                   (Prims.of_int (204))
                                                   (Prims.of_int (57))
                                                   (Prims.of_int (204))
                                                   (Prims.of_int (73)))
                                                (Prims.mk_range "prims.fst"
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (31)))
                                                (Obj.magic
                                                   (FStar_Tactics_Builtins.term_to_string
                                                      r))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat uu___1
                                                          ")"))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat ") (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Le (" uu___))))
       | Comp (Gt, l, r) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Reflection.Formula.fst"
                      (Prims.of_int (205)) (Prims.of_int (30))
                      (Prims.of_int (205)) (Prims.of_int (79)))
                   (Prims.mk_range "prims.fst" (Prims.of_int (606))
                      (Prims.of_int (19)) (Prims.of_int (606))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (205)) (Prims.of_int (30))
                            (Prims.of_int (205)) (Prims.of_int (46)))
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (205)) (Prims.of_int (30))
                            (Prims.of_int (205)) (Prims.of_int (79)))
                         (Obj.magic (FStar_Tactics_Builtins.term_to_string l))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.Reflection.Formula.fst"
                                       (Prims.of_int (205))
                                       (Prims.of_int (49))
                                       (Prims.of_int (205))
                                       (Prims.of_int (79)))
                                    (Prims.mk_range "prims.fst"
                                       (Prims.of_int (606))
                                       (Prims.of_int (19))
                                       (Prims.of_int (606))
                                       (Prims.of_int (31)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (Prims.mk_range
                                             "FStar.Reflection.Formula.fst"
                                             (Prims.of_int (205))
                                             (Prims.of_int (57))
                                             (Prims.of_int (205))
                                             (Prims.of_int (79)))
                                          (Prims.mk_range "prims.fst"
                                             (Prims.of_int (606))
                                             (Prims.of_int (19))
                                             (Prims.of_int (606))
                                             (Prims.of_int (31)))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (Prims.mk_range
                                                   "FStar.Reflection.Formula.fst"
                                                   (Prims.of_int (205))
                                                   (Prims.of_int (57))
                                                   (Prims.of_int (205))
                                                   (Prims.of_int (73)))
                                                (Prims.mk_range "prims.fst"
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (31)))
                                                (Obj.magic
                                                   (FStar_Tactics_Builtins.term_to_string
                                                      r))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat uu___1
                                                          ")"))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat ") (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Gt (" uu___))))
       | Comp (Ge, l, r) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Reflection.Formula.fst"
                      (Prims.of_int (206)) (Prims.of_int (30))
                      (Prims.of_int (206)) (Prims.of_int (79)))
                   (Prims.mk_range "prims.fst" (Prims.of_int (606))
                      (Prims.of_int (19)) (Prims.of_int (606))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (206)) (Prims.of_int (30))
                            (Prims.of_int (206)) (Prims.of_int (46)))
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (206)) (Prims.of_int (30))
                            (Prims.of_int (206)) (Prims.of_int (79)))
                         (Obj.magic (FStar_Tactics_Builtins.term_to_string l))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.Reflection.Formula.fst"
                                       (Prims.of_int (206))
                                       (Prims.of_int (49))
                                       (Prims.of_int (206))
                                       (Prims.of_int (79)))
                                    (Prims.mk_range "prims.fst"
                                       (Prims.of_int (606))
                                       (Prims.of_int (19))
                                       (Prims.of_int (606))
                                       (Prims.of_int (31)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (Prims.mk_range
                                             "FStar.Reflection.Formula.fst"
                                             (Prims.of_int (206))
                                             (Prims.of_int (57))
                                             (Prims.of_int (206))
                                             (Prims.of_int (79)))
                                          (Prims.mk_range "prims.fst"
                                             (Prims.of_int (606))
                                             (Prims.of_int (19))
                                             (Prims.of_int (606))
                                             (Prims.of_int (31)))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (Prims.mk_range
                                                   "FStar.Reflection.Formula.fst"
                                                   (Prims.of_int (206))
                                                   (Prims.of_int (57))
                                                   (Prims.of_int (206))
                                                   (Prims.of_int (73)))
                                                (Prims.mk_range "prims.fst"
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (31)))
                                                (Obj.magic
                                                   (FStar_Tactics_Builtins.term_to_string
                                                      r))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat uu___1
                                                          ")"))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat ") (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Ge (" uu___))))
       | And (p, q) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Reflection.Formula.fst"
                      (Prims.of_int (207)) (Prims.of_int (27))
                      (Prims.of_int (207)) (Prims.of_int (76)))
                   (Prims.mk_range "prims.fst" (Prims.of_int (606))
                      (Prims.of_int (19)) (Prims.of_int (606))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (207)) (Prims.of_int (27))
                            (Prims.of_int (207)) (Prims.of_int (43)))
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (207)) (Prims.of_int (27))
                            (Prims.of_int (207)) (Prims.of_int (76)))
                         (Obj.magic (FStar_Tactics_Builtins.term_to_string p))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.Reflection.Formula.fst"
                                       (Prims.of_int (207))
                                       (Prims.of_int (46))
                                       (Prims.of_int (207))
                                       (Prims.of_int (76)))
                                    (Prims.mk_range "prims.fst"
                                       (Prims.of_int (606))
                                       (Prims.of_int (19))
                                       (Prims.of_int (606))
                                       (Prims.of_int (31)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (Prims.mk_range
                                             "FStar.Reflection.Formula.fst"
                                             (Prims.of_int (207))
                                             (Prims.of_int (54))
                                             (Prims.of_int (207))
                                             (Prims.of_int (76)))
                                          (Prims.mk_range "prims.fst"
                                             (Prims.of_int (606))
                                             (Prims.of_int (19))
                                             (Prims.of_int (606))
                                             (Prims.of_int (31)))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (Prims.mk_range
                                                   "FStar.Reflection.Formula.fst"
                                                   (Prims.of_int (207))
                                                   (Prims.of_int (54))
                                                   (Prims.of_int (207))
                                                   (Prims.of_int (70)))
                                                (Prims.mk_range "prims.fst"
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (31)))
                                                (Obj.magic
                                                   (FStar_Tactics_Builtins.term_to_string
                                                      q))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat uu___1
                                                          ")"))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat ") (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "And (" uu___))))
       | Or (p, q) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Reflection.Formula.fst"
                      (Prims.of_int (208)) (Prims.of_int (27))
                      (Prims.of_int (208)) (Prims.of_int (76)))
                   (Prims.mk_range "prims.fst" (Prims.of_int (606))
                      (Prims.of_int (19)) (Prims.of_int (606))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (208)) (Prims.of_int (27))
                            (Prims.of_int (208)) (Prims.of_int (43)))
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (208)) (Prims.of_int (27))
                            (Prims.of_int (208)) (Prims.of_int (76)))
                         (Obj.magic (FStar_Tactics_Builtins.term_to_string p))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.Reflection.Formula.fst"
                                       (Prims.of_int (208))
                                       (Prims.of_int (46))
                                       (Prims.of_int (208))
                                       (Prims.of_int (76)))
                                    (Prims.mk_range "prims.fst"
                                       (Prims.of_int (606))
                                       (Prims.of_int (19))
                                       (Prims.of_int (606))
                                       (Prims.of_int (31)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (Prims.mk_range
                                             "FStar.Reflection.Formula.fst"
                                             (Prims.of_int (208))
                                             (Prims.of_int (54))
                                             (Prims.of_int (208))
                                             (Prims.of_int (76)))
                                          (Prims.mk_range "prims.fst"
                                             (Prims.of_int (606))
                                             (Prims.of_int (19))
                                             (Prims.of_int (606))
                                             (Prims.of_int (31)))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (Prims.mk_range
                                                   "FStar.Reflection.Formula.fst"
                                                   (Prims.of_int (208))
                                                   (Prims.of_int (54))
                                                   (Prims.of_int (208))
                                                   (Prims.of_int (70)))
                                                (Prims.mk_range "prims.fst"
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (31)))
                                                (Obj.magic
                                                   (FStar_Tactics_Builtins.term_to_string
                                                      q))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat uu___1
                                                          ")"))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat ") (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Or (" uu___))))
       | Implies (p, q) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Reflection.Formula.fst"
                      (Prims.of_int (209)) (Prims.of_int (36))
                      (Prims.of_int (209)) (Prims.of_int (85)))
                   (Prims.mk_range "prims.fst" (Prims.of_int (606))
                      (Prims.of_int (19)) (Prims.of_int (606))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (209)) (Prims.of_int (36))
                            (Prims.of_int (209)) (Prims.of_int (52)))
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (209)) (Prims.of_int (36))
                            (Prims.of_int (209)) (Prims.of_int (85)))
                         (Obj.magic (FStar_Tactics_Builtins.term_to_string p))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.Reflection.Formula.fst"
                                       (Prims.of_int (209))
                                       (Prims.of_int (55))
                                       (Prims.of_int (209))
                                       (Prims.of_int (85)))
                                    (Prims.mk_range "prims.fst"
                                       (Prims.of_int (606))
                                       (Prims.of_int (19))
                                       (Prims.of_int (606))
                                       (Prims.of_int (31)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (Prims.mk_range
                                             "FStar.Reflection.Formula.fst"
                                             (Prims.of_int (209))
                                             (Prims.of_int (63))
                                             (Prims.of_int (209))
                                             (Prims.of_int (85)))
                                          (Prims.mk_range "prims.fst"
                                             (Prims.of_int (606))
                                             (Prims.of_int (19))
                                             (Prims.of_int (606))
                                             (Prims.of_int (31)))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (Prims.mk_range
                                                   "FStar.Reflection.Formula.fst"
                                                   (Prims.of_int (209))
                                                   (Prims.of_int (63))
                                                   (Prims.of_int (209))
                                                   (Prims.of_int (79)))
                                                (Prims.mk_range "prims.fst"
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (31)))
                                                (Obj.magic
                                                   (FStar_Tactics_Builtins.term_to_string
                                                      q))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat uu___1
                                                          ")"))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat ") (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Implies (" uu___))))
       | Not p ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Reflection.Formula.fst"
                      (Prims.of_int (210)) (Prims.of_int (26))
                      (Prims.of_int (210)) (Prims.of_int (48)))
                   (Prims.mk_range "prims.fst" (Prims.of_int (606))
                      (Prims.of_int (19)) (Prims.of_int (606))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (210)) (Prims.of_int (26))
                            (Prims.of_int (210)) (Prims.of_int (42)))
                         (Prims.mk_range "prims.fst" (Prims.of_int (606))
                            (Prims.of_int (19)) (Prims.of_int (606))
                            (Prims.of_int (31)))
                         (Obj.magic (FStar_Tactics_Builtins.term_to_string p))
                         (fun uu___ ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> Prims.strcat uu___ ")"))))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Not (" uu___))))
       | Iff (p, q) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Reflection.Formula.fst"
                      (Prims.of_int (211)) (Prims.of_int (28))
                      (Prims.of_int (211)) (Prims.of_int (77)))
                   (Prims.mk_range "prims.fst" (Prims.of_int (606))
                      (Prims.of_int (19)) (Prims.of_int (606))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (211)) (Prims.of_int (28))
                            (Prims.of_int (211)) (Prims.of_int (44)))
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (211)) (Prims.of_int (28))
                            (Prims.of_int (211)) (Prims.of_int (77)))
                         (Obj.magic (FStar_Tactics_Builtins.term_to_string p))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.Reflection.Formula.fst"
                                       (Prims.of_int (211))
                                       (Prims.of_int (47))
                                       (Prims.of_int (211))
                                       (Prims.of_int (77)))
                                    (Prims.mk_range "prims.fst"
                                       (Prims.of_int (606))
                                       (Prims.of_int (19))
                                       (Prims.of_int (606))
                                       (Prims.of_int (31)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (Prims.mk_range
                                             "FStar.Reflection.Formula.fst"
                                             (Prims.of_int (211))
                                             (Prims.of_int (55))
                                             (Prims.of_int (211))
                                             (Prims.of_int (77)))
                                          (Prims.mk_range "prims.fst"
                                             (Prims.of_int (606))
                                             (Prims.of_int (19))
                                             (Prims.of_int (606))
                                             (Prims.of_int (31)))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (Prims.mk_range
                                                   "FStar.Reflection.Formula.fst"
                                                   (Prims.of_int (211))
                                                   (Prims.of_int (55))
                                                   (Prims.of_int (211))
                                                   (Prims.of_int (71)))
                                                (Prims.mk_range "prims.fst"
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (31)))
                                                (Obj.magic
                                                   (FStar_Tactics_Builtins.term_to_string
                                                      q))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat uu___1
                                                          ")"))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat ") (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Iff (" uu___))))
       | Forall (bs, t) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Reflection.Formula.fst"
                      (Prims.of_int (212)) (Prims.of_int (39))
                      (Prims.of_int (212)) (Prims.of_int (61)))
                   (Prims.mk_range "prims.fst" (Prims.of_int (606))
                      (Prims.of_int (19)) (Prims.of_int (606))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (212)) (Prims.of_int (39))
                            (Prims.of_int (212)) (Prims.of_int (55)))
                         (Prims.mk_range "prims.fst" (Prims.of_int (606))
                            (Prims.of_int (19)) (Prims.of_int (606))
                            (Prims.of_int (31)))
                         (Obj.magic (FStar_Tactics_Builtins.term_to_string t))
                         (fun uu___ ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> Prims.strcat uu___ ")"))))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Forall <bs> (" uu___))))
       | Exists (bs, t) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Reflection.Formula.fst"
                      (Prims.of_int (213)) (Prims.of_int (39))
                      (Prims.of_int (213)) (Prims.of_int (61)))
                   (Prims.mk_range "prims.fst" (Prims.of_int (606))
                      (Prims.of_int (19)) (Prims.of_int (606))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (213)) (Prims.of_int (39))
                            (Prims.of_int (213)) (Prims.of_int (55)))
                         (Prims.mk_range "prims.fst" (Prims.of_int (606))
                            (Prims.of_int (19)) (Prims.of_int (606))
                            (Prims.of_int (31)))
                         (Obj.magic (FStar_Tactics_Builtins.term_to_string t))
                         (fun uu___ ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> Prims.strcat uu___ ")"))))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Exists <bs> (" uu___))))
       | App (p, q) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Reflection.Formula.fst"
                      (Prims.of_int (214)) (Prims.of_int (28))
                      (Prims.of_int (214)) (Prims.of_int (77)))
                   (Prims.mk_range "prims.fst" (Prims.of_int (606))
                      (Prims.of_int (19)) (Prims.of_int (606))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (214)) (Prims.of_int (28))
                            (Prims.of_int (214)) (Prims.of_int (44)))
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (214)) (Prims.of_int (28))
                            (Prims.of_int (214)) (Prims.of_int (77)))
                         (Obj.magic (FStar_Tactics_Builtins.term_to_string p))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.Reflection.Formula.fst"
                                       (Prims.of_int (214))
                                       (Prims.of_int (47))
                                       (Prims.of_int (214))
                                       (Prims.of_int (77)))
                                    (Prims.mk_range "prims.fst"
                                       (Prims.of_int (606))
                                       (Prims.of_int (19))
                                       (Prims.of_int (606))
                                       (Prims.of_int (31)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (Prims.mk_range
                                             "FStar.Reflection.Formula.fst"
                                             (Prims.of_int (214))
                                             (Prims.of_int (55))
                                             (Prims.of_int (214))
                                             (Prims.of_int (77)))
                                          (Prims.mk_range "prims.fst"
                                             (Prims.of_int (606))
                                             (Prims.of_int (19))
                                             (Prims.of_int (606))
                                             (Prims.of_int (31)))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (Prims.mk_range
                                                   "FStar.Reflection.Formula.fst"
                                                   (Prims.of_int (214))
                                                   (Prims.of_int (55))
                                                   (Prims.of_int (214))
                                                   (Prims.of_int (71)))
                                                (Prims.mk_range "prims.fst"
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (31)))
                                                (Obj.magic
                                                   (FStar_Tactics_Builtins.term_to_string
                                                      q))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        Prims.strcat uu___1
                                                          ")"))))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat ") (" uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat uu___ uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "App (" uu___))))
       | Name bv ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.Reflection.Formula.fst"
                      (Prims.of_int (215)) (Prims.of_int (29))
                      (Prims.of_int (215)) (Prims.of_int (50)))
                   (Prims.mk_range "prims.fst" (Prims.of_int (606))
                      (Prims.of_int (19)) (Prims.of_int (606))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range "FStar.Reflection.Formula.fst"
                            (Prims.of_int (215)) (Prims.of_int (29))
                            (Prims.of_int (215)) (Prims.of_int (44)))
                         (Prims.mk_range "prims.fst" (Prims.of_int (606))
                            (Prims.of_int (19)) (Prims.of_int (606))
                            (Prims.of_int (31)))
                         (Obj.magic (bv_to_string bv))
                         (fun uu___ ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> Prims.strcat uu___ ")"))))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Name (" uu___))))
       | FV fv ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Prims.strcat "FV ("
                        (Prims.strcat
                           (FStar_Reflection_Derived.flatten_name
                              (FStar_Reflection_Builtins.inspect_fv fv)) ")"))))
       | IntLit i ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> Prims.strcat "Int " (Prims.string_of_int i))))
       | F_Unknown ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "?"))))
      uu___