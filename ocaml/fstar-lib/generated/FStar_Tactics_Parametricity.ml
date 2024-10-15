open Prims
exception Unsupported of Prims.string 
let (uu___is_Unsupported : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Unsupported uu___ -> true | uu___ -> false
let (__proj__Unsupported__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | Unsupported uu___ -> uu___
exception NotFoundFV of FStarC_Reflection_Types.fv 
let (uu___is_NotFoundFV : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | NotFoundFV uu___ -> true | uu___ -> false
let (__proj__NotFoundFV__item__uu___ :
  Prims.exn -> FStarC_Reflection_Types.fv) =
  fun projectee -> match projectee with | NotFoundFV uu___ -> uu___
type bvmap =
  (FStar_Tactics_NamedView.namedv * (FStar_Tactics_NamedView.binder *
    FStar_Tactics_NamedView.binder * FStar_Tactics_NamedView.binder))
    Prims.list
type fvmap =
  (FStarC_Reflection_Types.fv * FStarC_Reflection_Types.fv) Prims.list
type param_state = {
  bvmap: bvmap ;
  fresh: Prims.int ;
  recs: fvmap }
let (__proj__Mkparam_state__item__bvmap : param_state -> bvmap) =
  fun projectee ->
    match projectee with | { bvmap = bvmap1; fresh; recs;_} -> bvmap1
let (__proj__Mkparam_state__item__fresh : param_state -> Prims.int) =
  fun projectee ->
    match projectee with | { bvmap = bvmap1; fresh; recs;_} -> fresh
let (__proj__Mkparam_state__item__recs : param_state -> fvmap) =
  fun projectee ->
    match projectee with | { bvmap = bvmap1; fresh; recs;_} -> recs
let rec fold_right2 :
  'a 'b 'c .
    ('a -> 'b -> 'c -> ('c, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list ->
        'b Prims.list -> 'c -> ('c, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun f ->
             fun l1 ->
               fun l2 ->
                 fun c1 ->
                   match (l1, l2) with
                   | (h1::t1, h2::t2) ->
                       Obj.magic
                         (Obj.repr
                            (let uu___ = fold_right2 f t1 t2 c1 in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.Parametricity.fst"
                                        (Prims.of_int (18))
                                        (Prims.of_int (30))
                                        (Prims.of_int (18))
                                        (Prims.of_int (53)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.Parametricity.fst"
                                        (Prims.of_int (18))
                                        (Prims.of_int (22))
                                        (Prims.of_int (18))
                                        (Prims.of_int (53)))))
                               (Obj.magic uu___)
                               (fun uu___1 ->
                                  (fun uu___1 -> Obj.magic (f h1 h2 uu___1))
                                    uu___1)))
                   | ([], []) ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ -> c1)))
                   | uu___ ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_V2_Derived.fail "fold_right2")))
            uu___3 uu___2 uu___1 uu___
let rec zip3 :
  'a 'b 'c .
    'a Prims.list ->
      'b Prims.list -> 'c Prims.list -> ('a * 'b * 'c) Prims.list
  =
  fun l1 ->
    fun l2 ->
      fun l3 ->
        match (l1, l2, l3) with
        | (h1::t1, h2::t2, h3::t3) -> (h1, h2, h3) :: (zip3 t1 t2 t3)
        | uu___ -> []
let last : 'a . 'a Prims.list -> ('a, unit) FStar_Tactics_Effect.tac_repr =
  fun uu___ ->
    (fun xs ->
       match FStar_List_Tot_Base.rev xs with
       | h::uu___ ->
           Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> h))
       | [] -> Obj.magic (FStar_Tactics_V2_Derived.fail "last: empty list"))
      uu___
let (app_binders :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.binder Prims.list ->
      (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun t ->
         fun bs ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   FStar_Reflection_V2_Derived.mk_e_app t
                     (FStar_List_Tot_Base.map
                        FStar_Tactics_V2_SyntaxCoercions.binder_to_term bs))))
        uu___1 uu___
let (push_var_to_state :
  FStar_Tactics_NamedView.namedv ->
    FStar_Tactics_NamedView.binder ->
      FStar_Tactics_NamedView.binder ->
        FStar_Tactics_NamedView.binder -> param_state -> param_state)
  =
  fun v ->
    fun b0 ->
      fun b1 ->
        fun b2 ->
          fun s ->
            {
              bvmap = ((v, (b0, b1, b2)) :: (s.bvmap));
              fresh = (s.fresh);
              recs = (s.recs)
            }
exception NotARecFV 
let (uu___is_NotARecFV : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | NotARecFV -> true | uu___ -> false
exception NotFoundBV of FStar_Tactics_NamedView.namedv 
let (uu___is_NotFoundBV : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | NotFoundBV uu___ -> true | uu___ -> false
let (__proj__NotFoundBV__item__uu___ :
  Prims.exn -> FStar_Tactics_NamedView.namedv) =
  fun projectee -> match projectee with | NotFoundBV uu___ -> uu___
let (lookup_rec_fv :
  param_state ->
    FStarC_Reflection_Types.fv ->
      (FStarC_Reflection_Types.fv, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    fun f ->
      let rec aux uu___ =
        (fun m ->
           match m with
           | [] ->
               Obj.magic (Obj.repr (FStar_Tactics_Effect.raise NotARecFV))
           | (f1, k)::fs ->
               Obj.magic
                 (Obj.repr
                    (if
                       (FStar_Reflection_V2_Compare.compare_fv f f1) =
                         FStar_Order.Eq
                     then
                       Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> k))
                     else Obj.repr (aux fs)))) uu___ in
      aux s.recs
let (push_fv :
  FStarC_Reflection_Types.fv ->
    FStarC_Reflection_Types.fv -> param_state -> param_state)
  =
  fun f1 ->
    fun f2 ->
      fun s ->
        { bvmap = (s.bvmap); fresh = (s.fresh); recs = ((f1, f2) :: (s.recs))
        }
let (lookup :
  param_state ->
    FStar_Tactics_NamedView.namedv ->
      ((FStar_Tactics_NamedView.binder * FStar_Tactics_NamedView.binder *
         FStar_Tactics_NamedView.binder),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    fun v ->
      let rec aux uu___ =
        (fun bvm ->
           match bvm with
           | [] ->
               Obj.magic
                 (Obj.repr (FStar_Tactics_Effect.raise (NotFoundBV v)))
           | (v', r)::tl ->
               Obj.magic
                 (Obj.repr
                    (if
                       (FStar_Tactics_NamedView.inspect_namedv v).FStarC_Reflection_V2_Data.uniq
                         =
                         (FStar_Tactics_NamedView.inspect_namedv v').FStarC_Reflection_V2_Data.uniq
                     then
                       Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> r))
                     else Obj.repr (aux tl)))) uu___ in
      aux s.bvmap
let (replace_var :
  param_state ->
    Prims.bool ->
      FStar_Tactics_NamedView.term ->
        (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    fun b ->
      fun t ->
        let uu___ = FStar_Tactics_NamedView.inspect t in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                   (Prims.of_int (72)) (Prims.of_int (8)) (Prims.of_int (72))
                   (Prims.of_int (17)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                   (Prims.of_int (72)) (Prims.of_int (2)) (Prims.of_int (84))
                   (Prims.of_int (10))))) (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | FStar_Tactics_NamedView.Tv_Var v ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_V2_Derived.try_with
                            (fun uu___2 ->
                               match () with
                               | () ->
                                   let uu___3 = lookup s v in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Parametricity.fst"
                                              (Prims.of_int (75))
                                              (Prims.of_int (22))
                                              (Prims.of_int (75))
                                              (Prims.of_int (32)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Parametricity.fst"
                                              (Prims.of_int (74))
                                              (Prims.of_int (13))
                                              (Prims.of_int (77))
                                              (Prims.of_int (22)))))
                                     (Obj.magic uu___3)
                                     (fun uu___4 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___5 ->
                                             match uu___4 with
                                             | (x, y, uu___6) ->
                                                 FStar_Tactics_NamedView.pack
                                                   (FStar_Tactics_NamedView.Tv_Var
                                                      (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                                         (if b then y else x))))))
                            (fun uu___2 ->
                               (fun uu___2 ->
                                  match uu___2 with
                                  | NotFoundBV uu___3 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 -> t))
                                  | e ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.raise e))
                                 uu___2)))
                | uu___2 ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> t))))
               uu___1)
let (replace_by :
  param_state ->
    Prims.bool ->
      FStar_Tactics_NamedView.term ->
        (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    fun b ->
      fun t ->
        let uu___ = FStar_Tactics_Visit.visit_tm (replace_var s b) t in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                   (Prims.of_int (87)) (Prims.of_int (10))
                   (Prims.of_int (87)) (Prims.of_int (38)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                   (Prims.of_int (87)) (Prims.of_int (6)) (Prims.of_int (87))
                   (Prims.of_int (7))))) (Obj.magic uu___)
          (fun r -> FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> r))
let (tapp :
  FStarC_Reflection_V2_Data.aqualv ->
    FStar_Tactics_NamedView.term ->
      FStarC_Reflection_Types.term -> FStar_Tactics_NamedView.term)
  =
  fun q ->
    fun t1 ->
      fun t2 ->
        FStar_Tactics_NamedView.pack
          (FStar_Tactics_NamedView.Tv_App (t1, (t2, q)))
let (tabs :
  FStar_Tactics_NamedView.binder ->
    FStar_Tactics_NamedView.term ->
      (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun b ->
         fun t ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   FStar_Tactics_NamedView.pack
                     (FStar_Tactics_NamedView.Tv_Abs (b, t))))) uu___1 uu___
let rec (param' :
  param_state ->
    FStar_Tactics_NamedView.term ->
      (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    fun t ->
      let uu___ =
        let uu___1 = FStar_Tactics_NamedView.inspect t in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                   (Prims.of_int (96)) (Prims.of_int (8)) (Prims.of_int (96))
                   (Prims.of_int (17)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                   (Prims.of_int (96)) (Prims.of_int (2))
                   (Prims.of_int (153)) (Prims.of_int (60)))))
          (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 ->
                match uu___2 with
                | FStar_Tactics_NamedView.Tv_Type _u ->
                    Obj.magic
                      (Obj.repr
                         (let uu___3 =
                            FStar_Tactics_V2_Derived.fresh_binder_named "s" t in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (101)) (Prims.of_int (12))
                                     (Prims.of_int (101)) (Prims.of_int (36)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (101)) (Prims.of_int (39))
                                     (Prims.of_int (105))
                                     (Prims.of_int (100)))))
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               (fun s1 ->
                                  let uu___4 =
                                    FStar_Tactics_V2_Derived.fresh_binder_named
                                      "r" t in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Parametricity.fst"
                                                (Prims.of_int (102))
                                                (Prims.of_int (12))
                                                (Prims.of_int (102))
                                                (Prims.of_int (36)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Parametricity.fst"
                                                (Prims.of_int (102))
                                                (Prims.of_int (39))
                                                (Prims.of_int (105))
                                                (Prims.of_int (100)))))
                                       (Obj.magic uu___4)
                                       (fun uu___5 ->
                                          (fun r ->
                                             let uu___5 =
                                               FStar_Tactics_V2_Derived.fresh_binder_named
                                                 "xs"
                                                 (FStar_Tactics_NamedView.pack
                                                    (FStar_Tactics_NamedView.Tv_Var
                                                       (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                                          s1))) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Parametricity.fst"
                                                           (Prims.of_int (103))
                                                           (Prims.of_int (13))
                                                           (Prims.of_int (103))
                                                           (Prims.of_int (47)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Parametricity.fst"
                                                           (Prims.of_int (103))
                                                           (Prims.of_int (50))
                                                           (Prims.of_int (105))
                                                           (Prims.of_int (100)))))
                                                  (Obj.magic uu___5)
                                                  (fun uu___6 ->
                                                     (fun xs ->
                                                        let uu___6 =
                                                          FStar_Tactics_V2_Derived.fresh_binder_named
                                                            "xr"
                                                            (FStar_Tactics_NamedView.pack
                                                               (FStar_Tactics_NamedView.Tv_Var
                                                                  (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                                                    r))) in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (47)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "dummy"
                                                                    Prims.int_zero
                                                                    Prims.int_zero
                                                                    Prims.int_zero
                                                                    Prims.int_zero)))
                                                             (Obj.magic
                                                                uu___6)
                                                             (fun xr ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___7
                                                                    ->
                                                                    FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_Abs
                                                                    (s1,
                                                                    (FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_Abs
                                                                    (r,
                                                                    (FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_Arrow
                                                                    (xs,
                                                                    (FStarC_Reflection_V2_Data.C_Total
                                                                    (FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_Arrow
                                                                    (xr,
                                                                    (FStarC_Reflection_V2_Data.C_Total
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Type
                                                                    (FStarC_Reflection_V2_Builtins.pack_universe
                                                                    FStarC_Reflection_V2_Data.Uv_Unk))))))))))))))))))))
                                                       uu___6))) uu___5)))
                                 uu___4)))
                | FStar_Tactics_NamedView.Tv_Var bv ->
                    Obj.magic
                      (Obj.repr
                         (let uu___3 = lookup s bv in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (108)) (Prims.of_int (20))
                                     (Prims.of_int (108)) (Prims.of_int (31)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (107)) (Prims.of_int (16))
                                     (Prims.of_int (109)) (Prims.of_int (20)))))
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___5 ->
                                    match uu___4 with
                                    | (uu___6, uu___7, b) ->
                                        FStar_Tactics_V2_SyntaxCoercions.binder_to_term
                                          b))))
                | FStar_Tactics_NamedView.Tv_Arrow (b, c) ->
                    Obj.magic
                      (Obj.repr
                         (match FStar_Tactics_NamedView.inspect_comp c with
                          | FStarC_Reflection_V2_Data.C_Total t2 ->
                              Obj.repr
                                (let uu___3 = push_binder b s in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.Parametricity.fst"
                                            (Prims.of_int (114))
                                            (Prims.of_int (34))
                                            (Prims.of_int (114))
                                            (Prims.of_int (49)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.Parametricity.fst"
                                            (Prims.of_int (113))
                                            (Prims.of_int (19))
                                            (Prims.of_int (121))
                                            (Prims.of_int (58)))))
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      (fun uu___4 ->
                                         match uu___4 with
                                         | (s', (bx0, bx1, bxR)) ->
                                             let uu___5 =
                                               Obj.magic
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___6 ->
                                                       b.FStar_Tactics_NamedView.qual)) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Parametricity.fst"
                                                           (Prims.of_int (115))
                                                           (Prims.of_int (14))
                                                           (Prims.of_int (115))
                                                           (Prims.of_int (20)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Parametricity.fst"
                                                           (Prims.of_int (115))
                                                           (Prims.of_int (23))
                                                           (Prims.of_int (121))
                                                           (Prims.of_int (58)))))
                                                  (Obj.magic uu___5)
                                                  (fun uu___6 ->
                                                     (fun q ->
                                                        let uu___6 =
                                                          let uu___7 =
                                                            replace_by s
                                                              false t in
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (62)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (62)))))
                                                            (Obj.magic uu___7)
                                                            (fun uu___8 ->
                                                               (fun uu___8 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_V2_Derived.fresh_binder_named
                                                                    "f0"
                                                                    uu___8))
                                                                 uu___8) in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (62)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (58)))))
                                                             (Obj.magic
                                                                uu___6)
                                                             (fun uu___7 ->
                                                                (fun bf0 ->
                                                                   let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    replace_by
                                                                    s true t in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.fresh_binder_named
                                                                    "f1"
                                                                    uu___9))
                                                                    uu___9) in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun bf1
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_V2_SyntaxCoercions.binder_to_term)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun b2t
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    tapp q
                                                                    (b2t bf1)
                                                                    (b2t bx1))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (101)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (103)))))
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
                                                                    tapp q
                                                                    (b2t bf0)
                                                                    (b2t bx0))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (103)))))
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
                                                                    param' s'
                                                                    t2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (103)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    (uu___15,
                                                                    (uu___13,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (uu___11,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))))))
                                                                    uu___13)))
                                                                    uu___11) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (103)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun res
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr
                                                                    [bx0;
                                                                    bx1;
                                                                    bxR] res in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (tabs bf1
                                                                    uu___12))
                                                                    uu___12) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (tabs bf0
                                                                    uu___11))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                  uu___7)))
                                                       uu___6))) uu___4))
                          | uu___3 ->
                              Obj.repr
                                (FStar_Tactics_Effect.raise
                                   (Unsupported "effects"))))
                | FStar_Tactics_NamedView.Tv_App (l, (r, q)) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___3 = param' s l in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (126)) (Prims.of_int (13))
                                     (Prims.of_int (126)) (Prims.of_int (23)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (126)) (Prims.of_int (26))
                                     (Prims.of_int (130)) (Prims.of_int (41)))))
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               (fun lR ->
                                  let uu___4 = replace_by s false r in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Parametricity.fst"
                                                (Prims.of_int (127))
                                                (Prims.of_int (13))
                                                (Prims.of_int (127))
                                                (Prims.of_int (33)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Parametricity.fst"
                                                (Prims.of_int (127))
                                                (Prims.of_int (36))
                                                (Prims.of_int (130))
                                                (Prims.of_int (41)))))
                                       (Obj.magic uu___4)
                                       (fun uu___5 ->
                                          (fun l0 ->
                                             let uu___5 = replace_by s true r in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Parametricity.fst"
                                                           (Prims.of_int (128))
                                                           (Prims.of_int (13))
                                                           (Prims.of_int (128))
                                                           (Prims.of_int (32)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Parametricity.fst"
                                                           (Prims.of_int (128))
                                                           (Prims.of_int (35))
                                                           (Prims.of_int (130))
                                                           (Prims.of_int (41)))))
                                                  (Obj.magic uu___5)
                                                  (fun uu___6 ->
                                                     (fun l1 ->
                                                        let uu___6 =
                                                          param' s r in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (23)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (41)))))
                                                             (Obj.magic
                                                                uu___6)
                                                             (fun rR ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___7
                                                                    ->
                                                                    FStar_Reflection_V2_Derived.mk_app
                                                                    lR
                                                                    [
                                                                    (l0, q);
                                                                    (l1, q);
                                                                    (rR, q)]))))
                                                       uu___6))) uu___5)))
                                 uu___4)))
                | FStar_Tactics_NamedView.Tv_Abs (b, t1) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___3 =
                            Obj.magic
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___6 ->
                                    fun uu___5 ->
                                      fun uu___4 ->
                                        (fun uu___4 ->
                                           fun b1 ->
                                             fun t2 ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___5 ->
                                                       FStar_Tactics_NamedView.pack
                                                         (FStar_Tactics_NamedView.Tv_Abs
                                                            (b1, t2)))))
                                          uu___6 uu___5 uu___4)) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (133)) (Prims.of_int (29))
                                     (Prims.of_int (133)) (Prims.of_int (46)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (133)) (Prims.of_int (49))
                                     (Prims.of_int (137)) (Prims.of_int (33)))))
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               (fun abs ->
                                  let uu___4 = push_binder b s in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Parametricity.fst"
                                                (Prims.of_int (134))
                                                (Prims.of_int (32))
                                                (Prims.of_int (134))
                                                (Prims.of_int (47)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Parametricity.fst"
                                                (Prims.of_int (133))
                                                (Prims.of_int (49))
                                                (Prims.of_int (137))
                                                (Prims.of_int (33)))))
                                       (Obj.magic uu___4)
                                       (fun uu___5 ->
                                          (fun uu___5 ->
                                             match uu___5 with
                                             | (s', (bx0, bx1, bxR)) ->
                                                 let uu___6 = param' s' t1 in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Parametricity.fst"
                                                               (Prims.of_int (136))
                                                               (Prims.of_int (12))
                                                               (Prims.of_int (136))
                                                               (Prims.of_int (23)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Parametricity.fst"
                                                               (Prims.of_int (137))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (137))
                                                               (Prims.of_int (33)))))
                                                      (Obj.magic uu___6)
                                                      (fun uu___7 ->
                                                         (fun t2 ->
                                                            let uu___7 =
                                                              let uu___8 =
                                                                abs bxR t2 in
                                                              FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (32)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (33)))))
                                                                (Obj.magic
                                                                   uu___8)
                                                                (fun uu___9
                                                                   ->
                                                                   (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (abs bx1
                                                                    uu___9))
                                                                    uu___9) in
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (33)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (33)))))
                                                                 (Obj.magic
                                                                    uu___7)
                                                                 (fun uu___8
                                                                    ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (abs bx0
                                                                    uu___8))
                                                                    uu___8)))
                                                           uu___7))) uu___5)))
                                 uu___4)))
                | FStar_Tactics_NamedView.Tv_Match
                    (t1, FStar_Pervasives_Native.None, brs) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___3 =
                            let uu___4 = param' s t1 in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.Parametricity.fst"
                                       (Prims.of_int (140))
                                       (Prims.of_int (19))
                                       (Prims.of_int (140))
                                       (Prims.of_int (31)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.Parametricity.fst"
                                       (Prims.of_int (140))
                                       (Prims.of_int (9))
                                       (Prims.of_int (140))
                                       (Prims.of_int (60)))))
                              (Obj.magic uu___4)
                              (fun uu___5 ->
                                 (fun uu___5 ->
                                    let uu___6 =
                                      FStar_Tactics_Util.map (param_br s) brs in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.Parametricity.fst"
                                                  (Prims.of_int (140))
                                                  (Prims.of_int (37))
                                                  (Prims.of_int (140))
                                                  (Prims.of_int (59)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.Parametricity.fst"
                                                  (Prims.of_int (140))
                                                  (Prims.of_int (9))
                                                  (Prims.of_int (140))
                                                  (Prims.of_int (60)))))
                                         (Obj.magic uu___6)
                                         (fun uu___7 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___8 ->
                                                 FStar_Tactics_NamedView.Tv_Match
                                                   (uu___5,
                                                     FStar_Pervasives_Native.None,
                                                     uu___7))))) uu___5) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (140)) (Prims.of_int (9))
                                     (Prims.of_int (140)) (Prims.of_int (60)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "dummy"
                                     Prims.int_zero Prims.int_zero
                                     Prims.int_zero Prims.int_zero)))
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___5 ->
                                    FStar_Tactics_NamedView.pack uu___4))))
                | FStar_Tactics_NamedView.Tv_UInst (fv, uu___3) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___4 =
                            let uu___5 = param_fv s fv in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.Parametricity.fst"
                                       (Prims.of_int (144))
                                       (Prims.of_int (18))
                                       (Prims.of_int (144))
                                       (Prims.of_int (33)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.Parametricity.fst"
                                       (Prims.of_int (144))
                                       (Prims.of_int (9))
                                       (Prims.of_int (144))
                                       (Prims.of_int (34)))))
                              (Obj.magic uu___5)
                              (fun uu___6 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___7 ->
                                      FStar_Tactics_NamedView.Tv_FVar uu___6)) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (144)) (Prims.of_int (9))
                                     (Prims.of_int (144)) (Prims.of_int (34)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "dummy"
                                     Prims.int_zero Prims.int_zero
                                     Prims.int_zero Prims.int_zero)))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___6 ->
                                    FStar_Tactics_NamedView.pack uu___5))))
                | FStar_Tactics_NamedView.Tv_FVar fv ->
                    Obj.magic
                      (Obj.repr
                         (let uu___3 =
                            let uu___4 = param_fv s fv in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.Parametricity.fst"
                                       (Prims.of_int (144))
                                       (Prims.of_int (18))
                                       (Prims.of_int (144))
                                       (Prims.of_int (33)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.Parametricity.fst"
                                       (Prims.of_int (144))
                                       (Prims.of_int (9))
                                       (Prims.of_int (144))
                                       (Prims.of_int (34)))))
                              (Obj.magic uu___4)
                              (fun uu___5 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___6 ->
                                      FStar_Tactics_NamedView.Tv_FVar uu___5)) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (144)) (Prims.of_int (9))
                                     (Prims.of_int (144)) (Prims.of_int (34)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "dummy"
                                     Prims.int_zero Prims.int_zero
                                     Prims.int_zero Prims.int_zero)))
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___5 ->
                                    FStar_Tactics_NamedView.pack uu___4))))
                | FStar_Tactics_NamedView.Tv_Const c ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 ->
                               FStarC_Reflection_V2_Builtins.pack_ln
                                 (FStarC_Reflection_V2_Data.Tv_Const
                                    FStarC_Reflection_V2_Data.C_Unit))))
                | FStar_Tactics_NamedView.Tv_AscribedT
                    (t1, uu___3, uu___4, uu___5) ->
                    Obj.magic (Obj.repr (param' s t1))
                | FStar_Tactics_NamedView.Tv_AscribedC
                    (t1, uu___3, uu___4, uu___5) ->
                    Obj.magic (Obj.repr (param' s t1))
                | uu___3 ->
                    Obj.magic
                      (Obj.repr
                         (let uu___4 =
                            let uu___5 =
                              FStar_Tactics_Print.term_to_ast_string t in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.Parametricity.fst"
                                       (Prims.of_int (153))
                                       (Prims.of_int (23))
                                       (Prims.of_int (153))
                                       (Prims.of_int (59)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.Parametricity.fst"
                                       (Prims.of_int (153))
                                       (Prims.of_int (10))
                                       (Prims.of_int (153))
                                       (Prims.of_int (60)))))
                              (Obj.magic uu___5)
                              (fun uu___6 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___7 -> Unsupported uu___6)) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (153)) (Prims.of_int (10))
                                     (Prims.of_int (153)) (Prims.of_int (60)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (153)) (Prims.of_int (4))
                                     (Prims.of_int (153)) (Prims.of_int (60)))))
                            (Obj.magic uu___4)
                            (fun uu___5 -> FStar_Tactics_Effect.raise uu___5))))
               uu___2) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                 (Prims.of_int (96)) (Prims.of_int (2)) (Prims.of_int (153))
                 (Prims.of_int (60)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                 (Prims.of_int (95)) (Prims.of_int (6)) (Prims.of_int (95))
                 (Prims.of_int (7))))) (Obj.magic uu___)
        (fun r -> FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> r))
and (param_fv :
  param_state ->
    FStarC_Reflection_Types.fv ->
      (FStarC_Reflection_Types.fv, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    fun f ->
      FStar_Tactics_V2_Derived.try_with
        (fun uu___ -> match () with | () -> lookup_rec_fv s f)
        (fun uu___ ->
           let uu___1 =
             Obj.magic
               (FStar_Tactics_Effect.lift_div_tac
                  (fun uu___2 ->
                     FStarC_Reflection_V2_Builtins.explode_qn
                       (Prims.strcat
                          (FStarC_Reflection_V2_Builtins.implode_qn
                             (FStarC_Reflection_V2_Builtins.inspect_fv f))
                          "_param"))) in
           FStar_Tactics_Effect.tac_bind
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                      (Prims.of_int (164)) (Prims.of_int (12))
                      (Prims.of_int (164)) (Prims.of_int (61)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                      (Prims.of_int (166)) (Prims.of_int (2))
                      (Prims.of_int (186)) (Prims.of_int (24)))))
             (Obj.magic uu___1)
             (fun uu___2 ->
                (fun nm' ->
                   let uu___2 =
                     let uu___3 = FStarC_Tactics_V2_Builtins.top_env () in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.Parametricity.fst"
                                (Prims.of_int (166)) (Prims.of_int (19))
                                (Prims.of_int (166)) (Prims.of_int (31)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.Parametricity.fst"
                                (Prims.of_int (166)) (Prims.of_int (8))
                                (Prims.of_int (166)) (Prims.of_int (35)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___5 ->
                               FStarC_Reflection_V2_Builtins.lookup_typ
                                 uu___4 nm')) in
                   Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.Parametricity.fst"
                                 (Prims.of_int (166)) (Prims.of_int (8))
                                 (Prims.of_int (166)) (Prims.of_int (35)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.Parametricity.fst"
                                 (Prims.of_int (166)) (Prims.of_int (2))
                                 (Prims.of_int (186)) (Prims.of_int (24)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun uu___3 ->
                              match uu___3 with
                              | FStar_Pervasives_Native.Some se' ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___4 ->
                                             FStarC_Reflection_V2_Builtins.pack_fv
                                               nm')))
                              | FStar_Pervasives_Native.None ->
                                  Obj.magic
                                    (Obj.repr
                                       (let uu___4 =
                                          let uu___5 =
                                            let uu___6 =
                                              let uu___7 =
                                                let uu___8 =
                                                  let uu___9 =
                                                    last
                                                      (FStarC_Reflection_V2_Builtins.inspect_fv
                                                         f) in
                                                  FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.Parametricity.fst"
                                                             (Prims.of_int (171))
                                                             (Prims.of_int (50))
                                                             (Prims.of_int (171))
                                                             (Prims.of_int (69)))))
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
                                                              uu___10
                                                              "_param")) in
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Parametricity.fst"
                                                           (Prims.of_int (171))
                                                           (Prims.of_int (50))
                                                           (Prims.of_int (171))
                                                           (Prims.of_int (80)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Parametricity.fst"
                                                           (Prims.of_int (171))
                                                           (Prims.of_int (12))
                                                           (Prims.of_int (171))
                                                           (Prims.of_int (81)))))
                                                  (Obj.magic uu___8)
                                                  (fun uu___9 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___10 ->
                                                          [uu___9])) in
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.Parametricity.fst"
                                                         (Prims.of_int (171))
                                                         (Prims.of_int (12))
                                                         (Prims.of_int (171))
                                                         (Prims.of_int (81)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.Parametricity.fst"
                                                         (Prims.of_int (171))
                                                         (Prims.of_int (12))
                                                         (Prims.of_int (171))
                                                         (Prims.of_int (81)))))
                                                (Obj.magic uu___7)
                                                (fun uu___8 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___9 ->
                                                        "Parametricity" ::
                                                        uu___8)) in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.Parametricity.fst"
                                                       (Prims.of_int (171))
                                                       (Prims.of_int (12))
                                                       (Prims.of_int (171))
                                                       (Prims.of_int (81)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.Parametricity.fst"
                                                       (Prims.of_int (171))
                                                       (Prims.of_int (12))
                                                       (Prims.of_int (171))
                                                       (Prims.of_int (81)))))
                                              (Obj.magic uu___6)
                                              (fun uu___7 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___8 -> "Tactics"
                                                      :: uu___7)) in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.Parametricity.fst"
                                                     (Prims.of_int (171))
                                                     (Prims.of_int (12))
                                                     (Prims.of_int (171))
                                                     (Prims.of_int (81)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.Parametricity.fst"
                                                     (Prims.of_int (171))
                                                     (Prims.of_int (12))
                                                     (Prims.of_int (171))
                                                     (Prims.of_int (81)))))
                                            (Obj.magic uu___5)
                                            (fun uu___6 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___7 -> "FStar" ::
                                                    uu___6)) in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Parametricity.fst"
                                                   (Prims.of_int (171))
                                                   (Prims.of_int (12))
                                                   (Prims.of_int (171))
                                                   (Prims.of_int (81)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Parametricity.fst"
                                                   (Prims.of_int (173))
                                                   (Prims.of_int (2))
                                                   (Prims.of_int (186))
                                                   (Prims.of_int (24)))))
                                          (Obj.magic uu___4)
                                          (fun uu___5 ->
                                             (fun nm'1 ->
                                                let uu___5 =
                                                  let uu___6 =
                                                    FStarC_Tactics_V2_Builtins.top_env
                                                      () in
                                                  FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.Parametricity.fst"
                                                             (Prims.of_int (173))
                                                             (Prims.of_int (19))
                                                             (Prims.of_int (173))
                                                             (Prims.of_int (31)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.Parametricity.fst"
                                                             (Prims.of_int (173))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (173))
                                                             (Prims.of_int (35)))))
                                                    (Obj.magic uu___6)
                                                    (fun uu___7 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___8 ->
                                                            FStarC_Reflection_V2_Builtins.lookup_typ
                                                              uu___7 nm'1)) in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.Parametricity.fst"
                                                              (Prims.of_int (173))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (173))
                                                              (Prims.of_int (35)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.Parametricity.fst"
                                                              (Prims.of_int (173))
                                                              (Prims.of_int (2))
                                                              (Prims.of_int (186))
                                                              (Prims.of_int (24)))))
                                                     (Obj.magic uu___5)
                                                     (fun uu___6 ->
                                                        (fun uu___6 ->
                                                           match uu___6 with
                                                           | FStar_Pervasives_Native.Some
                                                               se' ->
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStarC_Reflection_V2_Builtins.pack_fv
                                                                    nm'1)))
                                                           | FStar_Pervasives_Native.None
                                                               ->
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    FStar_Tactics_V2_Derived.cur_module
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    last
                                                                    (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                    f) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___13
                                                                    "_param")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    [uu___12])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (60)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    uu___9
                                                                    uu___11))))
                                                                    uu___9) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun nm'2
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.top_env
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.lookup_typ
                                                                    uu___10
                                                                    nm'2)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    se' ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.pack_fv
                                                                    nm'2)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Tactics_Effect.raise
                                                                    (NotFoundFV
                                                                    f))))
                                                                    uu___8))))
                                                          uu___6))) uu___5))))
                             uu___3))) uu___2))
and (param_pat :
  param_state ->
    FStar_Tactics_NamedView.pattern ->
      ((param_state * (FStar_Tactics_NamedView.pattern *
         FStar_Tactics_NamedView.pattern * FStar_Tactics_NamedView.pattern)),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    fun p ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___2 ->
                fun uu___1 ->
                  (fun uu___1 ->
                     fun p1 ->
                       Obj.magic
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               match p1 with
                               | FStar_Tactics_NamedView.Pat_Dot_Term uu___3
                                   -> true
                               | uu___3 -> false))) uu___2 uu___1)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                 (Prims.of_int (190)) (Prims.of_int (4)) (Prims.of_int (192))
                 (Prims.of_int (16)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                 (Prims.of_int (195)) (Prims.of_int (2)) (Prims.of_int (235))
                 (Prims.of_int (57))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun is_dot_pat ->
              match p with
              | FStar_Tactics_NamedView.Pat_Cons
                  { FStar_Tactics_NamedView.head = fv;
                    FStar_Tactics_NamedView.univs = us;
                    FStar_Tactics_NamedView.subpats = pats;_}
                  ->
                  Obj.magic
                    (Obj.repr
                       (let uu___1 = param_fv s fv in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Parametricity.fst"
                                   (Prims.of_int (197)) (Prims.of_int (14))
                                   (Prims.of_int (197)) (Prims.of_int (27)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Parametricity.fst"
                                   (Prims.of_int (197)) (Prims.of_int (30))
                                   (Prims.of_int (215)) (Prims.of_int (56)))))
                          (Obj.magic uu___1)
                          (fun uu___2 ->
                             (fun fv' ->
                                let uu___2 =
                                  FStar_Tactics_Util.fold_left
                                    (fun uu___3 ->
                                       fun uu___4 ->
                                         match (uu___3, uu___4) with
                                         | ((s1, (pats0, pats1, patsr)),
                                            (p1, i)) ->
                                             let uu___5 = is_dot_pat p1 in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.Parametricity.fst"
                                                        (Prims.of_int (200))
                                                        (Prims.of_int (23))
                                                        (Prims.of_int (200))
                                                        (Prims.of_int (35)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.Parametricity.fst"
                                                        (Prims.of_int (200))
                                                        (Prims.of_int (20))
                                                        (Prims.of_int (206))
                                                        (Prims.of_int (60)))))
                                               (Obj.magic uu___5)
                                               (fun uu___6 ->
                                                  (fun uu___6 ->
                                                     if uu___6
                                                     then
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___7 ->
                                                                  (s1,
                                                                    (pats0,
                                                                    pats1,
                                                                    patsr)))))
                                                     else
                                                       Obj.magic
                                                         (Obj.repr
                                                            (let uu___8 =
                                                               param_pat s1
                                                                 p1 in
                                                             FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (202))
                                                                    (Prims.of_int (58)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (60)))))
                                                               (Obj.magic
                                                                  uu___8)
                                                               (fun uu___9 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (s',
                                                                    (p0, p11,
                                                                    pr)) ->
                                                                    (s',
                                                                    (((p0, i)
                                                                    ::
                                                                    pats0),
                                                                    ((p11, i)
                                                                    ::
                                                                    pats1),
                                                                    ((pr,
                                                                    false) ::
                                                                    (p11, i)
                                                                    ::
                                                                    (p0, i)
                                                                    ::
                                                                    patsr))))))))
                                                    uu___6))
                                    (s, ([], [], [])) pats in
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Parametricity.fst"
                                              (Prims.of_int (199))
                                              (Prims.of_int (6))
                                              (Prims.of_int (208))
                                              (Prims.of_int (21)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Parametricity.fst"
                                              (Prims.of_int (197))
                                              (Prims.of_int (30))
                                              (Prims.of_int (215))
                                              (Prims.of_int (56)))))
                                     (Obj.magic uu___2)
                                     (fun uu___3 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___4 ->
                                             match uu___3 with
                                             | (s', (pats0, pats1, patsr)) ->
                                                 (s',
                                                   ((FStar_Tactics_NamedView.Pat_Cons
                                                       {
                                                         FStar_Tactics_NamedView.head
                                                           = fv;
                                                         FStar_Tactics_NamedView.univs
                                                           = us;
                                                         FStar_Tactics_NamedView.subpats
                                                           =
                                                           (FStar_List_Tot_Base.rev
                                                              pats0)
                                                       }),
                                                     (FStar_Tactics_NamedView.Pat_Cons
                                                        {
                                                          FStar_Tactics_NamedView.head
                                                            = fv;
                                                          FStar_Tactics_NamedView.univs
                                                            = us;
                                                          FStar_Tactics_NamedView.subpats
                                                            =
                                                            (FStar_List_Tot_Base.rev
                                                               pats1)
                                                        }),
                                                     (FStar_Tactics_NamedView.Pat_Cons
                                                        {
                                                          FStar_Tactics_NamedView.head
                                                            = fv';
                                                          FStar_Tactics_NamedView.univs
                                                            = us;
                                                          FStar_Tactics_NamedView.subpats
                                                            =
                                                            (FStar_List_Tot_Base.rev
                                                               patsr)
                                                        }))))))) uu___2)))
              | FStar_Tactics_NamedView.Pat_Var
                  { FStar_Tactics_NamedView.v = v;
                    FStar_Tactics_NamedView.sort1 = sort;_}
                  ->
                  Obj.magic
                    (Obj.repr
                       (let uu___1 =
                          let uu___2 = FStarC_Tactics_Unseal.unseal sort in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (218)) (Prims.of_int (31))
                                     (Prims.of_int (218)) (Prims.of_int (44)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (218)) (Prims.of_int (12))
                                     (Prims.of_int (218)) (Prims.of_int (44)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___4 ->
                                    FStar_Tactics_NamedView.namedv_to_binder
                                      v uu___3)) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Parametricity.fst"
                                   (Prims.of_int (218)) (Prims.of_int (12))
                                   (Prims.of_int (218)) (Prims.of_int (44)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Parametricity.fst"
                                   (Prims.of_int (218)) (Prims.of_int (47))
                                   (Prims.of_int (222)) (Prims.of_int (80)))))
                          (Obj.magic uu___1)
                          (fun uu___2 ->
                             (fun b ->
                                let uu___2 = push_binder b s in
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Parametricity.fst"
                                              (Prims.of_int (219))
                                              (Prims.of_int (29))
                                              (Prims.of_int (219))
                                              (Prims.of_int (44)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Parametricity.fst"
                                              (Prims.of_int (218))
                                              (Prims.of_int (47))
                                              (Prims.of_int (222))
                                              (Prims.of_int (80)))))
                                     (Obj.magic uu___2)
                                     (fun uu___3 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___4 ->
                                             match uu___3 with
                                             | (s', (b0, b1, bR)) ->
                                                 (s',
                                                   ((FStar_Tactics_NamedView.Pat_Var
                                                       {
                                                         FStar_Tactics_NamedView.v
                                                           =
                                                           (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                                              b0);
                                                         FStar_Tactics_NamedView.sort1
                                                           =
                                                           (FStar_Sealed.seal
                                                              (FStar_Tactics_V2_Derived.binder_sort
                                                                 b0))
                                                       }),
                                                     (FStar_Tactics_NamedView.Pat_Var
                                                        {
                                                          FStar_Tactics_NamedView.v
                                                            =
                                                            (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                                               b1);
                                                          FStar_Tactics_NamedView.sort1
                                                            =
                                                            (FStar_Sealed.seal
                                                               (FStar_Tactics_V2_Derived.binder_sort
                                                                  b1))
                                                        }),
                                                     (FStar_Tactics_NamedView.Pat_Var
                                                        {
                                                          FStar_Tactics_NamedView.v
                                                            =
                                                            (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                                               bR);
                                                          FStar_Tactics_NamedView.sort1
                                                            =
                                                            (FStar_Sealed.seal
                                                               (FStar_Tactics_V2_Derived.binder_sort
                                                                  bR))
                                                        }))))))) uu___2)))
              | FStar_Tactics_NamedView.Pat_Dot_Term t ->
                  Obj.magic
                    (Obj.repr (FStar_Tactics_V2_Derived.fail "no dot pats"))
              | FStar_Tactics_NamedView.Pat_Constant c ->
                  Obj.magic
                    (Obj.repr
                       (let uu___1 =
                          FStar_Tactics_V2_Derived.fresh_binder_named "cR"
                            (FStarC_Reflection_V2_Builtins.pack_ln
                               FStarC_Reflection_V2_Data.Tv_Unknown) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Parametricity.fst"
                                   (Prims.of_int (232)) (Prims.of_int (12))
                                   (Prims.of_int (232)) (Prims.of_int (40)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Parametricity.fst"
                                   (Prims.of_int (233)) (Prims.of_int (4))
                                   (Prims.of_int (235)) (Prims.of_int (57)))))
                          (Obj.magic uu___1)
                          (fun b ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 ->
                                  (s,
                                    ((FStar_Tactics_NamedView.Pat_Constant c),
                                      (FStar_Tactics_NamedView.Pat_Constant c),
                                      (FStar_Tactics_NamedView.Pat_Var
                                         {
                                           FStar_Tactics_NamedView.v =
                                             (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                                b);
                                           FStar_Tactics_NamedView.sort1 =
                                             (FStar_Sealed.seal
                                                (FStarC_Reflection_V2_Builtins.pack_ln
                                                   FStarC_Reflection_V2_Data.Tv_Unknown))
                                         })))))))) uu___1)
and (param_br :
  param_state ->
    FStar_Tactics_NamedView.branch ->
      (FStar_Tactics_NamedView.branch, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    fun br ->
      let uu___ =
        Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> br)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                 (Prims.of_int (238)) (Prims.of_int (17))
                 (Prims.of_int (238)) (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                 (Prims.of_int (237)) (Prims.of_int (57))
                 (Prims.of_int (240)) (Prims.of_int (21)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | (pat, t) ->
                  let uu___2 = param_pat s pat in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.Parametricity.fst"
                                (Prims.of_int (239)) (Prims.of_int (27))
                                (Prims.of_int (239)) (Prims.of_int (42)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.Parametricity.fst"
                                (Prims.of_int (238)) (Prims.of_int (22))
                                (Prims.of_int (240)) (Prims.of_int (21)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          (fun uu___3 ->
                             match uu___3 with
                             | (s', (uu___4, uu___5, pat')) ->
                                 let uu___6 = param' s' t in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Parametricity.fst"
                                               (Prims.of_int (240))
                                               (Prims.of_int (9))
                                               (Prims.of_int (240))
                                               (Prims.of_int (20)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Parametricity.fst"
                                               (Prims.of_int (240))
                                               (Prims.of_int (2))
                                               (Prims.of_int (240))
                                               (Prims.of_int (21)))))
                                      (Obj.magic uu___6)
                                      (fun uu___7 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___8 -> (pat', uu___7)))))
                            uu___3))) uu___1)
and (push_binder :
  FStar_Tactics_NamedView.binder ->
    param_state ->
      ((param_state * (FStar_Tactics_NamedView.binder *
         FStar_Tactics_NamedView.binder * FStar_Tactics_NamedView.binder)),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun s ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> b.FStar_Tactics_NamedView.qual)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                 (Prims.of_int (243)) (Prims.of_int (10))
                 (Prims.of_int (243)) (Prims.of_int (16)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                 (Prims.of_int (243)) (Prims.of_int (19))
                 (Prims.of_int (257)) (Prims.of_int (22)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun q ->
              let uu___1 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 -> b.FStar_Tactics_NamedView.sort)) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.Parametricity.fst"
                            (Prims.of_int (244)) (Prims.of_int (12))
                            (Prims.of_int (244)) (Prims.of_int (18)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.Parametricity.fst"
                            (Prims.of_int (244)) (Prims.of_int (21))
                            (Prims.of_int (257)) (Prims.of_int (22)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun typ ->
                         let uu___2 =
                           FStarC_Tactics_Unseal.unseal
                             b.FStar_Tactics_NamedView.ppname in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.Parametricity.fst"
                                       (Prims.of_int (245))
                                       (Prims.of_int (13))
                                       (Prims.of_int (245))
                                       (Prims.of_int (28)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.Parametricity.fst"
                                       (Prims.of_int (245))
                                       (Prims.of_int (31))
                                       (Prims.of_int (257))
                                       (Prims.of_int (22)))))
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 (fun name ->
                                    let uu___3 =
                                      Obj.magic
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___6 ->
                                              fun uu___5 ->
                                                fun uu___4 ->
                                                  (fun uu___4 ->
                                                     fun s1 ->
                                                       fun t ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___5 ->
                                                                 Prims.strcat
                                                                   s1 t)))
                                                    uu___6 uu___5 uu___4)) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.Parametricity.fst"
                                                  (Prims.of_int (246))
                                                  (Prims.of_int (53))
                                                  (Prims.of_int (246))
                                                  (Prims.of_int (60)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.Parametricity.fst"
                                                  (Prims.of_int (246))
                                                  (Prims.of_int (63))
                                                  (Prims.of_int (257))
                                                  (Prims.of_int (22)))))
                                         (Obj.magic uu___3)
                                         (fun uu___4 ->
                                            (fun decor ->
                                               let uu___4 =
                                                 let uu___5 = decor name "0" in
                                                 FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.Parametricity.fst"
                                                            (Prims.of_int (247))
                                                            (Prims.of_int (31))
                                                            (Prims.of_int (247))
                                                            (Prims.of_int (47)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.Parametricity.fst"
                                                            (Prims.of_int (247))
                                                            (Prims.of_int (12))
                                                            (Prims.of_int (247))
                                                            (Prims.of_int (72)))))
                                                   (Obj.magic uu___5)
                                                   (fun uu___6 ->
                                                      (fun uu___6 ->
                                                         let uu___7 =
                                                           replace_by s false
                                                             typ in
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (72)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (72)))))
                                                              (Obj.magic
                                                                 uu___7)
                                                              (fun uu___8 ->
                                                                 (fun uu___8
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.fresh_binder_named
                                                                    uu___6
                                                                    uu___8))
                                                                   uu___8)))
                                                        uu___6) in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.Parametricity.fst"
                                                             (Prims.of_int (247))
                                                             (Prims.of_int (12))
                                                             (Prims.of_int (247))
                                                             (Prims.of_int (72)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.Parametricity.fst"
                                                             (Prims.of_int (247))
                                                             (Prims.of_int (75))
                                                             (Prims.of_int (257))
                                                             (Prims.of_int (22)))))
                                                    (Obj.magic uu___4)
                                                    (fun uu___5 ->
                                                       (fun bx0 ->
                                                          let uu___5 =
                                                            let uu___6 =
                                                              decor name "1" in
                                                            FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (47)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (71)))))
                                                              (Obj.magic
                                                                 uu___6)
                                                              (fun uu___7 ->
                                                                 (fun uu___7
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    replace_by
                                                                    s true
                                                                    typ in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.fresh_binder_named
                                                                    uu___7
                                                                    uu___9))
                                                                    uu___9)))
                                                                   uu___7) in
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (71)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (22)))))
                                                               (Obj.magic
                                                                  uu___5)
                                                               (fun uu___6 ->
                                                                  (fun bx1 ->
                                                                    let uu___6
                                                                    =
                                                                    let uu___7
                                                                    =
                                                                    decor
                                                                    name "R" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (119)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_V2_SyntaxCoercions.binder_to_term
                                                                    bx1)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (117)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (119)))))
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
                                                                    FStar_Tactics_V2_SyntaxCoercions.binder_to_term
                                                                    bx0)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (119)))))
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
                                                                    param' s
                                                                    typ in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (119)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    (uu___15,
                                                                    (uu___13,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (uu___11,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))))))
                                                                    uu___13)))
                                                                    uu___11) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (119)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (119)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.fresh_binder_named
                                                                    uu___8
                                                                    uu___10))
                                                                    uu___10)))
                                                                    uu___8) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (249))
                                                                    (Prims.of_int (119)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun bxr
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    ((push_var_to_state
                                                                    (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                                                    b)
                                                                    {
                                                                    FStar_Tactics_NamedView.uniq
                                                                    =
                                                                    (bx0.FStar_Tactics_NamedView.uniq);
                                                                    FStar_Tactics_NamedView.ppname
                                                                    =
                                                                    (bx0.FStar_Tactics_NamedView.ppname);
                                                                    FStar_Tactics_NamedView.sort
                                                                    =
                                                                    (bx0.FStar_Tactics_NamedView.sort);
                                                                    FStar_Tactics_NamedView.qual
                                                                    = q;
                                                                    FStar_Tactics_NamedView.attrs
                                                                    =
                                                                    (bx0.FStar_Tactics_NamedView.attrs)
                                                                    }
                                                                    {
                                                                    FStar_Tactics_NamedView.uniq
                                                                    =
                                                                    (bx1.FStar_Tactics_NamedView.uniq);
                                                                    FStar_Tactics_NamedView.ppname
                                                                    =
                                                                    (bx1.FStar_Tactics_NamedView.ppname);
                                                                    FStar_Tactics_NamedView.sort
                                                                    =
                                                                    (bx1.FStar_Tactics_NamedView.sort);
                                                                    FStar_Tactics_NamedView.qual
                                                                    = q;
                                                                    FStar_Tactics_NamedView.attrs
                                                                    =
                                                                    (bx1.FStar_Tactics_NamedView.attrs)
                                                                    }
                                                                    {
                                                                    FStar_Tactics_NamedView.uniq
                                                                    =
                                                                    (bxr.FStar_Tactics_NamedView.uniq);
                                                                    FStar_Tactics_NamedView.ppname
                                                                    =
                                                                    (bxr.FStar_Tactics_NamedView.ppname);
                                                                    FStar_Tactics_NamedView.sort
                                                                    =
                                                                    (bxr.FStar_Tactics_NamedView.sort);
                                                                    FStar_Tactics_NamedView.qual
                                                                    = q;
                                                                    FStar_Tactics_NamedView.attrs
                                                                    =
                                                                    (bxr.FStar_Tactics_NamedView.attrs)
                                                                    } s),
                                                                    ({
                                                                    FStar_Tactics_NamedView.uniq
                                                                    =
                                                                    (bx0.FStar_Tactics_NamedView.uniq);
                                                                    FStar_Tactics_NamedView.ppname
                                                                    =
                                                                    (bx0.FStar_Tactics_NamedView.ppname);
                                                                    FStar_Tactics_NamedView.sort
                                                                    =
                                                                    (bx0.FStar_Tactics_NamedView.sort);
                                                                    FStar_Tactics_NamedView.qual
                                                                    = q;
                                                                    FStar_Tactics_NamedView.attrs
                                                                    =
                                                                    (bx0.FStar_Tactics_NamedView.attrs)
                                                                    },
                                                                    {
                                                                    FStar_Tactics_NamedView.uniq
                                                                    =
                                                                    (bx1.FStar_Tactics_NamedView.uniq);
                                                                    FStar_Tactics_NamedView.ppname
                                                                    =
                                                                    (bx1.FStar_Tactics_NamedView.ppname);
                                                                    FStar_Tactics_NamedView.sort
                                                                    =
                                                                    (bx1.FStar_Tactics_NamedView.sort);
                                                                    FStar_Tactics_NamedView.qual
                                                                    = q;
                                                                    FStar_Tactics_NamedView.attrs
                                                                    =
                                                                    (bx1.FStar_Tactics_NamedView.attrs)
                                                                    },
                                                                    {
                                                                    FStar_Tactics_NamedView.uniq
                                                                    =
                                                                    (bxr.FStar_Tactics_NamedView.uniq);
                                                                    FStar_Tactics_NamedView.ppname
                                                                    =
                                                                    (bxr.FStar_Tactics_NamedView.ppname);
                                                                    FStar_Tactics_NamedView.sort
                                                                    =
                                                                    (bxr.FStar_Tactics_NamedView.sort);
                                                                    FStar_Tactics_NamedView.qual
                                                                    = q;
                                                                    FStar_Tactics_NamedView.attrs
                                                                    =
                                                                    (bxr.FStar_Tactics_NamedView.attrs)
                                                                    }))))))
                                                                    uu___6)))
                                                         uu___5))) uu___4)))
                                   uu___3))) uu___2))) uu___1)
let (init_param_state : param_state) =
  { bvmap = []; fresh = Prims.int_zero; recs = [] }
let (param :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = param' init_param_state t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
               (Prims.of_int (267)) (Prims.of_int (10)) (Prims.of_int (267))
               (Prims.of_int (35)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
               (Prims.of_int (267)) (Prims.of_int (6)) (Prims.of_int (267))
               (Prims.of_int (7))))) (Obj.magic uu___)
      (fun t1 -> FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> t1))
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.Parametricity.param"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Parametricity.param (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 param)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Reflection_V2_Embeddings.e_term psc ncb us args)
let (fv_to_tm :
  FStarC_Reflection_Types.fv ->
    (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun f ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               FStar_Tactics_NamedView.pack
                 (FStar_Tactics_NamedView.Tv_FVar f)))) uu___
let (param_ctor :
  FStarC_Reflection_Types.name ->
    param_state ->
      FStarC_Reflection_V2_Data.ctor ->
        (FStarC_Reflection_V2_Data.ctor, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm_ty ->
    fun s ->
      fun c ->
        let uu___ =
          Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> c)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                   (Prims.of_int (275)) (Prims.of_int (15))
                   (Prims.of_int (275)) (Prims.of_int (16)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                   (Prims.of_int (273)) (Prims.of_int (65))
                   (Prims.of_int (299)) (Prims.of_int (3)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | (nm, ty) ->
                    let uu___2 =
                      let uu___3 = FStar_Tactics_V2_Derived.cur_module () in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.Parametricity.fst"
                                 (Prims.of_int (276)) (Prims.of_int (12))
                                 (Prims.of_int (276)) (Prims.of_int (25)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.Parametricity.fst"
                                 (Prims.of_int (276)) (Prims.of_int (12))
                                 (Prims.of_int (276)) (Prims.of_int (48)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           (fun uu___4 ->
                              let uu___5 =
                                let uu___6 =
                                  let uu___7 = last nm in
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.Parametricity.fst"
                                             (Prims.of_int (276))
                                             (Prims.of_int (29))
                                             (Prims.of_int (276))
                                             (Prims.of_int (36)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range "Prims.fst"
                                             (Prims.of_int (611))
                                             (Prims.of_int (19))
                                             (Prims.of_int (611))
                                             (Prims.of_int (31)))))
                                    (Obj.magic uu___7)
                                    (fun uu___8 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___9 ->
                                            Prims.strcat uu___8 "_param")) in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Parametricity.fst"
                                           (Prims.of_int (276))
                                           (Prims.of_int (29))
                                           (Prims.of_int (276))
                                           (Prims.of_int (47)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Parametricity.fst"
                                           (Prims.of_int (276))
                                           (Prims.of_int (28))
                                           (Prims.of_int (276))
                                           (Prims.of_int (48)))))
                                  (Obj.magic uu___6)
                                  (fun uu___7 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___8 -> [uu___7])) in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.Parametricity.fst"
                                            (Prims.of_int (276))
                                            (Prims.of_int (28))
                                            (Prims.of_int (276))
                                            (Prims.of_int (48)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.Parametricity.fst"
                                            (Prims.of_int (276))
                                            (Prims.of_int (12))
                                            (Prims.of_int (276))
                                            (Prims.of_int (48)))))
                                   (Obj.magic uu___5)
                                   (fun uu___6 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___7 ->
                                           FStar_List_Tot_Base.op_At uu___4
                                             uu___6)))) uu___4) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.Parametricity.fst"
                                  (Prims.of_int (276)) (Prims.of_int (12))
                                  (Prims.of_int (276)) (Prims.of_int (48)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.Parametricity.fst"
                                  (Prims.of_int (276)) (Prims.of_int (51))
                                  (Prims.of_int (299)) (Prims.of_int (3)))))
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            (fun nm' ->
                               let uu___3 =
                                 FStar_Tactics_V2_SyntaxHelpers.collect_arr_bs
                                   ty in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.Parametricity.fst"
                                             (Prims.of_int (277))
                                             (Prims.of_int (14))
                                             (Prims.of_int (277))
                                             (Prims.of_int (31)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.Parametricity.fst"
                                             (Prims.of_int (276))
                                             (Prims.of_int (51))
                                             (Prims.of_int (299))
                                             (Prims.of_int (3)))))
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       (fun uu___4 ->
                                          match uu___4 with
                                          | (bs, c1) ->
                                              let uu___5 =
                                                let uu___6 =
                                                  fv_to_tm
                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                       nm) in
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Parametricity.fst"
                                                           (Prims.of_int (279))
                                                           (Prims.of_int (25))
                                                           (Prims.of_int (279))
                                                           (Prims.of_int (48)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Parametricity.fst"
                                                           (Prims.of_int (279))
                                                           (Prims.of_int (13))
                                                           (Prims.of_int (279))
                                                           (Prims.of_int (51)))))
                                                  (Obj.magic uu___6)
                                                  (fun uu___7 ->
                                                     (fun uu___7 ->
                                                        Obj.magic
                                                          (app_binders uu___7
                                                             bs)) uu___7) in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.Parametricity.fst"
                                                            (Prims.of_int (279))
                                                            (Prims.of_int (13))
                                                            (Prims.of_int (279))
                                                            (Prims.of_int (51)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.Parametricity.fst"
                                                            (Prims.of_int (279))
                                                            (Prims.of_int (54))
                                                            (Prims.of_int (299))
                                                            (Prims.of_int (3)))))
                                                   (Obj.magic uu___5)
                                                   (fun uu___6 ->
                                                      (fun orig ->
                                                         let uu___6 =
                                                           FStar_Tactics_Util.fold_left
                                                             (fun uu___7 ->
                                                                fun b ->
                                                                  match uu___7
                                                                  with
                                                                  | (s1, bvs)
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    push_binder
                                                                    b s1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (s2,
                                                                    (bx0,
                                                                    bx1, bxr))
                                                                    ->
                                                                    (s2, (bxr
                                                                    :: bx1 ::
                                                                    bx0 ::
                                                                    bvs)))))
                                                             (s, []) bs in
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (283))
                                                                    (Prims.of_int (67)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (3)))))
                                                              (Obj.magic
                                                                 uu___6)
                                                              (fun uu___7 ->
                                                                 (fun uu___7
                                                                    ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (s1, bs1)
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_List_Tot_Base.rev
                                                                    bs1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (285))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun bs2
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    match 
                                                                    FStar_Tactics_NamedView.inspect_comp
                                                                    c1
                                                                    with
                                                                    | 
                                                                    FStarC_Reflection_V2_Data.C_Total
                                                                    ty1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> ty1))
                                                                    | 
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "param_ctor got a non-tot comp") in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (290))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (291))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun cod
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    param' s1
                                                                    cod in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (85)))))
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
                                                                    replace_by
                                                                    s1 false
                                                                    orig in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (85)))))
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
                                                                    let uu___17
                                                                    =
                                                                    replace_by
                                                                    s1 true
                                                                    orig in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (84)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (85)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    [uu___18])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (85)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    uu___15
                                                                    ::
                                                                    uu___17))))
                                                                    uu___15) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (85)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Reflection_V2_Derived.mk_e_app
                                                                    uu___12
                                                                    uu___14))))
                                                                    uu___12) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (88))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun cod1
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr
                                                                    bs2 cod1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun ty'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (nm',
                                                                    ty')))))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                   uu___7)))
                                                        uu___6))) uu___4)))
                              uu___3))) uu___1)
let (param_inductive :
  FStarC_Reflection_Types.sigelt ->
    FStarC_Reflection_Types.fv ->
      FStarC_Reflection_Types.fv ->
        (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun se ->
    fun fv0 ->
      fun fv1 ->
        let uu___ = FStar_Tactics_NamedView.inspect_sigelt se in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                   (Prims.of_int (305)) (Prims.of_int (8))
                   (Prims.of_int (305)) (Prims.of_int (25)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                   (Prims.of_int (305)) (Prims.of_int (2))
                   (Prims.of_int (326)) (Prims.of_int (16)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | FStar_Tactics_NamedView.Sg_Inductive
                    { FStar_Tactics_NamedView.nm = nm;
                      FStar_Tactics_NamedView.univs1 = univs;
                      FStar_Tactics_NamedView.params = params;
                      FStar_Tactics_NamedView.typ = typ;
                      FStar_Tactics_NamedView.ctors = ctors;_}
                    ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 =
                            Obj.magic
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___3 ->
                                    push_fv fv0 fv1 init_param_state)) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (308)) (Prims.of_int (12))
                                     (Prims.of_int (308)) (Prims.of_int (44)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (308)) (Prims.of_int (47))
                                     (Prims.of_int (325)) (Prims.of_int (20)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun s ->
                                  let uu___3 =
                                    let uu___4 =
                                      fv_to_tm
                                        (FStarC_Reflection_V2_Builtins.pack_fv
                                           nm) in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Parametricity.fst"
                                               (Prims.of_int (309))
                                               (Prims.of_int (27))
                                               (Prims.of_int (309))
                                               (Prims.of_int (50)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Parametricity.fst"
                                               (Prims.of_int (309))
                                               (Prims.of_int (15))
                                               (Prims.of_int (309))
                                               (Prims.of_int (57)))))
                                      (Obj.magic uu___4)
                                      (fun uu___5 ->
                                         (fun uu___5 ->
                                            Obj.magic
                                              (app_binders uu___5 params))
                                           uu___5) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Parametricity.fst"
                                                (Prims.of_int (309))
                                                (Prims.of_int (15))
                                                (Prims.of_int (309))
                                                (Prims.of_int (57)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Parametricity.fst"
                                                (Prims.of_int (309))
                                                (Prims.of_int (60))
                                                (Prims.of_int (325))
                                                (Prims.of_int (20)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          (fun orig ->
                                             let uu___4 =
                                               FStar_Tactics_Util.fold_left
                                                 (fun uu___5 ->
                                                    fun b ->
                                                      match uu___5 with
                                                      | (s1, bvs) ->
                                                          let uu___6 =
                                                            push_binder b s1 in
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (79)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (57)))))
                                                            (Obj.magic uu___6)
                                                            (fun uu___7 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___8
                                                                    ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (s2,
                                                                    (bx0,
                                                                    bx1, bxr))
                                                                    ->
                                                                    (s2, (bxr
                                                                    :: bx1 ::
                                                                    bx0 ::
                                                                    bvs)))))
                                                 (s, []) params in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Parametricity.fst"
                                                           (Prims.of_int (312))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (316))
                                                           (Prims.of_int (73)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Parametricity.fst"
                                                           (Prims.of_int (309))
                                                           (Prims.of_int (60))
                                                           (Prims.of_int (325))
                                                           (Prims.of_int (20)))))
                                                  (Obj.magic uu___4)
                                                  (fun uu___5 ->
                                                     (fun uu___5 ->
                                                        match uu___5 with
                                                        | (s1, param_bs) ->
                                                            let uu___6 =
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___7 ->
                                                                    FStar_List_Tot_Base.rev
                                                                    param_bs)) in
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (40)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (20)))))
                                                                 (Obj.magic
                                                                    uu___6)
                                                                 (fun uu___7
                                                                    ->
                                                                    (fun
                                                                    param_bs1
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    param' s1
                                                                    typ in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (87)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    replace_by
                                                                    s1 false
                                                                    orig in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (87)))))
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
                                                                    replace_by
                                                                    s1 true
                                                                    orig in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (87)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    [uu___15])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (87)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    uu___12
                                                                    ::
                                                                    uu___14))))
                                                                    uu___12) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (87)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Reflection_V2_Derived.mk_e_app
                                                                    uu___9
                                                                    uu___11))))
                                                                    uu___9) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun typ1
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    FStar_Tactics_Util.map
                                                                    (param_ctor
                                                                    nm s1)
                                                                    ctors in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    ctors1 ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_NamedView.Sg_Inductive
                                                                    {
                                                                    FStar_Tactics_NamedView.nm
                                                                    =
                                                                    (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                    fv1);
                                                                    FStar_Tactics_NamedView.univs1
                                                                    = univs;
                                                                    FStar_Tactics_NamedView.params
                                                                    =
                                                                    param_bs1;
                                                                    FStar_Tactics_NamedView.typ
                                                                    = typ1;
                                                                    FStar_Tactics_NamedView.ctors
                                                                    = ctors1
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun se1
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    FStar_Tactics_NamedView.pack_sigelt
                                                                    se1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    [uu___11]))))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                       uu___5))) uu___4)))
                                 uu___3)))
                | uu___2 ->
                    Obj.magic (Obj.repr (FStar_Tactics_V2_Derived.fail "")))
               uu___1)
let (param_letbinding :
  FStarC_Reflection_Types.sigelt ->
    FStarC_Reflection_Types.fv ->
      FStarC_Reflection_Types.fv ->
        (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun se ->
    fun fv0 ->
      fun fv1 ->
        let uu___ = FStar_Tactics_NamedView.inspect_sigelt se in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                   (Prims.of_int (329)) (Prims.of_int (8))
                   (Prims.of_int (329)) (Prims.of_int (25)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                   (Prims.of_int (329)) (Prims.of_int (2))
                   (Prims.of_int (335)) (Prims.of_int (35)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | FStar_Tactics_NamedView.Sg_Let
                    { FStar_Tactics_NamedView.isrec = r;
                      FStar_Tactics_NamedView.lbs = lb::[];_}
                    ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 =
                            param lb.FStar_Tactics_NamedView.lb_typ in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (331)) (Prims.of_int (14))
                                     (Prims.of_int (331)) (Prims.of_int (29)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (331)) (Prims.of_int (32))
                                     (Prims.of_int (334)) (Prims.of_int (21)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun rrr ->
                                  let uu___3 =
                                    let uu___4 =
                                      let uu___5 =
                                        let uu___6 = fv_to_tm fv0 in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Parametricity.fst"
                                                   (Prims.of_int (332))
                                                   (Prims.of_int (51))
                                                   (Prims.of_int (332))
                                                   (Prims.of_int (63)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Parametricity.fst"
                                                   (Prims.of_int (332))
                                                   (Prims.of_int (50))
                                                   (Prims.of_int (332))
                                                   (Prims.of_int (78)))))
                                          (Obj.magic uu___6)
                                          (fun uu___7 ->
                                             (fun uu___7 ->
                                                let uu___8 =
                                                  let uu___9 = fv_to_tm fv0 in
                                                  FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.Parametricity.fst"
                                                             (Prims.of_int (332))
                                                             (Prims.of_int (65))
                                                             (Prims.of_int (332))
                                                             (Prims.of_int (77)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.Parametricity.fst"
                                                             (Prims.of_int (332))
                                                             (Prims.of_int (50))
                                                             (Prims.of_int (332))
                                                             (Prims.of_int (78)))))
                                                    (Obj.magic uu___9)
                                                    (fun uu___10 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___11 ->
                                                            [uu___10])) in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.Parametricity.fst"
                                                              (Prims.of_int (332))
                                                              (Prims.of_int (50))
                                                              (Prims.of_int (332))
                                                              (Prims.of_int (78)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.Parametricity.fst"
                                                              (Prims.of_int (332))
                                                              (Prims.of_int (50))
                                                              (Prims.of_int (332))
                                                              (Prims.of_int (78)))))
                                                     (Obj.magic uu___8)
                                                     (fun uu___9 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___10 ->
                                                             uu___7 :: uu___9))))
                                               uu___7) in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.Parametricity.fst"
                                                 (Prims.of_int (332))
                                                 (Prims.of_int (50))
                                                 (Prims.of_int (332))
                                                 (Prims.of_int (78)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.Parametricity.fst"
                                                 (Prims.of_int (332))
                                                 (Prims.of_int (36))
                                                 (Prims.of_int (332))
                                                 (Prims.of_int (79)))))
                                        (Obj.magic uu___5)
                                        (fun uu___6 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___7 ->
                                                FStar_Reflection_V2_Derived.mk_e_app
                                                  rrr uu___6)) in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Parametricity.fst"
                                               (Prims.of_int (332))
                                               (Prims.of_int (36))
                                               (Prims.of_int (332))
                                               (Prims.of_int (79)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Parametricity.fst"
                                               (Prims.of_int (332))
                                               (Prims.of_int (23))
                                               (Prims.of_int (332))
                                               (Prims.of_int (79)))))
                                      (Obj.magic uu___4)
                                      (fun uu___5 ->
                                         (fun uu___5 ->
                                            Obj.magic
                                              (FStar_Tactics_V2_Derived.norm_term
                                                 [] uu___5)) uu___5) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Parametricity.fst"
                                                (Prims.of_int (332))
                                                (Prims.of_int (23))
                                                (Prims.of_int (332))
                                                (Prims.of_int (79)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Parametricity.fst"
                                                (Prims.of_int (332))
                                                (Prims.of_int (82))
                                                (Prims.of_int (334))
                                                (Prims.of_int (21)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          (fun expected_typ ->
                                             let uu___4 =
                                               let uu___5 =
                                                 let uu___6 =
                                                   let uu___7 =
                                                     let uu___8 =
                                                       param
                                                         lb.FStar_Tactics_NamedView.lb_def in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.Parametricity.fst"
                                                                (Prims.of_int (333))
                                                                (Prims.of_int (94))
                                                                (Prims.of_int (333))
                                                                (Prims.of_int (111)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.Parametricity.fst"
                                                                (Prims.of_int (333))
                                                                (Prims.of_int (37))
                                                                (Prims.of_int (333))
                                                                (Prims.of_int (111)))))
                                                       (Obj.magic uu___8)
                                                       (fun uu___9 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___10 ->
                                                               {
                                                                 FStar_Tactics_NamedView.lb_fv
                                                                   = fv1;
                                                                 FStar_Tactics_NamedView.lb_us
                                                                   =
                                                                   (lb.FStar_Tactics_NamedView.lb_us);
                                                                 FStar_Tactics_NamedView.lb_typ
                                                                   =
                                                                   expected_typ;
                                                                 FStar_Tactics_NamedView.lb_def
                                                                   = uu___9
                                                               })) in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.Parametricity.fst"
                                                              (Prims.of_int (333))
                                                              (Prims.of_int (37))
                                                              (Prims.of_int (333))
                                                              (Prims.of_int (111)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.Parametricity.fst"
                                                              (Prims.of_int (333))
                                                              (Prims.of_int (35))
                                                              (Prims.of_int (333))
                                                              (Prims.of_int (113)))))
                                                     (Obj.magic uu___7)
                                                     (fun uu___8 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___9 ->
                                                             [uu___8])) in
                                                 FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.Parametricity.fst"
                                                            (Prims.of_int (333))
                                                            (Prims.of_int (35))
                                                            (Prims.of_int (333))
                                                            (Prims.of_int (113)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.Parametricity.fst"
                                                            (Prims.of_int (333))
                                                            (Prims.of_int (22))
                                                            (Prims.of_int (333))
                                                            (Prims.of_int (113)))))
                                                   (Obj.magic uu___6)
                                                   (fun uu___7 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___8 ->
                                                           {
                                                             FStar_Tactics_NamedView.isrec
                                                               = r;
                                                             FStar_Tactics_NamedView.lbs
                                                               = uu___7
                                                           })) in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.Parametricity.fst"
                                                          (Prims.of_int (333))
                                                          (Prims.of_int (22))
                                                          (Prims.of_int (333))
                                                          (Prims.of_int (113)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.Parametricity.fst"
                                                          (Prims.of_int (333))
                                                          (Prims.of_int (14))
                                                          (Prims.of_int (333))
                                                          (Prims.of_int (114)))))
                                                 (Obj.magic uu___5)
                                                 (fun uu___6 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___7 ->
                                                         FStar_Tactics_NamedView.Sg_Let
                                                           uu___6)) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Parametricity.fst"
                                                           (Prims.of_int (333))
                                                           (Prims.of_int (14))
                                                           (Prims.of_int (333))
                                                           (Prims.of_int (114)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Parametricity.fst"
                                                           (Prims.of_int (334))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (334))
                                                           (Prims.of_int (21)))))
                                                  (Obj.magic uu___4)
                                                  (fun uu___5 ->
                                                     (fun se' ->
                                                        let uu___5 =
                                                          FStar_Tactics_NamedView.pack_sigelt
                                                            se' in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (20)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (334))
                                                                    (Prims.of_int (21)))))
                                                             (Obj.magic
                                                                uu___5)
                                                             (fun uu___6 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___7
                                                                    ->
                                                                    [uu___6]))))
                                                       uu___5))) uu___4)))
                                 uu___3)))
                | uu___2 ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_V2_Derived.fail "no mutual recursion")))
               uu___1)
let (paramd :
  Prims.string ->
    (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm ->
    let uu___ =
      let uu___1 =
        let uu___2 = FStar_Tactics_V2_Derived.cur_module () in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                   (Prims.of_int (339)) (Prims.of_int (24))
                   (Prims.of_int (339)) (Prims.of_int (37)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                   (Prims.of_int (339)) (Prims.of_int (23))
                   (Prims.of_int (339)) (Prims.of_int (74)))))
          (Obj.magic uu___2)
          (fun uu___3 ->
             (fun uu___3 ->
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      last (FStarC_Reflection_V2_Builtins.explode_qn nm) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.Parametricity.fst"
                               (Prims.of_int (339)) (Prims.of_int (41))
                               (Prims.of_int (339)) (Prims.of_int (61)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Prims.fst"
                               (Prims.of_int (611)) (Prims.of_int (19))
                               (Prims.of_int (611)) (Prims.of_int (31)))))
                      (Obj.magic uu___6)
                      (fun uu___7 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___8 -> Prims.strcat uu___7 "_param")) in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.Parametricity.fst"
                             (Prims.of_int (339)) (Prims.of_int (41))
                             (Prims.of_int (339)) (Prims.of_int (72)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.Parametricity.fst"
                             (Prims.of_int (339)) (Prims.of_int (40))
                             (Prims.of_int (339)) (Prims.of_int (73)))))
                    (Obj.magic uu___5)
                    (fun uu___6 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___7 -> [uu___6])) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.Parametricity.fst"
                              (Prims.of_int (339)) (Prims.of_int (40))
                              (Prims.of_int (339)) (Prims.of_int (73)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.Parametricity.fst"
                              (Prims.of_int (339)) (Prims.of_int (23))
                              (Prims.of_int (339)) (Prims.of_int (74)))))
                     (Obj.magic uu___4)
                     (fun uu___5 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___6 ->
                             FStar_List_Tot_Base.op_At uu___3 uu___5))))
               uu___3) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                 (Prims.of_int (339)) (Prims.of_int (23))
                 (Prims.of_int (339)) (Prims.of_int (74)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
                 (Prims.of_int (339)) (Prims.of_int (12))
                 (Prims.of_int (339)) (Prims.of_int (74)))))
        (Obj.magic uu___1)
        (fun uu___2 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___3 -> FStarC_Reflection_V2_Builtins.implode_qn uu___2)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
               (Prims.of_int (339)) (Prims.of_int (12)) (Prims.of_int (339))
               (Prims.of_int (74)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
               (Prims.of_int (339)) (Prims.of_int (77)) (Prims.of_int (351))
               (Prims.of_int (7))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun nm' ->
            let uu___1 =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      FStarC_Reflection_V2_Builtins.pack_fv
                        (FStarC_Reflection_V2_Builtins.explode_qn nm))) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.Tactics.Parametricity.fst"
                          (Prims.of_int (340)) (Prims.of_int (12))
                          (Prims.of_int (340)) (Prims.of_int (35)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.Tactics.Parametricity.fst"
                          (Prims.of_int (340)) (Prims.of_int (38))
                          (Prims.of_int (351)) (Prims.of_int (7)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun fv0 ->
                       let uu___2 =
                         Obj.magic
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___3 ->
                                 FStarC_Reflection_V2_Builtins.pack_fv
                                   (FStarC_Reflection_V2_Builtins.explode_qn
                                      nm'))) in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (341)) (Prims.of_int (12))
                                     (Prims.of_int (341)) (Prims.of_int (36)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Parametricity.fst"
                                     (Prims.of_int (341)) (Prims.of_int (39))
                                     (Prims.of_int (351)) (Prims.of_int (7)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun fv1 ->
                                  let uu___3 =
                                    let uu___4 =
                                      FStarC_Tactics_V2_Builtins.top_env () in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Parametricity.fst"
                                               (Prims.of_int (342))
                                               (Prims.of_int (22))
                                               (Prims.of_int (342))
                                               (Prims.of_int (34)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Parametricity.fst"
                                               (Prims.of_int (342))
                                               (Prims.of_int (11))
                                               (Prims.of_int (342))
                                               (Prims.of_int (50)))))
                                      (Obj.magic uu___4)
                                      (fun uu___5 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___6 ->
                                              FStarC_Reflection_V2_Builtins.lookup_typ
                                                uu___5
                                                (FStarC_Reflection_V2_Builtins.explode_qn
                                                   nm))) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Parametricity.fst"
                                                (Prims.of_int (342))
                                                (Prims.of_int (11))
                                                (Prims.of_int (342))
                                                (Prims.of_int (50)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Parametricity.fst"
                                                (Prims.of_int (343))
                                                (Prims.of_int (2))
                                                (Prims.of_int (351))
                                                (Prims.of_int (7)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          (fun se ->
                                             match se with
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_V2_Derived.fail
                                                         "param_letbinding: not found"))
                                             | FStar_Pervasives_Native.Some
                                                 se1 ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (let uu___4 =
                                                         let uu___5 =
                                                           FStar_Tactics_NamedView.inspect_sigelt
                                                             se1 in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (26)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.Parametricity.fst"
                                                                    (Prims.of_int (345))
                                                                    (Prims.of_int (3))
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (43)))))
                                                           (Obj.magic uu___5)
                                                           (fun uu___6 ->
                                                              (fun uu___6 ->
                                                                 match uu___6
                                                                 with
                                                                 | FStar_Tactics_NamedView.Sg_Let
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (param_letbinding
                                                                    se1 fv0
                                                                    fv1))
                                                                 | FStar_Tactics_NamedView.Sg_Inductive
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (param_inductive
                                                                    se1 fv0
                                                                    fv1))
                                                                 | uu___7 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "paramd: unsupported sigelt")))
                                                                uu___6) in
                                                       FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.Parametricity.fst"
                                                                  (Prims.of_int (345))
                                                                  (Prims.of_int (3))
                                                                  (Prims.of_int (348))
                                                                  (Prims.of_int (43)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.Parametricity.fst"
                                                                  (Prims.of_int (344))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (344))
                                                                  (Prims.of_int (11)))))
                                                         (Obj.magic uu___4)
                                                         (fun decls ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___5 ->
                                                                 decls)))))
                                            uu___4))) uu___3))) uu___2)))
           uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.Parametricity.paramd"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Parametricity.paramd (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 paramd)
               FStarC_Syntax_Embeddings.e_string
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Reflection_V2_Embeddings.e_sigelt) psc ncb us args)
let (paramds :
  Prims.string Prims.list ->
    (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nms ->
    let uu___ = FStar_Tactics_Util.map paramd nms in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
               (Prims.of_int (355)) (Prims.of_int (19)) (Prims.of_int (355))
               (Prims.of_int (35)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Parametricity.fst"
               (Prims.of_int (355)) (Prims.of_int (2)) (Prims.of_int (355))
               (Prims.of_int (35))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_List_Tot_Base.flatten uu___1))
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.Parametricity.paramds"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Parametricity.paramds (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 paramds)
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Syntax_Embeddings.e_string)
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Reflection_V2_Embeddings.e_sigelt) psc ncb us args)
type ('a, 'x, 'y) param_of_eqtype = unit
type ('uuuuu, 'uuuuu1) int_param = unit
type ('uuuuu, 'uuuuu1) bool_param = unit
type ('uuuuu, 'uuuuu1) unit_param = unit
type ('uuuuu, 'uuuuu1) string_param = unit