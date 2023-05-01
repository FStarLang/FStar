open Prims
let (term_eq :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  = FStar_Tactics_Builtins.term_eq_old
type atom = Prims.int
type exp =
  | Unit 
  | Mult of exp * exp 
  | Atom of atom 
let (uu___is_Unit : exp -> Prims.bool) =
  fun projectee -> match projectee with | Unit -> true | uu___ -> false
let (uu___is_Mult : exp -> Prims.bool) =
  fun projectee ->
    match projectee with | Mult (_0, _1) -> true | uu___ -> false
let (__proj__Mult__item___0 : exp -> exp) =
  fun projectee -> match projectee with | Mult (_0, _1) -> _0
let (__proj__Mult__item___1 : exp -> exp) =
  fun projectee -> match projectee with | Mult (_0, _1) -> _1
let (uu___is_Atom : exp -> Prims.bool) =
  fun projectee -> match projectee with | Atom _0 -> true | uu___ -> false
let (__proj__Atom__item___0 : exp -> atom) =
  fun projectee -> match projectee with | Atom _0 -> _0
let rec (exp_to_string : exp -> Prims.string) =
  fun e ->
    match e with
    | Unit -> "Unit"
    | Atom x -> Prims.strcat "Atom " (Prims.string_of_int x)
    | Mult (e1, e2) ->
        Prims.strcat "Mult ("
          (Prims.strcat (exp_to_string e1)
             (Prims.strcat ") (" (Prims.strcat (exp_to_string e2) ")")))
type 'a amap = ((atom * 'a) Prims.list * 'a)
let const : 'a . 'a -> 'a amap = fun xa -> ([], xa)
let select : 'a . atom -> 'a amap -> 'a =
  fun x ->
    fun am ->
      match FStar_List_Tot_Base.assoc x (FStar_Pervasives_Native.fst am) with
      | FStar_Pervasives_Native.Some a1 -> a1
      | uu___ -> FStar_Pervasives_Native.snd am
let update : 'a . atom -> 'a -> 'a amap -> 'a amap =
  fun x ->
    fun xa ->
      fun am ->
        (((x, xa) :: (FStar_Pervasives_Native.fst am)),
          (FStar_Pervasives_Native.snd am))
let rec mdenote :
  'a .
    'a FStar_Algebra_CommMonoid_Equiv.equiv ->
      ('a, unit) FStar_Algebra_CommMonoid_Equiv.cm -> 'a amap -> exp -> 'a
  =
  fun eq ->
    fun m ->
      fun am ->
        fun e ->
          match e with
          | Unit ->
              FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__unit eq m
          | Atom x -> select x am
          | Mult (e1, e2) ->
              FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq m
                (mdenote eq m am e1) (mdenote eq m am e2)
let rec xsdenote :
  'a .
    'a FStar_Algebra_CommMonoid_Equiv.equiv ->
      ('a, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
        'a amap -> atom Prims.list -> 'a
  =
  fun eq ->
    fun m ->
      fun am ->
        fun xs ->
          match xs with
          | [] -> FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__unit eq m
          | x::[] -> select x am
          | x::xs' ->
              FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq m
                (select x am) (xsdenote eq m am xs')
let rec (flatten : exp -> atom Prims.list) =
  fun e ->
    match e with
    | Unit -> []
    | Atom x -> [x]
    | Mult (e1, e2) -> FStar_List_Tot_Base.op_At (flatten e1) (flatten e2)
type permute = atom Prims.list -> atom Prims.list
type 'p permute_correct = unit
type 'p permute_via_swaps = unit

let (sort : permute) =
  FStar_List_Tot_Base.sortWith (FStar_List_Tot_Base.compare_of_bool (<))

let (canon : exp -> atom Prims.list) = fun e -> sort (flatten e)
let rec (where_aux :
  Prims.nat ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term Prims.list ->
        (Prims.nat FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun n ->
           fun x ->
             fun xs ->
               match xs with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> FStar_Pervasives_Native.None)))
               | x'::xs' ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range
                              "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                              (Prims.of_int (275)) (Prims.of_int (18))
                              (Prims.of_int (275)) (Prims.of_int (30)))
                           (FStar_Range.mk_range
                              "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                              (Prims.of_int (275)) (Prims.of_int (15))
                              (Prims.of_int (275)) (Prims.of_int (69)))
                           (Obj.magic (term_eq x x'))
                           (fun uu___ ->
                              (fun uu___ ->
                                 if uu___
                                 then
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              FStar_Pervasives_Native.Some n)))
                                 else
                                   Obj.magic
                                     (Obj.repr
                                        (where_aux (n + Prims.int_one) x xs')))
                                uu___)))) uu___2 uu___1 uu___
let (where :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list ->
      (Prims.nat FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  = where_aux Prims.int_zero
let (fatom :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list ->
      FStar_Reflection_Types.term amap ->
        ((exp * FStar_Reflection_Types.term Prims.list *
           FStar_Reflection_Types.term amap),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun ts ->
      fun am ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range
             "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
             (Prims.of_int (279)) (Prims.of_int (8)) (Prims.of_int (279))
             (Prims.of_int (18)))
          (FStar_Range.mk_range
             "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
             (Prims.of_int (279)) (Prims.of_int (2)) (Prims.of_int (284))
             (Prims.of_int (47))) (Obj.magic (where t ts))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | FStar_Pervasives_Native.Some v ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> ((Atom v), ts, am))))
                | FStar_Pervasives_Native.None ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range
                               "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                               (Prims.of_int (282)) (Prims.of_int (17))
                               (Prims.of_int (282)) (Prims.of_int (26)))
                            (FStar_Range.mk_range
                               "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                               (Prims.of_int (283)) (Prims.of_int (4))
                               (Prims.of_int (284)) (Prims.of_int (47)))
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> FStar_List_Tot_Base.length ts))
                            (fun uu___1 ->
                               (fun vfresh ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                          (Prims.of_int (283))
                                          (Prims.of_int (12))
                                          (Prims.of_int (283))
                                          (Prims.of_int (36)))
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                          (Prims.of_int (284))
                                          (Prims.of_int (4))
                                          (Prims.of_int (284))
                                          (Prims.of_int (47)))
                                       (Obj.magic
                                          (FStar_Tactics_Derived.norm_term
                                             [FStar_Pervasives.iota;
                                             FStar_Pervasives.zeta] t))
                                       (fun t1 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___1 ->
                                               ((Atom vfresh),
                                                 (FStar_List_Tot_Base.op_At
                                                    ts [t1]),
                                                 (update vfresh t1 am))))))
                                 uu___1)))) uu___)
let rec (reification_aux :
  FStar_Reflection_Types.term Prims.list ->
    FStar_Reflection_Types.term amap ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            ((exp * FStar_Reflection_Types.term Prims.list *
               FStar_Reflection_Types.term amap),
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ts ->
    fun am ->
      fun mult ->
        fun unit ->
          fun t ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range
                 "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                 (Prims.of_int (289)) (Prims.of_int (15))
                 (Prims.of_int (289)) (Prims.of_int (32)))
              (FStar_Range.mk_range
                 "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                 (Prims.of_int (289)) (Prims.of_int (2)) (Prims.of_int (300))
                 (Prims.of_int (22)))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    FStar_Reflection_Derived_Lemmas.collect_app_ref t))
              (fun uu___ ->
                 (fun uu___ ->
                    match uu___ with
                    | (hd, tl) ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range
                                "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                (Prims.of_int (290)) (Prims.of_int (8))
                                (Prims.of_int (290)) (Prims.of_int (33)))
                             (FStar_Range.mk_range
                                "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                (Prims.of_int (290)) (Prims.of_int (2))
                                (Prims.of_int (300)) (Prims.of_int (22)))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                      (Prims.of_int (290)) (Prims.of_int (8))
                                      (Prims.of_int (290))
                                      (Prims.of_int (18)))
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                      (Prims.of_int (290)) (Prims.of_int (8))
                                      (Prims.of_int (290))
                                      (Prims.of_int (33)))
                                   (Obj.magic
                                      (FStar_Tactics_Builtins.inspect hd))
                                   (fun uu___1 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 ->
                                           (uu___1,
                                             (FStar_List_Tot_Base.list_unref
                                                tl))))))
                             (fun uu___1 ->
                                (fun uu___1 ->
                                   match uu___1 with
                                   | (FStar_Reflection_Data.Tv_FVar fv,
                                      (t1, FStar_Reflection_Data.Q_Explicit)::
                                      (t2, FStar_Reflection_Data.Q_Explicit)::[])
                                       ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                               (Prims.of_int (292))
                                               (Prims.of_int (7))
                                               (Prims.of_int (292))
                                               (Prims.of_int (39)))
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                               (Prims.of_int (292))
                                               (Prims.of_int (4))
                                               (Prims.of_int (296))
                                               (Prims.of_int (22)))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                     (Prims.of_int (292))
                                                     (Prims.of_int (15))
                                                     (Prims.of_int (292))
                                                     (Prims.of_int (34)))
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                     (Prims.of_int (292))
                                                     (Prims.of_int (7))
                                                     (Prims.of_int (292))
                                                     (Prims.of_int (39)))
                                                  (Obj.magic
                                                     (FStar_Tactics_Builtins.pack
                                                        (FStar_Reflection_Data.Tv_FVar
                                                           fv)))
                                                  (fun uu___2 ->
                                                     (fun uu___2 ->
                                                        Obj.magic
                                                          (term_eq uu___2
                                                             mult)) uu___2)))
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  if uu___2
                                                  then
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                            (Prims.of_int (293))
                                                            (Prims.of_int (29))
                                                            (Prims.of_int (293))
                                                            (Prims.of_int (63)))
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                            (Prims.of_int (293))
                                                            (Prims.of_int (9))
                                                            (Prims.of_int (295))
                                                            (Prims.of_int (31)))
                                                         (Obj.magic
                                                            (reification_aux
                                                               ts am mult
                                                               unit t1))
                                                         (fun uu___3 ->
                                                            (fun uu___3 ->
                                                               match uu___3
                                                               with
                                                               | (e1, ts1,
                                                                  am1) ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (63)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (30)))
                                                                    (Obj.magic
                                                                    (reification_aux
                                                                    ts1 am1
                                                                    mult unit
                                                                    t2))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (e2, ts2,
                                                                    am2) ->
                                                                    ((Mult
                                                                    (e1, e2)),
                                                                    ts2, am2)))))
                                                              uu___3))
                                                  else
                                                    Obj.magic (fatom t ts am))
                                                 uu___2))
                                   | (uu___2, uu___3) ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                               (Prims.of_int (298))
                                               (Prims.of_int (7))
                                               (Prims.of_int (298))
                                               (Prims.of_int (21)))
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                               (Prims.of_int (298))
                                               (Prims.of_int (4))
                                               (Prims.of_int (300))
                                               (Prims.of_int (22)))
                                            (Obj.magic (term_eq t unit))
                                            (fun uu___4 ->
                                               (fun uu___4 ->
                                                  if uu___4
                                                  then
                                                    Obj.magic
                                                      (Obj.repr
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___5 ->
                                                               (Unit, ts, am))))
                                                  else
                                                    Obj.magic
                                                      (Obj.repr
                                                         (fatom t ts am)))
                                                 uu___4))) uu___1))) uu___)
let (reification :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term Prims.list ->
        FStar_Reflection_Types.term amap ->
          FStar_Reflection_Types.term ->
            ((exp * FStar_Reflection_Types.term Prims.list *
               FStar_Reflection_Types.term amap),
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun eq ->
    fun m ->
      fun ts ->
        fun am ->
          fun t ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range
                 "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                 (Prims.of_int (304)) (Prims.of_int (13))
                 (Prims.of_int (304)) (Prims.of_int (60)))
              (FStar_Range.mk_range
                 "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                 (Prims.of_int (305)) (Prims.of_int (2)) (Prims.of_int (307))
                 (Prims.of_int (35)))
              (Obj.magic
                 (FStar_Tactics_Derived.norm_term
                    [FStar_Pervasives.iota;
                    FStar_Pervasives.zeta;
                    FStar_Pervasives.delta]
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_App
                          ((FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar";
                                    "Algebra";
                                    "CommMonoid";
                                    "Equiv";
                                    "__proj__CM__item__mult"]))),
                            (m, FStar_Reflection_Data.Q_Explicit))))))
              (fun uu___ ->
                 (fun mult ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range
                            "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                            (Prims.of_int (305)) (Prims.of_int (13))
                            (Prims.of_int (305)) (Prims.of_int (60)))
                         (FStar_Range.mk_range
                            "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                            (Prims.of_int (306)) (Prims.of_int (2))
                            (Prims.of_int (307)) (Prims.of_int (35)))
                         (Obj.magic
                            (FStar_Tactics_Derived.norm_term
                               [FStar_Pervasives.iota;
                               FStar_Pervasives.zeta;
                               FStar_Pervasives.delta]
                               (FStar_Reflection_Builtins.pack_ln
                                  (FStar_Reflection_Data.Tv_App
                                     ((FStar_Reflection_Builtins.pack_ln
                                         (FStar_Reflection_Data.Tv_FVar
                                            (FStar_Reflection_Builtins.pack_fv
                                               ["FStar";
                                               "Algebra";
                                               "CommMonoid";
                                               "Equiv";
                                               "__proj__CM__item__unit"]))),
                                       (m, FStar_Reflection_Data.Q_Explicit))))))
                         (fun uu___ ->
                            (fun unit ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                       (Prims.of_int (306))
                                       (Prims.of_int (13))
                                       (Prims.of_int (306))
                                       (Prims.of_int (37)))
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                       (Prims.of_int (307))
                                       (Prims.of_int (2))
                                       (Prims.of_int (307))
                                       (Prims.of_int (35)))
                                    (Obj.magic
                                       (FStar_Tactics_Derived.norm_term
                                          [FStar_Pervasives.iota;
                                          FStar_Pervasives.zeta] t))
                                    (fun uu___ ->
                                       (fun t1 ->
                                          Obj.magic
                                            (reification_aux ts am mult unit
                                               t1)) uu___))) uu___))) uu___)
let rec (repeat_cong_right_identity :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun eq ->
    fun m ->
      FStar_Tactics_Derived.or_else
        (fun uu___ ->
           FStar_Tactics_Derived.apply_lemma
             (FStar_Reflection_Builtins.pack_ln
                (FStar_Reflection_Data.Tv_FVar
                   (FStar_Reflection_Builtins.pack_fv
                      ["FStar";
                      "Algebra";
                      "CommMonoid";
                      "Equiv";
                      "right_identity"]))))
        (fun uu___ ->
           FStar_Tactics_Effect.tac_bind
             (FStar_Range.mk_range
                "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                (Prims.of_int (311)) (Prims.of_int (20)) (Prims.of_int (311))
                (Prims.of_int (55)))
             (FStar_Range.mk_range
                "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                (Prims.of_int (312)) (Prims.of_int (20)) (Prims.of_int (314))
                (Prims.of_int (51)))
             (Obj.magic
                (FStar_Tactics_Derived.apply_lemma
                   (FStar_Reflection_Builtins.pack_ln
                      (FStar_Reflection_Data.Tv_App
                         ((FStar_Reflection_Builtins.pack_ln
                             (FStar_Reflection_Data.Tv_FVar
                                (FStar_Reflection_Builtins.pack_fv
                                   ["FStar";
                                   "Algebra";
                                   "CommMonoid";
                                   "Equiv";
                                   "__proj__CM__item__congruence"]))),
                           (m, FStar_Reflection_Data.Q_Explicit))))))
             (fun uu___1 ->
                (fun uu___1 ->
                   Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range
                           "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                           (Prims.of_int (312)) (Prims.of_int (20))
                           (Prims.of_int (312)) (Prims.of_int (28)))
                        (FStar_Range.mk_range
                           "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                           (Prims.of_int (313)) (Prims.of_int (20))
                           (Prims.of_int (314)) (Prims.of_int (51)))
                        (Obj.magic (FStar_Tactics_Logic.split ()))
                        (fun uu___2 ->
                           (fun uu___2 ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                      (Prims.of_int (313))
                                      (Prims.of_int (20))
                                      (Prims.of_int (313))
                                      (Prims.of_int (57)))
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                      (Prims.of_int (314))
                                      (Prims.of_int (20))
                                      (Prims.of_int (314))
                                      (Prims.of_int (51)))
                                   (Obj.magic
                                      (FStar_Tactics_Derived.apply_lemma
                                         (FStar_Reflection_Builtins.pack_ln
                                            (FStar_Reflection_Data.Tv_App
                                               ((FStar_Reflection_Builtins.pack_ln
                                                   (FStar_Reflection_Data.Tv_FVar
                                                      (FStar_Reflection_Builtins.pack_fv
                                                         ["FStar";
                                                         "Algebra";
                                                         "CommMonoid";
                                                         "Equiv";
                                                         "__proj__EQ__item__reflexivity"]))),
                                                 (eq,
                                                   FStar_Reflection_Data.Q_Explicit))))))
                                   (fun uu___3 ->
                                      (fun uu___3 ->
                                         Obj.magic
                                           (repeat_cong_right_identity eq m))
                                        uu___3))) uu___2))) uu___1))
let rec (convert_map :
  (atom * FStar_Reflection_Types.term) Prims.list ->
    FStar_Reflection_Types.term)
  =
  fun m ->
    match m with
    | [] ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv ["Prims"; "Nil"]))
    | (a, t)::ps ->
        let a1 =
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_Int a)) in
        let uu___ = convert_map ps in
        let uu___1 = t in
        let uu___2 = a1 in
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_App
             ((FStar_Reflection_Builtins.pack_ln
                 (FStar_Reflection_Data.Tv_App
                    ((FStar_Reflection_Builtins.pack_ln
                        (FStar_Reflection_Data.Tv_FVar
                           (FStar_Reflection_Builtins.pack_fv
                              ["Prims"; "Cons"]))),
                      ((FStar_Reflection_Builtins.pack_ln
                          (FStar_Reflection_Data.Tv_App
                             ((FStar_Reflection_Builtins.pack_ln
                                 (FStar_Reflection_Data.Tv_App
                                    ((FStar_Reflection_Builtins.pack_ln
                                        (FStar_Reflection_Data.Tv_FVar
                                           (FStar_Reflection_Builtins.pack_fv
                                              ["FStar";
                                              "Pervasives";
                                              "Native";
                                              "Mktuple2"]))),
                                      (uu___2,
                                        FStar_Reflection_Data.Q_Explicit)))),
                               (uu___1, FStar_Reflection_Data.Q_Explicit)))),
                        FStar_Reflection_Data.Q_Explicit)))),
               (uu___, FStar_Reflection_Data.Q_Explicit)))
let (convert_am :
  FStar_Reflection_Types.term amap -> FStar_Reflection_Types.term) =
  fun am ->
    let uu___ = am in
    match uu___ with
    | (map, def) ->
        let uu___1 = def in
        let uu___2 = convert_map map in
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_App
             ((FStar_Reflection_Builtins.pack_ln
                 (FStar_Reflection_Data.Tv_App
                    ((FStar_Reflection_Builtins.pack_ln
                        (FStar_Reflection_Data.Tv_FVar
                           (FStar_Reflection_Builtins.pack_fv
                              ["FStar"; "Pervasives"; "Native"; "Mktuple2"]))),
                      (uu___2, FStar_Reflection_Data.Q_Explicit)))),
               (uu___1, FStar_Reflection_Data.Q_Explicit)))
let rec (quote_exp : exp -> FStar_Reflection_Types.term) =
  fun e ->
    match e with
    | Unit ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv
                ["FStar";
                "Tactics";
                "CanonCommMonoidSimple";
                "Equiv";
                "Unit"]))
    | Mult (e1, e2) ->
        let uu___ = quote_exp e2 in
        let uu___1 = quote_exp e1 in
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_App
             ((FStar_Reflection_Builtins.pack_ln
                 (FStar_Reflection_Data.Tv_App
                    ((FStar_Reflection_Builtins.pack_ln
                        (FStar_Reflection_Data.Tv_FVar
                           (FStar_Reflection_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "CanonCommMonoidSimple";
                              "Equiv";
                              "Mult"]))),
                      (uu___1, FStar_Reflection_Data.Q_Explicit)))),
               (uu___, FStar_Reflection_Data.Q_Explicit)))
    | Atom n ->
        let nt =
          FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_Const (FStar_Reflection_Data.C_Int n)) in
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_App
             ((FStar_Reflection_Builtins.pack_ln
                 (FStar_Reflection_Data.Tv_FVar
                    (FStar_Reflection_Builtins.pack_fv
                       ["FStar";
                       "Tactics";
                       "CanonCommMonoidSimple";
                       "Equiv";
                       "Atom"]))), (nt, FStar_Reflection_Data.Q_Explicit)))
let (canon_lhs_rhs :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun eq ->
    fun m ->
      fun lhs ->
        fun rhs ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range
               "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
               (Prims.of_int (341)) (Prims.of_int (15)) (Prims.of_int (341))
               (Prims.of_int (61)))
            (FStar_Range.mk_range
               "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
               (Prims.of_int (342)) (Prims.of_int (2)) (Prims.of_int (370))
               (Prims.of_int (52)))
            (Obj.magic
               (FStar_Tactics_Derived.norm_term
                  [FStar_Pervasives.iota;
                  FStar_Pervasives.zeta;
                  FStar_Pervasives.delta]
                  (FStar_Reflection_Builtins.pack_ln
                     (FStar_Reflection_Data.Tv_App
                        ((FStar_Reflection_Builtins.pack_ln
                            (FStar_Reflection_Data.Tv_FVar
                               (FStar_Reflection_Builtins.pack_fv
                                  ["FStar";
                                  "Algebra";
                                  "CommMonoid";
                                  "Equiv";
                                  "__proj__CM__item__unit"]))),
                          (m, FStar_Reflection_Data.Q_Explicit))))))
            (fun uu___ ->
               (fun m_unit ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range
                          "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                          (Prims.of_int (342)) (Prims.of_int (11))
                          (Prims.of_int (342)) (Prims.of_int (23)))
                       (FStar_Range.mk_range
                          "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                          (Prims.of_int (343)) (Prims.of_int (2))
                          (Prims.of_int (370)) (Prims.of_int (52)))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ -> const m_unit))
                       (fun uu___ ->
                          (fun am ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                     (Prims.of_int (343)) (Prims.of_int (21))
                                     (Prims.of_int (343)) (Prims.of_int (47)))
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                     (Prims.of_int (343)) (Prims.of_int (2))
                                     (Prims.of_int (370)) (Prims.of_int (52)))
                                  (Obj.magic (reification eq m [] am lhs))
                                  (fun uu___ ->
                                     (fun uu___ ->
                                        match uu___ with
                                        | (r1, ts, am1) ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                    (Prims.of_int (344))
                                                    (Prims.of_int (21))
                                                    (Prims.of_int (344))
                                                    (Prims.of_int (47)))
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                    (Prims.of_int (344))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (370))
                                                    (Prims.of_int (52)))
                                                 (Obj.magic
                                                    (reification eq m ts am1
                                                       rhs))
                                                 (fun uu___1 ->
                                                    (fun uu___1 ->
                                                       match uu___1 with
                                                       | (r2, uu___2, am2) ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                   (Prims.of_int (351))
                                                                   (Prims.of_int (11))
                                                                   (Prims.of_int (351))
                                                                   (Prims.of_int (24)))
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                   (Prims.of_int (352))
                                                                   (Prims.of_int (2))
                                                                   (Prims.of_int (370))
                                                                   (Prims.of_int (52)))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    convert_am
                                                                    am2))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun am3
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (23)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (52)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    quote_exp
                                                                    r1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun r11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (23)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (52)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    quote_exp
                                                                    r2))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun r21
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (51)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (52)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.change_sq
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Algebra";
                                                                    "CommMonoid";
                                                                    "Equiv";
                                                                    "__proj__EQ__item__eq"]))),
                                                                    (eq,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoidSimple";
                                                                    "Equiv";
                                                                    "mdenote"]))),
                                                                    (eq,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (m,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (am3,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (r11,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoidSimple";
                                                                    "Equiv";
                                                                    "mdenote"]))),
                                                                    (eq,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (m,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (am3,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    (r21,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    FStar_Reflection_Data.Q_Explicit))))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (25)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (52)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.apply
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoidSimple";
                                                                    "Equiv";
                                                                    "monoid_reflect"])))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (18)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (52)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.norm
                                                                    [FStar_Pervasives.iota;
                                                                    FStar_Pervasives.zeta;
                                                                    FStar_Pervasives.delta_only
                                                                    ["FStar.Tactics.CanonCommMonoidSimple.Equiv.canon";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.xsdenote";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.flatten";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.sort";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.select";
                                                                    "FStar.List.Tot.Base.assoc";
                                                                    "FStar.Pervasives.Native.fst";
                                                                    "FStar.Pervasives.Native.__proj__Mktuple2__item___1";
                                                                    "FStar.List.Tot.Base.op_At";
                                                                    "FStar.List.Tot.Base.append";
                                                                    "FStar.List.Tot.Base.sortWith";
                                                                    "FStar.List.Tot.Base.partition";
                                                                    "FStar.List.Tot.Base.bool_of_compare";
                                                                    "FStar.List.Tot.Base.compare_of_bool"];
                                                                    FStar_Pervasives.primops]))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Derived.or_else
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Derived.apply_lemma
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Algebra";
                                                                    "CommMonoid";
                                                                    "Equiv";
                                                                    "__proj__EQ__item__reflexivity"]))),
                                                                    (eq,
                                                                    FStar_Reflection_Data.Q_Explicit)))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    repeat_cong_right_identity
                                                                    eq m)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                      uu___1))) uu___)))
                            uu___))) uu___)
let (canon_monoid :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun eq ->
    fun m ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
           (Prims.of_int (374)) (Prims.of_int (2)) (Prims.of_int (374))
           (Prims.of_int (19)))
        (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
           (Prims.of_int (375)) (Prims.of_int (2)) (Prims.of_int (392))
           (Prims.of_int (68)))
        (Obj.magic
           (FStar_Tactics_Builtins.norm
              [FStar_Pervasives.iota; FStar_Pervasives.zeta]))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range
                      "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                      (Prims.of_int (375)) (Prims.of_int (10))
                      (Prims.of_int (375)) (Prims.of_int (21)))
                   (FStar_Range.mk_range
                      "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                      (Prims.of_int (377)) (Prims.of_int (2))
                      (Prims.of_int (392)) (Prims.of_int (68)))
                   (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
                   (fun uu___1 ->
                      (fun t ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                 (Prims.of_int (377)) (Prims.of_int (19))
                                 (Prims.of_int (377)) (Prims.of_int (36)))
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                 (Prims.of_int (377)) (Prims.of_int (2))
                                 (Prims.of_int (392)) (Prims.of_int (68)))
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 ->
                                    FStar_Reflection_Derived_Lemmas.collect_app_ref
                                      t))
                              (fun uu___1 ->
                                 (fun uu___1 ->
                                    match uu___1 with
                                    | (sq, rel_xy) ->
                                        (match rel_xy with
                                         | (rel_xy1, uu___2)::[] ->
                                             Obj.magic
                                               (Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                        (Prims.of_int (381))
                                                        (Prims.of_int (21))
                                                        (Prims.of_int (381))
                                                        (Prims.of_int (43)))
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                        (Prims.of_int (380))
                                                        (Prims.of_int (21))
                                                        (Prims.of_int (391))
                                                        (Prims.of_int (6)))
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___3 ->
                                                           FStar_Reflection_Derived_Lemmas.collect_app_ref
                                                             rel_xy1))
                                                     (fun uu___3 ->
                                                        (fun uu___3 ->
                                                           match uu___3 with
                                                           | (rel, xy) ->
                                                               if
                                                                 (FStar_List_Tot_Base.length
                                                                    xy)
                                                                   >=
                                                                   (Prims.of_int (2))
                                                               then
                                                                 Obj.magic
                                                                   (Obj.repr
                                                                    (match 
                                                                    ((FStar_List_Tot_Base.index
                                                                    xy
                                                                    ((FStar_List_Tot_Base.length
                                                                    xy) -
                                                                    (Prims.of_int (2)))),
                                                                    (FStar_List_Tot_Base.index
                                                                    xy
                                                                    ((FStar_List_Tot_Base.length
                                                                    xy) -
                                                                    Prims.int_one)))
                                                                    with
                                                                    | 
                                                                    ((lhs,
                                                                    FStar_Reflection_Data.Q_Explicit),
                                                                    (rhs,
                                                                    FStar_Reflection_Data.Q_Explicit))
                                                                    ->
                                                                    Obj.repr
                                                                    (canon_lhs_rhs
                                                                    eq m lhs
                                                                    rhs)
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Goal should have been an application of a binary relation to 2 explicit arguments")))
                                                               else
                                                                 Obj.magic
                                                                   (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Goal should have been an application of a binary relation to n implicit and 2 explicit arguments")))
                                                          uu___3)))
                                         | uu___2 ->
                                             Obj.magic
                                               (Obj.repr
                                                  (FStar_Tactics_Derived.fail
                                                     "Goal should be squash applied to a binary relation"))))
                                   uu___1))) uu___1))) uu___)
let _ =
  FStar_Tactics_Native.register_tactic
    "FStar.Tactics.CanonCommMonoidSimple.Equiv.canon_monoid"
    (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_InterpFuns.mk_tactic_interpretation_2
             (FStar_Tactics_Native.from_tactic_2 canon_monoid)
             FStar_Reflection_Embeddings.e_term
             FStar_Reflection_Embeddings.e_term
             FStar_Syntax_Embeddings.e_unit psc ncb args)
