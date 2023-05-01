open Prims
let (term_eq :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  = FStar_Tactics_Builtins.term_eq_old
let (dump : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun m ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoidSimple.fst"
         (Prims.of_int (36)) (Prims.of_int (16)) (Prims.of_int (36))
         (Prims.of_int (28)))
      (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoidSimple.fst"
         (Prims.of_int (36)) (Prims.of_int (13)) (Prims.of_int (36))
         (Prims.of_int (40)))
      (Obj.magic (FStar_Tactics_Builtins.debugging ()))
      (fun uu___ ->
         (fun uu___ ->
            if uu___
            then Obj.magic (Obj.repr (FStar_Tactics_Builtins.dump m))
            else
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))))
           uu___)
type atom = Prims.nat
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
let rec mdenote : 'a . 'a FStar_Algebra_CommMonoid.cm -> 'a amap -> exp -> 'a
  =
  fun m ->
    fun am ->
      fun e ->
        match e with
        | Unit -> FStar_Algebra_CommMonoid.__proj__CM__item__unit m
        | Atom x -> select x am
        | Mult (e1, e2) ->
            FStar_Algebra_CommMonoid.__proj__CM__item__mult m
              (mdenote m am e1) (mdenote m am e2)
let rec xsdenote :
  'a . 'a FStar_Algebra_CommMonoid.cm -> 'a amap -> atom Prims.list -> 'a =
  fun m ->
    fun am ->
      fun xs ->
        match xs with
        | [] -> FStar_Algebra_CommMonoid.__proj__CM__item__unit m
        | x::[] -> select x am
        | x::xs' ->
            FStar_Algebra_CommMonoid.__proj__CM__item__mult m (select x am)
              (xsdenote m am xs')
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
                              "FStar.Tactics.CanonCommMonoidSimple.fst"
                              (Prims.of_int (217)) (Prims.of_int (18))
                              (Prims.of_int (217)) (Prims.of_int (30)))
                           (FStar_Range.mk_range
                              "FStar.Tactics.CanonCommMonoidSimple.fst"
                              (Prims.of_int (217)) (Prims.of_int (15))
                              (Prims.of_int (217)) (Prims.of_int (69)))
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
let rec reification_aux :
  'a .
    FStar_Reflection_Types.term Prims.list ->
      'a amap ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              ((exp * FStar_Reflection_Types.term Prims.list * 'a amap),
                unit) FStar_Tactics_Effect.tac_repr
  =
  fun ts ->
    fun am ->
      fun mult ->
        fun unit ->
          fun t ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoidSimple.fst"
                 (Prims.of_int (223)) (Prims.of_int (15))
                 (Prims.of_int (223)) (Prims.of_int (32)))
              (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoidSimple.fst"
                 (Prims.of_int (223)) (Prims.of_int (2)) (Prims.of_int (240))
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
                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                (Prims.of_int (225)) (Prims.of_int (4))
                                (Prims.of_int (228)) (Prims.of_int (57)))
                             (FStar_Range.mk_range
                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                (Prims.of_int (230)) (Prims.of_int (2))
                                (Prims.of_int (240)) (Prims.of_int (22)))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 ->
                                   fun t1 ->
                                     fun ts1 ->
                                       fun am1 ->
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.CanonCommMonoidSimple.fst"
                                              (Prims.of_int (225))
                                              (Prims.of_int (10))
                                              (Prims.of_int (225))
                                              (Prims.of_int (20)))
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.CanonCommMonoidSimple.fst"
                                              (Prims.of_int (225))
                                              (Prims.of_int (4))
                                              (Prims.of_int (228))
                                              (Prims.of_int (57)))
                                           (Obj.magic (where t1 ts1))
                                           (fun uu___2 ->
                                              (fun uu___2 ->
                                                 match uu___2 with
                                                 | FStar_Pervasives_Native.Some
                                                     v ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___3 ->
                                                                ((Atom v),
                                                                  ts1, am1))))
                                                 | FStar_Pervasives_Native.None
                                                     ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                (Prims.of_int (227))
                                                                (Prims.of_int (27))
                                                                (Prims.of_int (227))
                                                                (Prims.of_int (36)))
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                (Prims.of_int (227))
                                                                (Prims.of_int (40))
                                                                (Prims.of_int (228))
                                                                (Prims.of_int (57)))
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___3
                                                                   ->
                                                                   FStar_List_Tot_Base.length
                                                                    ts1))
                                                             (fun uu___3 ->
                                                                (fun vfresh
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (57)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (57)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.unquote
                                                                    t1))
                                                                    (fun z ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ((Atom
                                                                    vfresh),
                                                                    (FStar_List_Tot_Base.op_At
                                                                    ts1 
                                                                    [t1]),
                                                                    (update
                                                                    vfresh z
                                                                    am1))))))
                                                                  uu___3))))
                                                uu___2)))
                             (fun uu___1 ->
                                (fun fatom ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.CanonCommMonoidSimple.fst"
                                           (Prims.of_int (230))
                                           (Prims.of_int (8))
                                           (Prims.of_int (230))
                                           (Prims.of_int (33)))
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.CanonCommMonoidSimple.fst"
                                           (Prims.of_int (230))
                                           (Prims.of_int (2))
                                           (Prims.of_int (240))
                                           (Prims.of_int (22)))
                                        (Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                 (Prims.of_int (230))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (230))
                                                 (Prims.of_int (18)))
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                 (Prims.of_int (230))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (230))
                                                 (Prims.of_int (33)))
                                              (Obj.magic
                                                 (FStar_Tactics_Builtins.inspect
                                                    hd))
                                              (fun uu___1 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___2 ->
                                                      (uu___1,
                                                        (FStar_List_Tot_Base.list_unref
                                                           tl))))))
                                        (fun uu___1 ->
                                           (fun uu___1 ->
                                              match uu___1 with
                                              | (FStar_Reflection_Data.Tv_FVar
                                                 fv,
                                                 (t1,
                                                  FStar_Reflection_Data.Q_Explicit)::
                                                 (t2,
                                                  FStar_Reflection_Data.Q_Explicit)::[])
                                                  ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                          (Prims.of_int (232))
                                                          (Prims.of_int (7))
                                                          (Prims.of_int (232))
                                                          (Prims.of_int (39)))
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                          (Prims.of_int (232))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (236))
                                                          (Prims.of_int (22)))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                (Prims.of_int (232))
                                                                (Prims.of_int (15))
                                                                (Prims.of_int (232))
                                                                (Prims.of_int (34)))
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                (Prims.of_int (232))
                                                                (Prims.of_int (7))
                                                                (Prims.of_int (232))
                                                                (Prims.of_int (39)))
                                                             (Obj.magic
                                                                (FStar_Tactics_Builtins.pack
                                                                   (FStar_Reflection_Data.Tv_FVar
                                                                    fv)))
                                                             (fun uu___2 ->
                                                                (fun uu___2
                                                                   ->
                                                                   Obj.magic
                                                                    (term_eq
                                                                    uu___2
                                                                    mult))
                                                                  uu___2)))
                                                       (fun uu___2 ->
                                                          (fun uu___2 ->
                                                             if uu___2
                                                             then
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (61)))
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (31)))
                                                                    (
                                                                    Obj.magic
                                                                    (reification_aux
                                                                    ts am
                                                                    mult unit
                                                                    t1))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (e1, ts1,
                                                                    am1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (61)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (235))
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
                                                               Obj.magic
                                                                 (fatom t ts
                                                                    am))
                                                            uu___2))
                                              | (uu___2, uu___3) ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                          (Prims.of_int (238))
                                                          (Prims.of_int (7))
                                                          (Prims.of_int (238))
                                                          (Prims.of_int (21)))
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                          (Prims.of_int (238))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (240))
                                                          (Prims.of_int (22)))
                                                       (Obj.magic
                                                          (term_eq t unit))
                                                       (fun uu___4 ->
                                                          (fun uu___4 ->
                                                             if uu___4
                                                             then
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    (Unit,
                                                                    ts, am))))
                                                             else
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    fatom t
                                                                    ts am)))
                                                            uu___4))) uu___1)))
                                  uu___1))) uu___)
let reification :
  'a .
    'a FStar_Algebra_CommMonoid.cm ->
      FStar_Reflection_Types.term Prims.list ->
        'a amap ->
          FStar_Reflection_Types.term ->
            ((exp * FStar_Reflection_Types.term Prims.list * 'a amap), 
              unit) FStar_Tactics_Effect.tac_repr
  =
  fun m ->
    fun ts ->
      fun am ->
        fun t ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoidSimple.fst"
               (Prims.of_int (244)) (Prims.of_int (13)) (Prims.of_int (244))
               (Prims.of_int (61)))
            (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoidSimple.fst"
               (Prims.of_int (245)) (Prims.of_int (2)) (Prims.of_int (247))
               (Prims.of_int (35)))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range
                     "FStar.Tactics.CanonCommMonoidSimple.fst"
                     (Prims.of_int (244)) (Prims.of_int (41))
                     (Prims.of_int (244)) (Prims.of_int (61)))
                  (FStar_Range.mk_range
                     "FStar.Tactics.CanonCommMonoidSimple.fst"
                     (Prims.of_int (244)) (Prims.of_int (13))
                     (Prims.of_int (244)) (Prims.of_int (61)))
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic
                             (failwith
                                "Cannot evaluate open quotation at runtime"))
                          uu___))
                  (fun uu___ ->
                     (fun uu___ ->
                        Obj.magic
                          (FStar_Tactics_Derived.norm_term
                             [FStar_Pervasives.delta;
                             FStar_Pervasives.zeta;
                             FStar_Pervasives.iota] uu___)) uu___)))
            (fun uu___ ->
               (fun mult ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range
                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                          (Prims.of_int (245)) (Prims.of_int (13))
                          (Prims.of_int (245)) (Prims.of_int (61)))
                       (FStar_Range.mk_range
                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                          (Prims.of_int (246)) (Prims.of_int (2))
                          (Prims.of_int (247)) (Prims.of_int (35)))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range
                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                (Prims.of_int (245)) (Prims.of_int (41))
                                (Prims.of_int (245)) (Prims.of_int (61)))
                             (FStar_Range.mk_range
                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                (Prims.of_int (245)) (Prims.of_int (13))
                                (Prims.of_int (245)) (Prims.of_int (61)))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ ->
                                   (fun uu___ ->
                                      Obj.magic
                                        (failwith
                                           "Cannot evaluate open quotation at runtime"))
                                     uu___))
                             (fun uu___ ->
                                (fun uu___ ->
                                   Obj.magic
                                     (FStar_Tactics_Derived.norm_term
                                        [FStar_Pervasives.delta;
                                        FStar_Pervasives.zeta;
                                        FStar_Pervasives.iota] uu___)) uu___)))
                       (fun uu___ ->
                          (fun unit ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.CanonCommMonoidSimple.fst"
                                     (Prims.of_int (246)) (Prims.of_int (13))
                                     (Prims.of_int (246)) (Prims.of_int (42)))
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.CanonCommMonoidSimple.fst"
                                     (Prims.of_int (247)) (Prims.of_int (2))
                                     (Prims.of_int (247)) (Prims.of_int (35)))
                                  (Obj.magic
                                     (FStar_Tactics_Derived.norm_term
                                        [FStar_Pervasives.delta;
                                        FStar_Pervasives.zeta;
                                        FStar_Pervasives.iota] t))
                                  (fun uu___ ->
                                     (fun t1 ->
                                        Obj.magic
                                          (reification_aux ts am mult unit t1))
                                       uu___))) uu___))) uu___)
let canon_monoid :
  'a .
    'a FStar_Algebra_CommMonoid.cm ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun m ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoidSimple.fst"
         (Prims.of_int (250)) (Prims.of_int (2)) (Prims.of_int (250))
         (Prims.of_int (9)))
      (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoidSimple.fst"
         (Prims.of_int (251)) (Prims.of_int (2)) (Prims.of_int (274))
         (Prims.of_int (42))) (Obj.magic (FStar_Tactics_Builtins.norm []))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range
                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                    (Prims.of_int (251)) (Prims.of_int (8))
                    (Prims.of_int (251)) (Prims.of_int (37)))
                 (FStar_Range.mk_range
                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                    (Prims.of_int (251)) (Prims.of_int (2))
                    (Prims.of_int (274)) (Prims.of_int (42)))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range
                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                          (Prims.of_int (251)) (Prims.of_int (24))
                          (Prims.of_int (251)) (Prims.of_int (37)))
                       (FStar_Range.mk_range
                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                          (Prims.of_int (251)) (Prims.of_int (8))
                          (Prims.of_int (251)) (Prims.of_int (37)))
                       (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
                       (fun uu___1 ->
                          (fun uu___1 ->
                             Obj.magic
                               (FStar_Reflection_Formula.term_as_formula
                                  uu___1)) uu___1)))
                 (fun uu___1 ->
                    (fun uu___1 ->
                       match uu___1 with
                       | FStar_Reflection_Formula.Comp
                           (FStar_Reflection_Formula.Eq
                            (FStar_Pervasives_Native.Some t), t1, t2)
                           ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommMonoidSimple.fst"
                                      (Prims.of_int (255)) (Prims.of_int (9))
                                      (Prims.of_int (255))
                                      (Prims.of_int (28)))
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommMonoidSimple.fst"
                                      (Prims.of_int (255)) (Prims.of_int (6))
                                      (Prims.of_int (273))
                                      (Prims.of_int (69)))
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.CanonCommMonoidSimple.fst"
                                            (Prims.of_int (255))
                                            (Prims.of_int (19))
                                            (Prims.of_int (255))
                                            (Prims.of_int (28)))
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.CanonCommMonoidSimple.fst"
                                            (Prims.of_int (255))
                                            (Prims.of_int (9))
                                            (Prims.of_int (255))
                                            (Prims.of_int (28)))
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  Obj.magic
                                                    (failwith
                                                       "Cannot evaluate open quotation at runtime"))
                                                 uu___2))
                                         (fun uu___2 ->
                                            (fun uu___2 ->
                                               Obj.magic (term_eq t uu___2))
                                              uu___2)))
                                   (fun uu___2 ->
                                      (fun uu___2 ->
                                         if uu___2
                                         then
                                           Obj.magic
                                             (Obj.repr
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                      (Prims.of_int (256))
                                                      (Prims.of_int (27))
                                                      (Prims.of_int (256))
                                                      (Prims.of_int (67)))
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                      (Prims.of_int (256))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (271))
                                                      (Prims.of_int (22)))
                                                   (Obj.magic
                                                      (reification m []
                                                         (const
                                                            (FStar_Algebra_CommMonoid.__proj__CM__item__unit
                                                               m)) t1))
                                                   (fun uu___3 ->
                                                      (fun uu___3 ->
                                                         match uu___3 with
                                                         | (r1, ts, am) ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (48)))
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (22)))
                                                                  (Obj.magic
                                                                    (reification
                                                                    m ts am
                                                                    t2))
                                                                  (fun uu___4
                                                                    ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (r2,
                                                                    uu___5,
                                                                    am1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (50)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (22)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (50)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (50)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (49)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (49)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (49)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))
                                                                    uu___6))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    uu___6))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    "am ="
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (dump
                                                                    uu___6))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (62)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (22)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (62)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (62)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))
                                                                    uu___7))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Derived.change_sq
                                                                    uu___7))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (31)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (22)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.apply
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoidSimple";
                                                                    "monoid_reflect"])))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.norm
                                                                    [
                                                                    FStar_Pervasives.delta_only
                                                                    ["FStar.Tactics.CanonCommMonoidSimple.canon";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.xsdenote";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.flatten";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.sort";
                                                                    "FStar.Tactics.CanonCommMonoidSimple.select";
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
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___4)))
                                                        uu___3)))
                                         else
                                           Obj.magic
                                             (Obj.repr
                                                (FStar_Tactics_Derived.fail
                                                   "Goal should be an equality at the right monoid type")))
                                        uu___2)))
                       | uu___2 ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Derived.fail
                                   "Goal should be an equality"))) uu___1)))
           uu___)
