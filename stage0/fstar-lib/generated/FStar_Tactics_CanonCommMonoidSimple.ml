open Prims
let (term_eq :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  = FStarC_Tactics_V2_Builtins.term_eq_old
let (dump : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun m ->
    let uu___ = FStarC_Tactics_V2_Builtins.debugging () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoidSimple.fst"
               (Prims.of_int (36)) (Prims.of_int (16)) (Prims.of_int (36))
               (Prims.of_int (28)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoidSimple.fst"
               (Prims.of_int (36)) (Prims.of_int (13)) (Prims.of_int (36))
               (Prims.of_int (40))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            if uu___1
            then Obj.magic (Obj.repr (FStarC_Tactics_V2_Builtins.dump m))
            else
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))))
           uu___1)
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
    FStar_Tactics_NamedView.term ->
      FStar_Tactics_NamedView.term Prims.list ->
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
                        (let uu___ = term_eq x x' in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                    (Prims.of_int (217)) (Prims.of_int (18))
                                    (Prims.of_int (217)) (Prims.of_int (30)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                    (Prims.of_int (217)) (Prims.of_int (15))
                                    (Prims.of_int (217)) (Prims.of_int (69)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 if uu___1
                                 then
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              FStar_Pervasives_Native.Some n)))
                                 else
                                   Obj.magic
                                     (Obj.repr
                                        (where_aux (n + Prims.int_one) x xs')))
                                uu___1)))) uu___2 uu___1 uu___
let (where :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term Prims.list ->
      (Prims.nat FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  = where_aux Prims.int_zero
let rec reification_aux :
  'a .
    FStar_Tactics_NamedView.term Prims.list ->
      'a amap ->
        FStar_Tactics_NamedView.term ->
          FStar_Tactics_NamedView.term ->
            FStar_Tactics_NamedView.term ->
              ((exp * FStar_Tactics_NamedView.term Prims.list * 'a amap),
                unit) FStar_Tactics_Effect.tac_repr
  =
  fun ts ->
    fun am ->
      fun mult ->
        fun unit ->
          fun t ->
            let uu___ =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      FStar_Reflection_V2_Derived_Lemmas.collect_app_ref t)) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.Tactics.CanonCommMonoidSimple.fst"
                       (Prims.of_int (223)) (Prims.of_int (15))
                       (Prims.of_int (223)) (Prims.of_int (32)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.Tactics.CanonCommMonoidSimple.fst"
                       (Prims.of_int (222)) (Prims.of_int (79))
                       (Prims.of_int (240)) (Prims.of_int (22)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun uu___1 ->
                    match uu___1 with
                    | (hd, tl) ->
                        let uu___2 =
                          Obj.magic
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 ->
                                  fun t1 ->
                                    fun ts1 ->
                                      fun am1 ->
                                        let uu___4 = where t1 ts1 in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                   (Prims.of_int (225))
                                                   (Prims.of_int (10))
                                                   (Prims.of_int (225))
                                                   (Prims.of_int (20)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                   (Prims.of_int (225))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (228))
                                                   (Prims.of_int (57)))))
                                          (Obj.magic uu___4)
                                          (fun uu___5 ->
                                             (fun uu___5 ->
                                                match uu___5 with
                                                | FStar_Pervasives_Native.Some
                                                    v ->
                                                    Obj.magic
                                                      (Obj.repr
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___6 ->
                                                               ((Atom v),
                                                                 ts1, am1))))
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    Obj.magic
                                                      (Obj.repr
                                                         (let uu___6 =
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___7
                                                                    ->
                                                                    FStar_List_Tot_Base.length
                                                                    ts1)) in
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (36)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (57)))))
                                                            (Obj.magic uu___6)
                                                            (fun uu___7 ->
                                                               (fun vfresh ->
                                                                  let uu___7
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.unquote
                                                                    t1 in
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun z ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    ((Atom
                                                                    vfresh),
                                                                    (FStar_List_Tot_Base.op_At
                                                                    ts1 
                                                                    [t1]),
                                                                    (update
                                                                    vfresh z
                                                                    am1))))))
                                                                 uu___7))))
                                               uu___5))) in
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommMonoidSimple.fst"
                                      (Prims.of_int (225)) (Prims.of_int (4))
                                      (Prims.of_int (228))
                                      (Prims.of_int (57)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommMonoidSimple.fst"
                                      (Prims.of_int (230)) (Prims.of_int (2))
                                      (Prims.of_int (240))
                                      (Prims.of_int (22)))))
                             (Obj.magic uu___2)
                             (fun uu___3 ->
                                (fun fatom ->
                                   let uu___3 =
                                     let uu___4 =
                                       FStar_Tactics_NamedView.inspect hd in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                (Prims.of_int (230))
                                                (Prims.of_int (8))
                                                (Prims.of_int (230))
                                                (Prims.of_int (18)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                (Prims.of_int (230))
                                                (Prims.of_int (8))
                                                (Prims.of_int (230))
                                                (Prims.of_int (33)))))
                                       (Obj.magic uu___4)
                                       (fun uu___5 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___6 ->
                                               (uu___5,
                                                 (FStar_List_Tot_Base.list_unref
                                                    tl)))) in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                 (Prims.of_int (230))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (230))
                                                 (Prims.of_int (33)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                 (Prims.of_int (230))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (240))
                                                 (Prims.of_int (22)))))
                                        (Obj.magic uu___3)
                                        (fun uu___4 ->
                                           (fun uu___4 ->
                                              match uu___4 with
                                              | (FStar_Tactics_NamedView.Tv_FVar
                                                 fv,
                                                 (t1,
                                                  FStarC_Reflection_V2_Data.Q_Explicit)::
                                                 (t2,
                                                  FStarC_Reflection_V2_Data.Q_Explicit)::[])
                                                  ->
                                                  let uu___5 =
                                                    term_eq
                                                      (FStar_Tactics_NamedView.pack
                                                         (FStar_Tactics_NamedView.Tv_FVar
                                                            fv)) mult in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                (Prims.of_int (232))
                                                                (Prims.of_int (7))
                                                                (Prims.of_int (232))
                                                                (Prims.of_int (39)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                (Prims.of_int (232))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (236))
                                                                (Prims.of_int (22)))))
                                                       (Obj.magic uu___5)
                                                       (fun uu___6 ->
                                                          (fun uu___6 ->
                                                             if uu___6
                                                             then
                                                               let uu___7 =
                                                                 reification_aux
                                                                   ts am mult
                                                                   unit t1 in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (61)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (31)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___7)
                                                                    (
                                                                    fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (e1, ts1,
                                                                    am1) ->
                                                                    let uu___9
                                                                    =
                                                                    reification_aux
                                                                    ts1 am1
                                                                    mult unit
                                                                    t2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    (e2, ts2,
                                                                    am2) ->
                                                                    ((Mult
                                                                    (e1, e2)),
                                                                    ts2, am2)))))
                                                                    uu___8))
                                                             else
                                                               Obj.magic
                                                                 (fatom t ts
                                                                    am))
                                                            uu___6))
                                              | (uu___5, uu___6) ->
                                                  let uu___7 = term_eq t unit in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                (Prims.of_int (238))
                                                                (Prims.of_int (7))
                                                                (Prims.of_int (238))
                                                                (Prims.of_int (21)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                (Prims.of_int (238))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (240))
                                                                (Prims.of_int (22)))))
                                                       (Obj.magic uu___7)
                                                       (fun uu___8 ->
                                                          (fun uu___8 ->
                                                             if uu___8
                                                             then
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    (Unit,
                                                                    ts, am))))
                                                             else
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    fatom t
                                                                    ts am)))
                                                            uu___8))) uu___4)))
                                  uu___3))) uu___1)
let reification :
  'a .
    'a FStar_Algebra_CommMonoid.cm ->
      FStar_Tactics_NamedView.term Prims.list ->
        'a amap ->
          FStar_Tactics_NamedView.term ->
            ((exp * FStar_Tactics_NamedView.term Prims.list * 'a amap), 
              unit) FStar_Tactics_Effect.tac_repr
  =
  fun m ->
    fun ts ->
      fun am ->
        fun t ->
          let uu___ =
            let uu___1 =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      (fun uu___2 ->
                         Obj.magic
                           (failwith
                              "Cannot evaluate open quotation at runtime"))
                        uu___2)) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.Tactics.CanonCommMonoidSimple.fst"
                       (Prims.of_int (244)) (Prims.of_int (41))
                       (Prims.of_int (244)) (Prims.of_int (61)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.Tactics.CanonCommMonoidSimple.fst"
                       (Prims.of_int (244)) (Prims.of_int (13))
                       (Prims.of_int (244)) (Prims.of_int (61)))))
              (Obj.magic uu___1)
              (fun uu___2 ->
                 (fun uu___2 ->
                    Obj.magic
                      (FStar_Tactics_V2_Derived.norm_term
                         [FStar_Pervasives.delta;
                         FStar_Pervasives.zeta;
                         FStar_Pervasives.iota] uu___2)) uu___2) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.Tactics.CanonCommMonoidSimple.fst"
                     (Prims.of_int (244)) (Prims.of_int (13))
                     (Prims.of_int (244)) (Prims.of_int (61)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.Tactics.CanonCommMonoidSimple.fst"
                     (Prims.of_int (244)) (Prims.of_int (64))
                     (Prims.of_int (247)) (Prims.of_int (35)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun mult ->
                  let uu___1 =
                    let uu___2 =
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___3 ->
                              (fun uu___3 ->
                                 Obj.magic
                                   (failwith
                                      "Cannot evaluate open quotation at runtime"))
                                uu___3)) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.CanonCommMonoidSimple.fst"
                               (Prims.of_int (245)) (Prims.of_int (41))
                               (Prims.of_int (245)) (Prims.of_int (61)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.CanonCommMonoidSimple.fst"
                               (Prims.of_int (245)) (Prims.of_int (13))
                               (Prims.of_int (245)) (Prims.of_int (61)))))
                      (Obj.magic uu___2)
                      (fun uu___3 ->
                         (fun uu___3 ->
                            Obj.magic
                              (FStar_Tactics_V2_Derived.norm_term
                                 [FStar_Pervasives.delta;
                                 FStar_Pervasives.zeta;
                                 FStar_Pervasives.iota] uu___3)) uu___3) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                (Prims.of_int (245)) (Prims.of_int (13))
                                (Prims.of_int (245)) (Prims.of_int (61)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.CanonCommMonoidSimple.fst"
                                (Prims.of_int (245)) (Prims.of_int (64))
                                (Prims.of_int (247)) (Prims.of_int (35)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun unit ->
                             let uu___2 =
                               FStar_Tactics_V2_Derived.norm_term
                                 [FStar_Pervasives.delta;
                                 FStar_Pervasives.zeta;
                                 FStar_Pervasives.iota] t in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.CanonCommMonoidSimple.fst"
                                           (Prims.of_int (246))
                                           (Prims.of_int (13))
                                           (Prims.of_int (246))
                                           (Prims.of_int (42)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.CanonCommMonoidSimple.fst"
                                           (Prims.of_int (247))
                                           (Prims.of_int (2))
                                           (Prims.of_int (247))
                                           (Prims.of_int (35)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     (fun t1 ->
                                        Obj.magic
                                          (reification_aux ts am mult unit t1))
                                       uu___3))) uu___2))) uu___1)
let canon_monoid :
  'a .
    'a FStar_Algebra_CommMonoid.cm ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun m ->
    let uu___ = FStarC_Tactics_V2_Builtins.norm [] in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoidSimple.fst"
               (Prims.of_int (250)) (Prims.of_int (2)) (Prims.of_int (250))
               (Prims.of_int (9)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoidSimple.fst"
               (Prims.of_int (251)) (Prims.of_int (2)) (Prims.of_int (274))
               (Prims.of_int (42))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            let uu___2 =
              let uu___3 = FStar_Tactics_V2_Derived.cur_goal () in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "FStar.Tactics.CanonCommMonoidSimple.fst"
                         (Prims.of_int (251)) (Prims.of_int (24))
                         (Prims.of_int (251)) (Prims.of_int (37)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "FStar.Tactics.CanonCommMonoidSimple.fst"
                         (Prims.of_int (251)) (Prims.of_int (8))
                         (Prims.of_int (251)) (Prims.of_int (37)))))
                (Obj.magic uu___3)
                (fun uu___4 ->
                   (fun uu___4 ->
                      Obj.magic
                        (FStar_Reflection_V2_Formula.term_as_formula uu___4))
                     uu___4) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                          (Prims.of_int (251)) (Prims.of_int (8))
                          (Prims.of_int (251)) (Prims.of_int (37)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.Tactics.CanonCommMonoidSimple.fst"
                          (Prims.of_int (251)) (Prims.of_int (2))
                          (Prims.of_int (274)) (Prims.of_int (42)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun uu___3 ->
                       match uu___3 with
                       | FStar_Reflection_V2_Formula.Comp
                           (FStar_Reflection_V2_Formula.Eq
                            (FStar_Pervasives_Native.Some t), t1, t2)
                           ->
                           Obj.magic
                             (Obj.repr
                                (let uu___4 =
                                   let uu___5 =
                                     Obj.magic
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___6 ->
                                             (fun uu___6 ->
                                                Obj.magic
                                                  (failwith
                                                     "Cannot evaluate open quotation at runtime"))
                                               uu___6)) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.CanonCommMonoidSimple.fst"
                                              (Prims.of_int (255))
                                              (Prims.of_int (19))
                                              (Prims.of_int (255))
                                              (Prims.of_int (28)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.CanonCommMonoidSimple.fst"
                                              (Prims.of_int (255))
                                              (Prims.of_int (9))
                                              (Prims.of_int (255))
                                              (Prims.of_int (28)))))
                                     (Obj.magic uu___5)
                                     (fun uu___6 ->
                                        (fun uu___6 ->
                                           Obj.magic (term_eq t uu___6))
                                          uu___6) in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.CanonCommMonoidSimple.fst"
                                            (Prims.of_int (255))
                                            (Prims.of_int (9))
                                            (Prims.of_int (255))
                                            (Prims.of_int (28)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.CanonCommMonoidSimple.fst"
                                            (Prims.of_int (255))
                                            (Prims.of_int (6))
                                            (Prims.of_int (273))
                                            (Prims.of_int (69)))))
                                   (Obj.magic uu___4)
                                   (fun uu___5 ->
                                      (fun uu___5 ->
                                         if uu___5
                                         then
                                           Obj.magic
                                             (Obj.repr
                                                (let uu___6 =
                                                   reification m []
                                                     (const
                                                        (FStar_Algebra_CommMonoid.__proj__CM__item__unit
                                                           m)) t1 in
                                                 FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                            (Prims.of_int (256))
                                                            (Prims.of_int (27))
                                                            (Prims.of_int (256))
                                                            (Prims.of_int (67)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                            (Prims.of_int (255))
                                                            (Prims.of_int (33))
                                                            (Prims.of_int (271))
                                                            (Prims.of_int (22)))))
                                                   (Obj.magic uu___6)
                                                   (fun uu___7 ->
                                                      (fun uu___7 ->
                                                         match uu___7 with
                                                         | (r1, ts, am) ->
                                                             let uu___8 =
                                                               reification m
                                                                 ts am t2 in
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (48)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (22)))))
                                                                  (Obj.magic
                                                                    uu___8)
                                                                  (fun uu___9
                                                                    ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (r2,
                                                                    uu___10,
                                                                    am1) ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))
                                                                    uu___15)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V2_Builtins.term_to_string
                                                                    uu___15))
                                                                    uu___15) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
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
                                                                    "am ="
                                                                    uu___14)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (dump
                                                                    uu___13))
                                                                    uu___13) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (22)))))
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
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))
                                                                    uu___15)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.change_sq
                                                                    uu___15))
                                                                    uu___15) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    FStar_Tactics_V2_Derived.apply
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoidSimple";
                                                                    "monoid_reflect"]))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.fst"
                                                                    (Prims.of_int (267))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V2_Builtins.norm
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
                                                                    uu___16)))
                                                                    uu___14)))
                                                                    uu___12)))
                                                                    uu___9)))
                                                        uu___7)))
                                         else
                                           Obj.magic
                                             (Obj.repr
                                                (FStar_Tactics_V2_Derived.fail
                                                   "Goal should be an equality at the right monoid type")))
                                        uu___5)))
                       | uu___4 ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_V2_Derived.fail
                                   "Goal should be an equality"))) uu___3)))
           uu___1)