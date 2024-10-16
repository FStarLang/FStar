open Prims
let (term_eq :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term -> Prims.bool)
  = FStar_Reflection_TermEq_Simple.term_eq
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
                        (if term_eq x x'
                         then
                           Obj.repr
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> FStar_Pervasives_Native.Some n))
                         else Obj.repr (where_aux (n + Prims.int_one) x xs'))))
          uu___2 uu___1 uu___
let (where :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term Prims.list ->
      (Prims.nat FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  = where_aux Prims.int_zero
let (fatom :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term Prims.list ->
      FStar_Tactics_NamedView.term amap ->
        ((exp * FStar_Tactics_NamedView.term Prims.list *
           FStar_Tactics_NamedView.term amap),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun ts ->
      fun am ->
        let uu___ = where t ts in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                   (Prims.of_int (279)) (Prims.of_int (8))
                   (Prims.of_int (279)) (Prims.of_int (18)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                   (Prims.of_int (279)) (Prims.of_int (2))
                   (Prims.of_int (284)) (Prims.of_int (47)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | FStar_Pervasives_Native.Some v ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> ((Atom v), ts, am))))
                | FStar_Pervasives_Native.None ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 =
                            Obj.magic
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___3 -> FStar_List_Tot_Base.length ts)) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                     (Prims.of_int (282)) (Prims.of_int (17))
                                     (Prims.of_int (282)) (Prims.of_int (26)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                     (Prims.of_int (282)) (Prims.of_int (29))
                                     (Prims.of_int (284)) (Prims.of_int (47)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun vfresh ->
                                  let uu___3 =
                                    FStar_Tactics_V2_Derived.norm_term
                                      [FStar_Pervasives.iota;
                                      FStar_Pervasives.zeta] t in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                (Prims.of_int (283))
                                                (Prims.of_int (12))
                                                (Prims.of_int (283))
                                                (Prims.of_int (36)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                (Prims.of_int (284))
                                                (Prims.of_int (4))
                                                (Prims.of_int (284))
                                                (Prims.of_int (47)))))
                                       (Obj.magic uu___3)
                                       (fun t1 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___4 ->
                                               ((Atom vfresh),
                                                 (FStar_List_Tot_Base.op_At
                                                    ts [t1]),
                                                 (update vfresh t1 am))))))
                                 uu___3)))) uu___1)
let rec (reification_aux :
  FStar_Tactics_NamedView.term Prims.list ->
    FStar_Tactics_NamedView.term amap ->
      FStar_Tactics_NamedView.term ->
        FStar_Tactics_NamedView.term ->
          FStar_Tactics_NamedView.term ->
            ((exp * FStar_Tactics_NamedView.term Prims.list *
               FStar_Tactics_NamedView.term amap),
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ts ->
    fun am ->
      fun mult ->
        fun unit ->
          fun t ->
            let uu___ = FStar_Tactics_V2_SyntaxHelpers.collect_app t in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                       (Prims.of_int (289)) (Prims.of_int (15))
                       (Prims.of_int (289)) (Prims.of_int (28)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                       (Prims.of_int (288)) (Prims.of_int (82))
                       (Prims.of_int (300)) (Prims.of_int (22)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun uu___1 ->
                    match uu___1 with
                    | (hd, tl) ->
                        let uu___2 =
                          let uu___3 = FStar_Tactics_NamedView.inspect hd in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                     (Prims.of_int (290)) (Prims.of_int (8))
                                     (Prims.of_int (290)) (Prims.of_int (18)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                     (Prims.of_int (290)) (Prims.of_int (8))
                                     (Prims.of_int (290)) (Prims.of_int (22)))))
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___5 -> (uu___4, tl))) in
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                      (Prims.of_int (290)) (Prims.of_int (8))
                                      (Prims.of_int (290))
                                      (Prims.of_int (22)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                      (Prims.of_int (290)) (Prims.of_int (2))
                                      (Prims.of_int (300))
                                      (Prims.of_int (22)))))
                             (Obj.magic uu___2)
                             (fun uu___3 ->
                                (fun uu___3 ->
                                   match uu___3 with
                                   | (FStar_Tactics_NamedView.Tv_FVar fv,
                                      (t1,
                                       FStarC_Reflection_V2_Data.Q_Explicit)::
                                      (t2,
                                       FStarC_Reflection_V2_Data.Q_Explicit)::[])
                                       ->
                                       Obj.magic
                                         (Obj.repr
                                            (if
                                               term_eq
                                                 (FStar_Tactics_NamedView.pack
                                                    (FStar_Tactics_NamedView.Tv_FVar
                                                       fv)) mult
                                             then
                                               let uu___4 =
                                                 reification_aux ts am mult
                                                   unit t1 in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                          (Prims.of_int (293))
                                                          (Prims.of_int (29))
                                                          (Prims.of_int (293))
                                                          (Prims.of_int (63)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                          (Prims.of_int (293))
                                                          (Prims.of_int (9))
                                                          (Prims.of_int (295))
                                                          (Prims.of_int (31)))))
                                                 (Obj.magic uu___4)
                                                 (fun uu___5 ->
                                                    (fun uu___5 ->
                                                       match uu___5 with
                                                       | (e1, ts1, am1) ->
                                                           let uu___6 =
                                                             reification_aux
                                                               ts1 am1 mult
                                                               unit t2 in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (63)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (293))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (295))
                                                                    (Prims.of_int (30)))))
                                                                (Obj.magic
                                                                   uu___6)
                                                                (fun uu___7
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (e2, ts2,
                                                                    am2) ->
                                                                    ((Mult
                                                                    (e1, e2)),
                                                                    ts2, am2)))))
                                                      uu___5)
                                             else fatom t ts am))
                                   | (uu___4, uu___5) ->
                                       Obj.magic
                                         (Obj.repr
                                            (if term_eq t unit
                                             then
                                               Obj.repr
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___6 ->
                                                       (Unit, ts, am)))
                                             else Obj.repr (fatom t ts am))))
                                  uu___3))) uu___1)
let (reification :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term ->
      FStar_Tactics_NamedView.term Prims.list ->
        FStar_Tactics_NamedView.term amap ->
          FStar_Tactics_NamedView.term ->
            ((exp * FStar_Tactics_NamedView.term Prims.list *
               FStar_Tactics_NamedView.term amap),
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun eq ->
    fun m ->
      fun ts ->
        fun am ->
          fun t ->
            let uu___ =
              FStar_Tactics_V2_Derived.norm_term
                [FStar_Pervasives.iota;
                FStar_Pervasives.zeta;
                FStar_Pervasives.delta]
                (FStarC_Reflection_V2_Builtins.pack_ln
                   (FStarC_Reflection_V2_Data.Tv_App
                      ((FStarC_Reflection_V2_Builtins.pack_ln
                          (FStarC_Reflection_V2_Data.Tv_FVar
                             (FStarC_Reflection_V2_Builtins.pack_fv
                                ["FStar";
                                "Algebra";
                                "CommMonoid";
                                "Equiv";
                                "__proj__CM__item__mult"]))),
                        (m, FStarC_Reflection_V2_Data.Q_Explicit)))) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                       (Prims.of_int (304)) (Prims.of_int (13))
                       (Prims.of_int (304)) (Prims.of_int (60)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                       (Prims.of_int (304)) (Prims.of_int (63))
                       (Prims.of_int (307)) (Prims.of_int (35)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun mult ->
                    let uu___1 =
                      FStar_Tactics_V2_Derived.norm_term
                        [FStar_Pervasives.iota;
                        FStar_Pervasives.zeta;
                        FStar_Pervasives.delta]
                        (FStarC_Reflection_V2_Builtins.pack_ln
                           (FStarC_Reflection_V2_Data.Tv_App
                              ((FStarC_Reflection_V2_Builtins.pack_ln
                                  (FStarC_Reflection_V2_Data.Tv_FVar
                                     (FStarC_Reflection_V2_Builtins.pack_fv
                                        ["FStar";
                                        "Algebra";
                                        "CommMonoid";
                                        "Equiv";
                                        "__proj__CM__item__unit"]))),
                                (m, FStarC_Reflection_V2_Data.Q_Explicit)))) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                  (Prims.of_int (305)) (Prims.of_int (13))
                                  (Prims.of_int (305)) (Prims.of_int (60)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                  (Prims.of_int (305)) (Prims.of_int (63))
                                  (Prims.of_int (307)) (Prims.of_int (35)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            (fun unit ->
                               let uu___2 =
                                 FStar_Tactics_V2_Derived.norm_term
                                   [FStar_Pervasives.iota;
                                   FStar_Pervasives.zeta] t in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                             (Prims.of_int (306))
                                             (Prims.of_int (13))
                                             (Prims.of_int (306))
                                             (Prims.of_int (37)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                             (Prims.of_int (307))
                                             (Prims.of_int (2))
                                             (Prims.of_int (307))
                                             (Prims.of_int (35)))))
                                    (Obj.magic uu___2)
                                    (fun uu___3 ->
                                       (fun t1 ->
                                          Obj.magic
                                            (reification_aux ts am mult unit
                                               t1)) uu___3))) uu___2)))
                   uu___1)
let rec (repeat_cong_right_identity :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun eq ->
    fun m ->
      FStar_Tactics_V2_Derived.or_else
        (fun uu___ ->
           FStar_Tactics_V2_Derived.apply_lemma
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv
                      ["FStar";
                      "Algebra";
                      "CommMonoid";
                      "Equiv";
                      "right_identity"]))))
        (fun uu___ ->
           let uu___1 =
             FStar_Tactics_V2_Derived.apply_lemma
               (FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_App
                     ((FStarC_Reflection_V2_Builtins.pack_ln
                         (FStarC_Reflection_V2_Data.Tv_FVar
                            (FStarC_Reflection_V2_Builtins.pack_fv
                               ["FStar";
                               "Algebra";
                               "CommMonoid";
                               "Equiv";
                               "__proj__CM__item__congruence"]))),
                       (m, FStarC_Reflection_V2_Data.Q_Explicit)))) in
           FStar_Tactics_Effect.tac_bind
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range
                      "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                      (Prims.of_int (311)) (Prims.of_int (20))
                      (Prims.of_int (311)) (Prims.of_int (55)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range
                      "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                      (Prims.of_int (312)) (Prims.of_int (20))
                      (Prims.of_int (314)) (Prims.of_int (51)))))
             (Obj.magic uu___1)
             (fun uu___2 ->
                (fun uu___2 ->
                   let uu___3 = FStar_Tactics_V2_Logic.split () in
                   Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                 (Prims.of_int (312)) (Prims.of_int (20))
                                 (Prims.of_int (312)) (Prims.of_int (28)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                 (Prims.of_int (313)) (Prims.of_int (20))
                                 (Prims.of_int (314)) (Prims.of_int (51)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           (fun uu___4 ->
                              let uu___5 =
                                FStar_Tactics_V2_Derived.apply_lemma
                                  (FStarC_Reflection_V2_Builtins.pack_ln
                                     (FStarC_Reflection_V2_Data.Tv_App
                                        ((FStarC_Reflection_V2_Builtins.pack_ln
                                            (FStarC_Reflection_V2_Data.Tv_FVar
                                               (FStarC_Reflection_V2_Builtins.pack_fv
                                                  ["FStar";
                                                  "Algebra";
                                                  "CommMonoid";
                                                  "Equiv";
                                                  "__proj__EQ__item__reflexivity"]))),
                                          (eq,
                                            FStarC_Reflection_V2_Data.Q_Explicit)))) in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                            (Prims.of_int (313))
                                            (Prims.of_int (20))
                                            (Prims.of_int (313))
                                            (Prims.of_int (57)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                            (Prims.of_int (314))
                                            (Prims.of_int (20))
                                            (Prims.of_int (314))
                                            (Prims.of_int (51)))))
                                   (Obj.magic uu___5)
                                   (fun uu___6 ->
                                      (fun uu___6 ->
                                         Obj.magic
                                           (repeat_cong_right_identity eq m))
                                        uu___6))) uu___4))) uu___2))
let rec (convert_map :
  (atom * FStar_Tactics_NamedView.term) Prims.list ->
    FStar_Tactics_NamedView.term)
  =
  fun m ->
    match m with
    | [] ->
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "Nil"]))
    | (a, t)::ps ->
        let a1 =
          FStar_Tactics_NamedView.pack
            (FStar_Tactics_NamedView.Tv_Const
               (FStarC_Reflection_V2_Data.C_Int a)) in
        let uu___ = convert_map ps in
        let uu___1 = t in
        let uu___2 = a1 in
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_App
             ((FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_App
                    ((FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["Prims"; "Cons"]))),
                      ((FStarC_Reflection_V2_Builtins.pack_ln
                          (FStarC_Reflection_V2_Data.Tv_App
                             ((FStarC_Reflection_V2_Builtins.pack_ln
                                 (FStarC_Reflection_V2_Data.Tv_App
                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                        (FStarC_Reflection_V2_Data.Tv_FVar
                                           (FStarC_Reflection_V2_Builtins.pack_fv
                                              ["FStar";
                                              "Pervasives";
                                              "Native";
                                              "Mktuple2"]))),
                                      (uu___2,
                                        FStarC_Reflection_V2_Data.Q_Explicit)))),
                               (uu___1, FStarC_Reflection_V2_Data.Q_Explicit)))),
                        FStarC_Reflection_V2_Data.Q_Explicit)))),
               (uu___, FStarC_Reflection_V2_Data.Q_Explicit)))
let (convert_am :
  FStar_Tactics_NamedView.term amap -> FStar_Tactics_NamedView.term) =
  fun am ->
    let uu___ = am in
    match uu___ with
    | (map, def) ->
        let uu___1 = def in
        let uu___2 = convert_map map in
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_App
             ((FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_App
                    ((FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar"; "Pervasives"; "Native"; "Mktuple2"]))),
                      (uu___2, FStarC_Reflection_V2_Data.Q_Explicit)))),
               (uu___1, FStarC_Reflection_V2_Data.Q_Explicit)))
let rec (quote_exp : exp -> FStar_Tactics_NamedView.term) =
  fun e ->
    match e with
    | Unit ->
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                ["FStar";
                "Tactics";
                "CanonCommMonoidSimple";
                "Equiv";
                "Unit"]))
    | Mult (e1, e2) ->
        let uu___ = quote_exp e2 in
        let uu___1 = quote_exp e1 in
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_App
             ((FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_App
                    ((FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "CanonCommMonoidSimple";
                              "Equiv";
                              "Mult"]))),
                      (uu___1, FStarC_Reflection_V2_Data.Q_Explicit)))),
               (uu___, FStarC_Reflection_V2_Data.Q_Explicit)))
    | Atom n ->
        let nt =
          FStar_Tactics_NamedView.pack
            (FStar_Tactics_NamedView.Tv_Const
               (FStarC_Reflection_V2_Data.C_Int n)) in
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_App
             ((FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar";
                       "Tactics";
                       "CanonCommMonoidSimple";
                       "Equiv";
                       "Atom"]))),
               (nt, FStarC_Reflection_V2_Data.Q_Explicit)))
let (canon_lhs_rhs :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term ->
      FStar_Tactics_NamedView.term ->
        FStar_Tactics_NamedView.term ->
          (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun eq ->
    fun m ->
      fun lhs ->
        fun rhs ->
          let uu___ =
            FStar_Tactics_V2_Derived.norm_term
              [FStar_Pervasives.iota;
              FStar_Pervasives.zeta;
              FStar_Pervasives.delta]
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_App
                    ((FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Algebra";
                              "CommMonoid";
                              "Equiv";
                              "__proj__CM__item__unit"]))),
                      (m, FStarC_Reflection_V2_Data.Q_Explicit)))) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                     (Prims.of_int (341)) (Prims.of_int (15))
                     (Prims.of_int (341)) (Prims.of_int (61)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                     (Prims.of_int (341)) (Prims.of_int (64))
                     (Prims.of_int (370)) (Prims.of_int (52)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun m_unit ->
                  let uu___1 =
                    Obj.magic
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___2 -> const m_unit)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                (Prims.of_int (342)) (Prims.of_int (11))
                                (Prims.of_int (342)) (Prims.of_int (23)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                (Prims.of_int (342)) (Prims.of_int (26))
                                (Prims.of_int (370)) (Prims.of_int (52)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun am ->
                             let uu___2 = reification eq m [] am lhs in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                           (Prims.of_int (343))
                                           (Prims.of_int (21))
                                           (Prims.of_int (343))
                                           (Prims.of_int (47)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                           (Prims.of_int (342))
                                           (Prims.of_int (26))
                                           (Prims.of_int (370))
                                           (Prims.of_int (52)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     (fun uu___3 ->
                                        match uu___3 with
                                        | (r1, ts, am1) ->
                                            let uu___4 =
                                              reification eq m ts am1 rhs in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                          (Prims.of_int (344))
                                                          (Prims.of_int (21))
                                                          (Prims.of_int (344))
                                                          (Prims.of_int (47)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                          (Prims.of_int (343))
                                                          (Prims.of_int (50))
                                                          (Prims.of_int (370))
                                                          (Prims.of_int (52)))))
                                                 (Obj.magic uu___4)
                                                 (fun uu___5 ->
                                                    (fun uu___5 ->
                                                       match uu___5 with
                                                       | (r2, uu___6, am2) ->
                                                           let uu___7 =
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___8
                                                                    ->
                                                                    convert_am
                                                                    am2)) in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (24)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (52)))))
                                                                (Obj.magic
                                                                   uu___7)
                                                                (fun uu___8
                                                                   ->
                                                                   (fun am3
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    quote_exp
                                                                    r1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun r11
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    quote_exp
                                                                    r2)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun r21
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    FStar_Tactics_V2_Derived.change_sq
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Algebra";
                                                                    "CommMonoid";
                                                                    "Equiv";
                                                                    "__proj__EQ__item__eq"]))),
                                                                    (eq,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoidSimple";
                                                                    "Equiv";
                                                                    "mdenote"]))),
                                                                    (eq,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (m,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (am3,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (r11,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoidSimple";
                                                                    "Equiv";
                                                                    "mdenote"]))),
                                                                    (eq,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (m,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (am3,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (r21,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (356))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (52)))))
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
                                                                    FStar_Tactics_V2_Derived.apply
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoidSimple";
                                                                    "Equiv";
                                                                    "monoid_reflect"]))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (52)))))
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
                                                                    FStarC_Tactics_V2_Builtins.norm
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
                                                                    FStar_Pervasives.primops] in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (370))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.or_else
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Algebra";
                                                                    "CommMonoid";
                                                                    "Equiv";
                                                                    "__proj__EQ__item__reflexivity"]))),
                                                                    (eq,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))))
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    repeat_cong_right_identity
                                                                    eq m)))
                                                                    uu___15)))
                                                                    uu___13)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                      uu___5))) uu___3)))
                            uu___2))) uu___1)
let (canon_monoid :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun eq ->
    fun m ->
      let uu___ =
        FStarC_Tactics_V2_Builtins.norm
          [FStar_Pervasives.iota; FStar_Pervasives.zeta] in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                 (Prims.of_int (374)) (Prims.of_int (2)) (Prims.of_int (374))
                 (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                 (Prims.of_int (374)) (Prims.of_int (20))
                 (Prims.of_int (392)) (Prims.of_int (68)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              let uu___2 = FStar_Tactics_V2_Derived.cur_goal () in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                            (Prims.of_int (375)) (Prims.of_int (10))
                            (Prims.of_int (375)) (Prims.of_int (21)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                            (Prims.of_int (375)) (Prims.of_int (24))
                            (Prims.of_int (392)) (Prims.of_int (68)))))
                   (Obj.magic uu___2)
                   (fun uu___3 ->
                      (fun t ->
                         let uu___3 =
                           FStar_Tactics_V2_SyntaxHelpers.collect_app t in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                       (Prims.of_int (377))
                                       (Prims.of_int (19))
                                       (Prims.of_int (377))
                                       (Prims.of_int (32)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                       (Prims.of_int (375))
                                       (Prims.of_int (24))
                                       (Prims.of_int (392))
                                       (Prims.of_int (68)))))
                              (Obj.magic uu___3)
                              (fun uu___4 ->
                                 (fun uu___4 ->
                                    match uu___4 with
                                    | (sq, rel_xy) ->
                                        (match rel_xy with
                                         | (rel_xy1, uu___5)::[] ->
                                             Obj.magic
                                               (Obj.repr
                                                  (let uu___6 =
                                                     FStar_Tactics_V2_SyntaxHelpers.collect_app
                                                       rel_xy1 in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                              (Prims.of_int (381))
                                                              (Prims.of_int (21))
                                                              (Prims.of_int (381))
                                                              (Prims.of_int (39)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.CanonCommMonoidSimple.Equiv.fst"
                                                              (Prims.of_int (380))
                                                              (Prims.of_int (21))
                                                              (Prims.of_int (391))
                                                              (Prims.of_int (6)))))
                                                     (Obj.magic uu___6)
                                                     (fun uu___7 ->
                                                        (fun uu___7 ->
                                                           match uu___7 with
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
                                                                    FStarC_Reflection_V2_Data.Q_Explicit),
                                                                    (rhs,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))
                                                                    ->
                                                                    Obj.repr
                                                                    (canon_lhs_rhs
                                                                    eq m lhs
                                                                    rhs)
                                                                    | 
                                                                    uu___8 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Goal should have been an application of a binary relation to 2 explicit arguments")))
                                                               else
                                                                 Obj.magic
                                                                   (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Goal should have been an application of a binary relation to n implicit and 2 explicit arguments")))
                                                          uu___7)))
                                         | uu___5 ->
                                             Obj.magic
                                               (Obj.repr
                                                  (FStar_Tactics_V2_Derived.fail
                                                     "Goal should be squash applied to a binary relation"))))
                                   uu___4))) uu___3))) uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.CanonCommMonoidSimple.Equiv.canon_monoid"
    (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.CanonCommMonoidSimple.Equiv.canon_monoid (plugin)"
               (FStarC_Tactics_Native.from_tactic_2 canon_monoid)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)