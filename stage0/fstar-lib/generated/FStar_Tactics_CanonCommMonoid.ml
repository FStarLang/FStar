open Prims
let (term_eq :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term -> Prims.bool)
  = FStar_Reflection_TermEq_Simple.term_eq
let (dump : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun m ->
    let uu___ = FStarC_Tactics_V2_Builtins.debugging () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
               (Prims.of_int (35)) (Prims.of_int (24)) (Prims.of_int (35))
               (Prims.of_int (36)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
               (Prims.of_int (35)) (Prims.of_int (21)) (Prims.of_int (35))
               (Prims.of_int (48))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            if uu___1
            then Obj.magic (Obj.repr (FStarC_Tactics_V2_Builtins.dump m))
            else
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))))
           uu___1)
type var = Prims.nat
type exp =
  | Unit 
  | Var of var 
  | Mult of exp * exp 
let (uu___is_Unit : exp -> Prims.bool) =
  fun projectee -> match projectee with | Unit -> true | uu___ -> false
let (uu___is_Var : exp -> Prims.bool) =
  fun projectee -> match projectee with | Var _0 -> true | uu___ -> false
let (__proj__Var__item___0 : exp -> var) =
  fun projectee -> match projectee with | Var _0 -> _0
let (uu___is_Mult : exp -> Prims.bool) =
  fun projectee ->
    match projectee with | Mult (_0, _1) -> true | uu___ -> false
let (__proj__Mult__item___0 : exp -> exp) =
  fun projectee -> match projectee with | Mult (_0, _1) -> _0
let (__proj__Mult__item___1 : exp -> exp) =
  fun projectee -> match projectee with | Mult (_0, _1) -> _1
let rec (exp_to_string : exp -> Prims.string) =
  fun e ->
    match e with
    | Unit -> "Unit"
    | Var x -> Prims.strcat "Var " (Prims.string_of_int x)
    | Mult (e1, e2) ->
        Prims.strcat "Mult ("
          (Prims.strcat (exp_to_string e1)
             (Prims.strcat ") (" (Prims.strcat (exp_to_string e2) ")")))
type ('a, 'b) vmap = ((var * ('a * 'b)) Prims.list * ('a * 'b))
let const : 'a 'b . 'a -> 'b -> ('a, 'b) vmap =
  fun xa -> fun xb -> ([], (xa, xb))
let select : 'a 'b . var -> ('a, 'b) vmap -> 'a =
  fun x ->
    fun vm ->
      match FStar_List_Tot_Base.assoc x (FStar_Pervasives_Native.fst vm) with
      | FStar_Pervasives_Native.Some (a1, uu___) -> a1
      | uu___ -> FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd vm)
let select_extra : 'a 'b . var -> ('a, 'b) vmap -> 'b =
  fun x ->
    fun vm ->
      match FStar_List_Tot_Base.assoc x (FStar_Pervasives_Native.fst vm) with
      | FStar_Pervasives_Native.Some (uu___, b1) -> b1
      | uu___ -> FStar_Pervasives_Native.snd (FStar_Pervasives_Native.snd vm)
let update : 'a 'b . var -> 'a -> 'b -> ('a, 'b) vmap -> ('a, 'b) vmap =
  fun x ->
    fun xa ->
      fun xb ->
        fun vm ->
          (((x, (xa, xb)) :: (FStar_Pervasives_Native.fst vm)),
            (FStar_Pervasives_Native.snd vm))
let rec mdenote :
  'a 'b . 'a FStar_Algebra_CommMonoid.cm -> ('a, 'b) vmap -> exp -> 'a =
  fun m ->
    fun vm ->
      fun e ->
        match e with
        | Unit -> FStar_Algebra_CommMonoid.__proj__CM__item__unit m
        | Var x -> select x vm
        | Mult (e1, e2) ->
            FStar_Algebra_CommMonoid.__proj__CM__item__mult m
              (mdenote m vm e1) (mdenote m vm e2)
let rec xsdenote :
  'a 'b .
    'a FStar_Algebra_CommMonoid.cm -> ('a, 'b) vmap -> var Prims.list -> 'a
  =
  fun m ->
    fun vm ->
      fun xs ->
        match xs with
        | [] -> FStar_Algebra_CommMonoid.__proj__CM__item__unit m
        | x::[] -> select x vm
        | x::xs' ->
            FStar_Algebra_CommMonoid.__proj__CM__item__mult m (select x vm)
              (xsdenote m vm xs')
let rec (flatten : exp -> var Prims.list) =
  fun e ->
    match e with
    | Unit -> []
    | Var x -> [x]
    | Mult (e1, e2) -> FStar_List_Tot_Base.op_At (flatten e1) (flatten e2)
type 'b permute =
  unit -> (Obj.t, 'b) vmap -> var Prims.list -> var Prims.list
type ('b, 'p) permute_correct = unit
type ('b, 'p) permute_via_swaps = unit

let (sort : unit permute) =
  fun a ->
    fun vm ->
      FStar_List_Tot_Base.sortWith (FStar_List_Tot_Base.compare_of_bool (<))
let sortWith : 'b . (Prims.nat -> Prims.nat -> Prims.int) -> 'b permute =
  fun f -> fun a -> fun vm -> FStar_List_Tot_Base.sortWith f


let canon : 'a 'b . ('a, 'b) vmap -> 'b permute -> exp -> var Prims.list =
  fun vm -> fun p -> fun e -> p () (Obj.magic vm) (flatten e)
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
                        (let uu___ =
                           FStarC_Tactics_V2_Builtins.term_eq_old x x' in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommMonoid.fst"
                                    (Prims.of_int (239)) (Prims.of_int (18))
                                    (Prims.of_int (239)) (Prims.of_int (34)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommMonoid.fst"
                                    (Prims.of_int (239)) (Prims.of_int (15))
                                    (Prims.of_int (239)) (Prims.of_int (73)))))
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
  'a 'b .
    (FStar_Tactics_NamedView.term -> ('a, unit) FStar_Tactics_Effect.tac_repr)
      ->
      FStar_Tactics_NamedView.term Prims.list ->
        ('a, 'b) vmap ->
          (FStar_Tactics_NamedView.term ->
             ('b, unit) FStar_Tactics_Effect.tac_repr)
            ->
            FStar_Tactics_NamedView.term ->
              FStar_Tactics_NamedView.term ->
                FStar_Tactics_NamedView.term ->
                  ((exp * FStar_Tactics_NamedView.term Prims.list * (
                     'a, 'b) vmap),
                    unit) FStar_Tactics_Effect.tac_repr
  =
  fun unquotea ->
    fun ts ->
      fun vm ->
        fun f ->
          fun mult ->
            fun unit ->
              fun t ->
                let uu___ =
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 ->
                          FStar_Reflection_V2_Derived_Lemmas.collect_app_ref
                            t)) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.Tactics.CanonCommMonoid.fst"
                           (Prims.of_int (246)) (Prims.of_int (15))
                           (Prims.of_int (246)) (Prims.of_int (32)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.Tactics.CanonCommMonoid.fst"
                           (Prims.of_int (245)) (Prims.of_int (61))
                           (Prims.of_int (263)) (Prims.of_int (21)))))
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
                                          fun vm1 ->
                                            let uu___4 = where t1 ts1 in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.CanonCommMonoid.fst"
                                                       (Prims.of_int (248))
                                                       (Prims.of_int (10))
                                                       (Prims.of_int (248))
                                                       (Prims.of_int (20)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.CanonCommMonoid.fst"
                                                       (Prims.of_int (248))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (251))
                                                       (Prims.of_int (62)))))
                                              (Obj.magic uu___4)
                                              (fun uu___5 ->
                                                 (fun uu___5 ->
                                                    match uu___5 with
                                                    | FStar_Pervasives_Native.Some
                                                        v ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___6
                                                                   ->
                                                                   ((Var v),
                                                                    ts1, vm1))))
                                                    | FStar_Pervasives_Native.None
                                                        ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (let uu___6 =
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_List_Tot_Base.length
                                                                    ts1)) in
                                                              FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (36)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (62)))))
                                                                (Obj.magic
                                                                   uu___6)
                                                                (fun uu___7
                                                                   ->
                                                                   (fun
                                                                    vfresh ->
                                                                    let uu___7
                                                                    =
                                                                    unquotea
                                                                    t1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun z ->
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    = f t1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    update
                                                                    vfresh z
                                                                    uu___10
                                                                    vm1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    ((Var
                                                                    vfresh),
                                                                    (FStar_List_Tot_Base.op_At
                                                                    ts1 
                                                                    [t1]),
                                                                    uu___9)))))
                                                                    uu___8)))
                                                                    uu___7))))
                                                   uu___5))) in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.CanonCommMonoid.fst"
                                          (Prims.of_int (248))
                                          (Prims.of_int (4))
                                          (Prims.of_int (251))
                                          (Prims.of_int (62)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.CanonCommMonoid.fst"
                                          (Prims.of_int (253))
                                          (Prims.of_int (2))
                                          (Prims.of_int (263))
                                          (Prims.of_int (21)))))
                                 (Obj.magic uu___2)
                                 (fun uu___3 ->
                                    (fun fvar ->
                                       let uu___3 =
                                         let uu___4 =
                                           FStar_Tactics_NamedView.inspect hd in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                    (Prims.of_int (253))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (253))
                                                    (Prims.of_int (18)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                    (Prims.of_int (253))
                                                    (Prims.of_int (8))
                                                    (Prims.of_int (253))
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
                                                     "FStar.Tactics.CanonCommMonoid.fst"
                                                     (Prims.of_int (253))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (253))
                                                     (Prims.of_int (33)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.CanonCommMonoid.fst"
                                                     (Prims.of_int (253))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (263))
                                                     (Prims.of_int (21)))))
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
                                                        FStarC_Tactics_V2_Builtins.term_eq_old
                                                          (FStar_Tactics_NamedView.pack
                                                             (FStar_Tactics_NamedView.Tv_FVar
                                                                fv)) mult in
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (43)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (259))
                                                                    (Prims.of_int (21)))))
                                                           (Obj.magic uu___5)
                                                           (fun uu___6 ->
                                                              (fun uu___6 ->
                                                                 if uu___6
                                                                 then
                                                                   let uu___7
                                                                    =
                                                                    reification_aux
                                                                    unquotea
                                                                    ts vm f
                                                                    mult unit
                                                                    t1 in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (e1, ts1,
                                                                    vm1) ->
                                                                    let uu___9
                                                                    =
                                                                    reification_aux
                                                                    unquotea
                                                                    ts1 vm1 f
                                                                    mult unit
                                                                    t2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (258))
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
                                                                    vm2) ->
                                                                    ((Mult
                                                                    (e1, e2)),
                                                                    ts2, vm2)))))
                                                                    uu___8))
                                                                 else
                                                                   Obj.magic
                                                                    (fvar t
                                                                    ts vm))
                                                                uu___6))
                                                  | (uu___5, uu___6) ->
                                                      let uu___7 =
                                                        FStarC_Tactics_V2_Builtins.term_eq_old
                                                          t unit in
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (25)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (261))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (21)))))
                                                           (Obj.magic uu___7)
                                                           (fun uu___8 ->
                                                              (fun uu___8 ->
                                                                 if uu___8
                                                                 then
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    (Unit,
                                                                    ts, vm))))
                                                                 else
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (fvar t
                                                                    ts vm)))
                                                                uu___8)))
                                                 uu___4))) uu___3))) uu___1)
let reification :
  'b .
    (FStar_Tactics_NamedView.term -> ('b, unit) FStar_Tactics_Effect.tac_repr)
      ->
      'b ->
        unit ->
          (FStar_Tactics_NamedView.term ->
             (Obj.t, unit) FStar_Tactics_Effect.tac_repr)
            ->
            (Obj.t ->
               (FStar_Tactics_NamedView.term, unit)
                 FStar_Tactics_Effect.tac_repr)
              ->
              FStar_Tactics_NamedView.term ->
                FStar_Tactics_NamedView.term ->
                  Obj.t ->
                    FStar_Tactics_NamedView.term Prims.list ->
                      ((exp Prims.list * (Obj.t, 'b) vmap), unit)
                        FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    fun def ->
      fun a ->
        fun unquotea ->
          fun quotea ->
            fun tmult ->
              fun tunit ->
                fun munit ->
                  fun ts ->
                    let uu___ =
                      FStar_Tactics_V2_Derived.norm_term
                        [FStar_Pervasives.delta;
                        FStar_Pervasives.zeta;
                        FStar_Pervasives.iota] tmult in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.CanonCommMonoid.fst"
                               (Prims.of_int (270)) (Prims.of_int (20))
                               (Prims.of_int (270)) (Prims.of_int (53)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.CanonCommMonoid.fst"
                               (Prims.of_int (270)) (Prims.of_int (56))
                               (Prims.of_int (282)) (Prims.of_int (30)))))
                      (Obj.magic uu___)
                      (fun uu___1 ->
                         (fun tmult1 ->
                            let uu___1 =
                              FStar_Tactics_V2_Derived.norm_term
                                [FStar_Pervasives.delta;
                                FStar_Pervasives.zeta;
                                FStar_Pervasives.iota] tunit in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.CanonCommMonoid.fst"
                                          (Prims.of_int (271))
                                          (Prims.of_int (20))
                                          (Prims.of_int (271))
                                          (Prims.of_int (53)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.CanonCommMonoid.fst"
                                          (Prims.of_int (271))
                                          (Prims.of_int (56))
                                          (Prims.of_int (282))
                                          (Prims.of_int (30)))))
                                 (Obj.magic uu___1)
                                 (fun uu___2 ->
                                    (fun tunit1 ->
                                       let uu___2 =
                                         FStar_Tactics_Util.map
                                           (FStar_Tactics_V2_Derived.norm_term
                                              [FStar_Pervasives.delta;
                                              FStar_Pervasives.zeta;
                                              FStar_Pervasives.iota]) ts in
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.CanonCommMonoid.fst"
                                                     (Prims.of_int (272))
                                                     (Prims.of_int (13))
                                                     (Prims.of_int (272))
                                                     (Prims.of_int (62)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.CanonCommMonoid.fst"
                                                     (Prims.of_int (272))
                                                     (Prims.of_int (65))
                                                     (Prims.of_int (282))
                                                     (Prims.of_int (30)))))
                                            (Obj.magic uu___2)
                                            (fun uu___3 ->
                                               (fun ts1 ->
                                                  let uu___3 =
                                                    FStar_Tactics_Util.fold_left
                                                      (fun uu___4 ->
                                                         fun t ->
                                                           match uu___4 with
                                                           | (es, vs, vm) ->
                                                               let uu___5 =
                                                                 reification_aux
                                                                   unquotea
                                                                   vs vm f
                                                                   tmult1
                                                                   tunit1 t in
                                                               FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (279))
                                                                    (Prims.of_int (70)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (24)))))
                                                                 (Obj.magic
                                                                    uu___5)
                                                                 (fun uu___6
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (e, vs1,
                                                                    vm1) ->
                                                                    ((e ::
                                                                    es), vs1,
                                                                    vm1))))
                                                      ([], [],
                                                        (const munit def))
                                                      ts1 in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.CanonCommMonoid.fst"
                                                                (Prims.of_int (277))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (281))
                                                                (Prims.of_int (33)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.CanonCommMonoid.fst"
                                                                (Prims.of_int (272))
                                                                (Prims.of_int (65))
                                                                (Prims.of_int (282))
                                                                (Prims.of_int (30)))))
                                                       (Obj.magic uu___3)
                                                       (fun uu___4 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___5 ->
                                                               match uu___4
                                                               with
                                                               | (es, uu___6,
                                                                  vm) ->
                                                                   ((FStar_List_Tot_Base.rev
                                                                    es), vm)))))
                                                 uu___3))) uu___2))) uu___1)
let rec (term_mem :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term Prims.list ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun x ->
         fun uu___ ->
           match uu___ with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> false)))
           | hd::tl ->
               Obj.magic
                 (Obj.repr
                    (let uu___1 = FStarC_Tactics_V2_Builtins.term_eq_old hd x in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.CanonCommMonoid.fst"
                                (Prims.of_int (287)) (Prims.of_int (17))
                                (Prims.of_int (287)) (Prims.of_int (33)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.CanonCommMonoid.fst"
                                (Prims.of_int (287)) (Prims.of_int (14))
                                (Prims.of_int (287)) (Prims.of_int (62)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun uu___2 ->
                             if uu___2
                             then
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___3 -> true)))
                             else Obj.magic (Obj.repr (term_mem x tl)))
                            uu___2)))) uu___1 uu___
let (unfold_topdown :
  FStar_Tactics_NamedView.term Prims.list ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ts ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              fun s ->
                let uu___2 = term_mem s ts in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.Tactics.CanonCommMonoid.fst"
                           (Prims.of_int (291)) (Prims.of_int (5))
                           (Prims.of_int (291)) (Prims.of_int (18)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.Tactics.CanonCommMonoid.fst"
                           (Prims.of_int (291)) (Prims.of_int (4))
                           (Prims.of_int (291)) (Prims.of_int (22)))))
                  (Obj.magic uu___2)
                  (fun uu___3 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___4 -> (uu___3, Prims.int_zero))))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
               (Prims.of_int (291)) (Prims.of_int (4)) (Prims.of_int (291))
               (Prims.of_int (22)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
               (Prims.of_int (292)) (Prims.of_int (4)) (Prims.of_int (297))
               (Prims.of_int (40))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun should_rewrite ->
            let uu___1 =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      fun uu___3 ->
                        let uu___4 =
                          FStarC_Tactics_V2_Builtins.norm
                            [FStar_Pervasives.delta] in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.CanonCommMonoid.fst"
                                   (Prims.of_int (294)) (Prims.of_int (4))
                                   (Prims.of_int (294)) (Prims.of_int (16)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.CanonCommMonoid.fst"
                                   (Prims.of_int (295)) (Prims.of_int (4))
                                   (Prims.of_int (295)) (Prims.of_int (11)))))
                          (Obj.magic uu___4)
                          (fun uu___5 ->
                             (fun uu___5 ->
                                Obj.magic (FStar_Tactics_V2_Derived.trefl ()))
                               uu___5))) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.Tactics.CanonCommMonoid.fst"
                          (Prims.of_int (294)) (Prims.of_int (4))
                          (Prims.of_int (295)) (Prims.of_int (11)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.Tactics.CanonCommMonoid.fst"
                          (Prims.of_int (297)) (Prims.of_int (2))
                          (Prims.of_int (297)) (Prims.of_int (40)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun rewrite ->
                       Obj.magic
                         (FStar_Tactics_V2_Derived.topdown_rewrite
                            should_rewrite rewrite)) uu___2))) uu___1)
let rec quote_list :
  'a .
    FStar_Tactics_NamedView.term ->
      ('a ->
         (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
        ->
        'a Prims.list ->
          (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun ta ->
           fun quotea ->
             fun xs ->
               match xs with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ ->
                              FStar_Reflection_V2_Derived.mk_app
                                (FStarC_Reflection_V2_Builtins.pack_ln
                                   (FStarC_Reflection_V2_Data.Tv_FVar
                                      (FStarC_Reflection_V2_Builtins.pack_fv
                                         ["Prims"; "Nil"])))
                                [(ta, FStarC_Reflection_V2_Data.Q_Implicit)])))
               | x::xs' ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ =
                           let uu___1 =
                             let uu___2 =
                               let uu___3 = quotea x in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.CanonCommMonoid.fst"
                                          (Prims.of_int (304))
                                          (Prims.of_int (31))
                                          (Prims.of_int (304))
                                          (Prims.of_int (39)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.CanonCommMonoid.fst"
                                          (Prims.of_int (304))
                                          (Prims.of_int (30))
                                          (Prims.of_int (304))
                                          (Prims.of_int (52)))))
                                 (Obj.magic uu___3)
                                 (fun uu___4 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___5 ->
                                         (uu___4,
                                           FStarC_Reflection_V2_Data.Q_Explicit))) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.CanonCommMonoid.fst"
                                        (Prims.of_int (304))
                                        (Prims.of_int (30))
                                        (Prims.of_int (304))
                                        (Prims.of_int (52)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.CanonCommMonoid.fst"
                                        (Prims.of_int (303))
                                        (Prims.of_int (29))
                                        (Prims.of_int (305))
                                        (Prims.of_int (69)))))
                               (Obj.magic uu___2)
                               (fun uu___3 ->
                                  (fun uu___3 ->
                                     let uu___4 =
                                       let uu___5 =
                                         let uu___6 =
                                           quote_list ta quotea xs' in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                    (Prims.of_int (305))
                                                    (Prims.of_int (31))
                                                    (Prims.of_int (305))
                                                    (Prims.of_int (55)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                    (Prims.of_int (305))
                                                    (Prims.of_int (30))
                                                    (Prims.of_int (305))
                                                    (Prims.of_int (68)))))
                                           (Obj.magic uu___6)
                                           (fun uu___7 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___8 ->
                                                   (uu___7,
                                                     FStarC_Reflection_V2_Data.Q_Explicit))) in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.CanonCommMonoid.fst"
                                                  (Prims.of_int (305))
                                                  (Prims.of_int (30))
                                                  (Prims.of_int (305))
                                                  (Prims.of_int (68)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.CanonCommMonoid.fst"
                                                  (Prims.of_int (303))
                                                  (Prims.of_int (29))
                                                  (Prims.of_int (305))
                                                  (Prims.of_int (69)))))
                                         (Obj.magic uu___5)
                                         (fun uu___6 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___7 -> [uu___6])) in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.CanonCommMonoid.fst"
                                                   (Prims.of_int (303))
                                                   (Prims.of_int (29))
                                                   (Prims.of_int (305))
                                                   (Prims.of_int (69)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.CanonCommMonoid.fst"
                                                   (Prims.of_int (303))
                                                   (Prims.of_int (29))
                                                   (Prims.of_int (305))
                                                   (Prims.of_int (69)))))
                                          (Obj.magic uu___4)
                                          (fun uu___5 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___6 -> uu___3 ::
                                                  uu___5)))) uu___3) in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommMonoid.fst"
                                      (Prims.of_int (303))
                                      (Prims.of_int (29))
                                      (Prims.of_int (305))
                                      (Prims.of_int (69)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.CanonCommMonoid.fst"
                                      (Prims.of_int (303))
                                      (Prims.of_int (29))
                                      (Prims.of_int (305))
                                      (Prims.of_int (69)))))
                             (Obj.magic uu___1)
                             (fun uu___2 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 ->
                                     (ta,
                                       FStarC_Reflection_V2_Data.Q_Implicit)
                                     :: uu___2)) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommMonoid.fst"
                                    (Prims.of_int (303)) (Prims.of_int (29))
                                    (Prims.of_int (305)) (Prims.of_int (69)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommMonoid.fst"
                                    (Prims.of_int (303)) (Prims.of_int (14))
                                    (Prims.of_int (305)) (Prims.of_int (69)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   FStar_Reflection_V2_Derived.mk_app
                                     (FStarC_Reflection_V2_Builtins.pack_ln
                                        (FStarC_Reflection_V2_Data.Tv_FVar
                                           (FStarC_Reflection_V2_Builtins.pack_fv
                                              ["Prims"; "Cons"]))) uu___1)))))
          uu___2 uu___1 uu___
let quote_vm :
  'a 'b .
    FStar_Tactics_NamedView.term ->
      FStar_Tactics_NamedView.term ->
        ('a ->
           (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
          ->
          ('b ->
             (FStar_Tactics_NamedView.term, unit)
               FStar_Tactics_Effect.tac_repr)
            ->
            ('a, 'b) vmap ->
              (FStar_Tactics_NamedView.term, unit)
                FStar_Tactics_Effect.tac_repr
  =
  fun ta ->
    fun tb ->
      fun quotea ->
        fun quoteb ->
          fun vm ->
            let uu___ =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      fun p ->
                        let uu___2 =
                          let uu___3 =
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  quotea (FStar_Pervasives_Native.fst p) in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.CanonCommMonoid.fst"
                                           (Prims.of_int (311))
                                           (Prims.of_int (12))
                                           (Prims.of_int (311))
                                           (Prims.of_int (26)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.CanonCommMonoid.fst"
                                           (Prims.of_int (311))
                                           (Prims.of_int (11))
                                           (Prims.of_int (311))
                                           (Prims.of_int (39)))))
                                  (Obj.magic uu___6)
                                  (fun uu___7 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___8 ->
                                          (uu___7,
                                            FStarC_Reflection_V2_Data.Q_Explicit))) in
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.CanonCommMonoid.fst"
                                         (Prims.of_int (311))
                                         (Prims.of_int (11))
                                         (Prims.of_int (311))
                                         (Prims.of_int (39)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.CanonCommMonoid.fst"
                                         (Prims.of_int (310))
                                         (Prims.of_int (23))
                                         (Prims.of_int (311))
                                         (Prims.of_int (70)))))
                                (Obj.magic uu___5)
                                (fun uu___6 ->
                                   (fun uu___6 ->
                                      let uu___7 =
                                        let uu___8 =
                                          let uu___9 =
                                            quoteb
                                              (FStar_Pervasives_Native.snd p) in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.CanonCommMonoid.fst"
                                                     (Prims.of_int (311))
                                                     (Prims.of_int (42))
                                                     (Prims.of_int (311))
                                                     (Prims.of_int (56)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.CanonCommMonoid.fst"
                                                     (Prims.of_int (311))
                                                     (Prims.of_int (41))
                                                     (Prims.of_int (311))
                                                     (Prims.of_int (69)))))
                                            (Obj.magic uu___9)
                                            (fun uu___10 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___11 ->
                                                    (uu___10,
                                                      FStarC_Reflection_V2_Data.Q_Explicit))) in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.CanonCommMonoid.fst"
                                                   (Prims.of_int (311))
                                                   (Prims.of_int (41))
                                                   (Prims.of_int (311))
                                                   (Prims.of_int (69)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.CanonCommMonoid.fst"
                                                   (Prims.of_int (310))
                                                   (Prims.of_int (23))
                                                   (Prims.of_int (311))
                                                   (Prims.of_int (70)))))
                                          (Obj.magic uu___8)
                                          (fun uu___9 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___10 -> [uu___9])) in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                    (Prims.of_int (310))
                                                    (Prims.of_int (23))
                                                    (Prims.of_int (311))
                                                    (Prims.of_int (70)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                    (Prims.of_int (310))
                                                    (Prims.of_int (23))
                                                    (Prims.of_int (311))
                                                    (Prims.of_int (70)))))
                                           (Obj.magic uu___7)
                                           (fun uu___8 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___9 -> uu___6 ::
                                                   uu___8)))) uu___6) in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonCommMonoid.fst"
                                       (Prims.of_int (310))
                                       (Prims.of_int (23))
                                       (Prims.of_int (311))
                                       (Prims.of_int (70)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonCommMonoid.fst"
                                       (Prims.of_int (310))
                                       (Prims.of_int (23))
                                       (Prims.of_int (311))
                                       (Prims.of_int (70)))))
                              (Obj.magic uu___4)
                              (fun uu___5 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___6 ->
                                      (tb,
                                        FStarC_Reflection_V2_Data.Q_Implicit)
                                      :: uu___5)) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.CanonCommMonoid.fst"
                                     (Prims.of_int (310)) (Prims.of_int (23))
                                     (Prims.of_int (311)) (Prims.of_int (70)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.CanonCommMonoid.fst"
                                     (Prims.of_int (310)) (Prims.of_int (23))
                                     (Prims.of_int (311)) (Prims.of_int (70)))))
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___5 ->
                                    (ta,
                                      FStarC_Reflection_V2_Data.Q_Implicit)
                                    :: uu___4)) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.CanonCommMonoid.fst"
                                   (Prims.of_int (310)) (Prims.of_int (23))
                                   (Prims.of_int (311)) (Prims.of_int (70)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.CanonCommMonoid.fst"
                                   (Prims.of_int (310)) (Prims.of_int (4))
                                   (Prims.of_int (311)) (Prims.of_int (70)))))
                          (Obj.magic uu___2)
                          (fun uu___3 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___4 ->
                                  FStar_Reflection_V2_Derived.mk_app
                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                       (FStarC_Reflection_V2_Data.Tv_FVar
                                          (FStarC_Reflection_V2_Builtins.pack_fv
                                             ["FStar";
                                             "Pervasives";
                                             "Native";
                                             "Mktuple2"]))) uu___3)))) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                       (Prims.of_int (310)) (Prims.of_int (4))
                       (Prims.of_int (311)) (Prims.of_int (70)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                       (Prims.of_int (311)) (Prims.of_int (73))
                       (Prims.of_int (325)) (Prims.of_int (63)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun quote_pair ->
                    let uu___1 =
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___2 ->
                              FStar_Reflection_V2_Derived.mk_e_app
                                (FStarC_Reflection_V2_Builtins.pack_ln
                                   (FStarC_Reflection_V2_Data.Tv_FVar
                                      (FStarC_Reflection_V2_Builtins.pack_fv
                                         ["FStar";
                                         "Pervasives";
                                         "Native";
                                         "tuple2"]))) [ta; tb])) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.CanonCommMonoid.fst"
                                  (Prims.of_int (312)) (Prims.of_int (19))
                                  (Prims.of_int (312)) (Prims.of_int (45)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.CanonCommMonoid.fst"
                                  (Prims.of_int (312)) (Prims.of_int (48))
                                  (Prims.of_int (325)) (Prims.of_int (63)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            (fun t_a_star_b ->
                               let uu___2 =
                                 Obj.magic
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___3 ->
                                         fun p ->
                                           let uu___4 =
                                             let uu___5 =
                                               let uu___6 =
                                                 let uu___7 =
                                                   let uu___8 =
                                                     let uu___9 =
                                                       quote_pair
                                                         (FStar_Pervasives_Native.snd
                                                            p) in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.CanonCommMonoid.fst"
                                                                (Prims.of_int (316))
                                                                (Prims.of_int (7))
                                                                (Prims.of_int (316))
                                                                (Prims.of_int (25)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.CanonCommMonoid.fst"
                                                                (Prims.of_int (316))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (316))
                                                                (Prims.of_int (38)))))
                                                       (Obj.magic uu___9)
                                                       (fun uu___10 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___11 ->
                                                               (uu___10,
                                                                 FStarC_Reflection_V2_Data.Q_Explicit))) in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.CanonCommMonoid.fst"
                                                              (Prims.of_int (316))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (316))
                                                              (Prims.of_int (38)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.CanonCommMonoid.fst"
                                                              (Prims.of_int (314))
                                                              (Prims.of_int (23))
                                                              (Prims.of_int (316))
                                                              (Prims.of_int (39)))))
                                                     (Obj.magic uu___8)
                                                     (fun uu___9 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___10 ->
                                                             [uu___9])) in
                                                 FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.CanonCommMonoid.fst"
                                                            (Prims.of_int (314))
                                                            (Prims.of_int (23))
                                                            (Prims.of_int (316))
                                                            (Prims.of_int (39)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.CanonCommMonoid.fst"
                                                            (Prims.of_int (314))
                                                            (Prims.of_int (23))
                                                            (Prims.of_int (316))
                                                            (Prims.of_int (39)))))
                                                   (Obj.magic uu___7)
                                                   (fun uu___8 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___9 ->
                                                           ((FStar_Tactics_NamedView.pack
                                                               (FStar_Tactics_NamedView.Tv_Const
                                                                  (FStarC_Reflection_V2_Data.C_Int
                                                                    (FStar_Pervasives_Native.fst
                                                                    p)))),
                                                             FStarC_Reflection_V2_Data.Q_Explicit)
                                                           :: uu___8)) in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommMonoid.fst"
                                                          (Prims.of_int (314))
                                                          (Prims.of_int (23))
                                                          (Prims.of_int (316))
                                                          (Prims.of_int (39)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommMonoid.fst"
                                                          (Prims.of_int (314))
                                                          (Prims.of_int (23))
                                                          (Prims.of_int (316))
                                                          (Prims.of_int (39)))))
                                                 (Obj.magic uu___6)
                                                 (fun uu___7 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___8 ->
                                                         (t_a_star_b,
                                                           FStarC_Reflection_V2_Data.Q_Implicit)
                                                         :: uu___7)) in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.CanonCommMonoid.fst"
                                                        (Prims.of_int (314))
                                                        (Prims.of_int (23))
                                                        (Prims.of_int (316))
                                                        (Prims.of_int (39)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.CanonCommMonoid.fst"
                                                        (Prims.of_int (314))
                                                        (Prims.of_int (23))
                                                        (Prims.of_int (316))
                                                        (Prims.of_int (39)))))
                                               (Obj.magic uu___5)
                                               (fun uu___6 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___7 ->
                                                       ((FStarC_Reflection_V2_Builtins.pack_ln
                                                           (FStarC_Reflection_V2_Data.Tv_FVar
                                                              (FStarC_Reflection_V2_Builtins.pack_fv
                                                                 ["Prims";
                                                                 "nat"]))),
                                                         FStarC_Reflection_V2_Data.Q_Implicit)
                                                       :: uu___6)) in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.CanonCommMonoid.fst"
                                                      (Prims.of_int (314))
                                                      (Prims.of_int (23))
                                                      (Prims.of_int (316))
                                                      (Prims.of_int (39)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.CanonCommMonoid.fst"
                                                      (Prims.of_int (314))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (316))
                                                      (Prims.of_int (39)))))
                                             (Obj.magic uu___4)
                                             (fun uu___5 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___6 ->
                                                     FStar_Reflection_V2_Derived.mk_app
                                                       (FStarC_Reflection_V2_Builtins.pack_ln
                                                          (FStarC_Reflection_V2_Data.Tv_FVar
                                                             (FStarC_Reflection_V2_Builtins.pack_fv
                                                                ["FStar";
                                                                "Pervasives";
                                                                "Native";
                                                                "Mktuple2"])))
                                                       uu___5)))) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.CanonCommMonoid.fst"
                                             (Prims.of_int (314))
                                             (Prims.of_int (4))
                                             (Prims.of_int (316))
                                             (Prims.of_int (39)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.CanonCommMonoid.fst"
                                             (Prims.of_int (316))
                                             (Prims.of_int (42))
                                             (Prims.of_int (325))
                                             (Prims.of_int (63)))))
                                    (Obj.magic uu___2)
                                    (fun uu___3 ->
                                       (fun quote_map_entry ->
                                          let uu___3 =
                                            Obj.magic
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___4 ->
                                                    FStar_Reflection_V2_Derived.mk_e_app
                                                      (FStarC_Reflection_V2_Builtins.pack_ln
                                                         (FStarC_Reflection_V2_Data.Tv_FVar
                                                            (FStarC_Reflection_V2_Builtins.pack_fv
                                                               ["FStar";
                                                               "Pervasives";
                                                               "Native";
                                                               "tuple2"])))
                                                      [FStarC_Reflection_V2_Builtins.pack_ln
                                                         (FStarC_Reflection_V2_Data.Tv_FVar
                                                            (FStarC_Reflection_V2_Builtins.pack_fv
                                                               ["Prims";
                                                               "nat"]));
                                                      t_a_star_b])) in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.CanonCommMonoid.fst"
                                                        (Prims.of_int (317))
                                                        (Prims.of_int (16))
                                                        (Prims.of_int (317))
                                                        (Prims.of_int (55)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.CanonCommMonoid.fst"
                                                        (Prims.of_int (317))
                                                        (Prims.of_int (58))
                                                        (Prims.of_int (325))
                                                        (Prims.of_int (63)))))
                                               (Obj.magic uu___3)
                                               (fun uu___4 ->
                                                  (fun tyentry ->
                                                     let uu___4 =
                                                       quote_list tyentry
                                                         quote_map_entry
                                                         (FStar_Pervasives_Native.fst
                                                            vm) in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.CanonCommMonoid.fst"
                                                                   (Prims.of_int (318))
                                                                   (Prims.of_int (14))
                                                                   (Prims.of_int (318))
                                                                   (Prims.of_int (57)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.CanonCommMonoid.fst"
                                                                   (Prims.of_int (318))
                                                                   (Prims.of_int (60))
                                                                   (Prims.of_int (325))
                                                                   (Prims.of_int (63)))))
                                                          (Obj.magic uu___4)
                                                          (fun uu___5 ->
                                                             (fun tlist ->
                                                                let uu___5 =
                                                                  quote_pair
                                                                    (
                                                                    FStar_Pervasives_Native.snd
                                                                    vm) in
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (320))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (324))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun
                                                                    tpair ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Reflection_V2_Derived.mk_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "Mktuple2"])))
                                                                    [
                                                                    ((FStar_Reflection_V2_Derived.mk_e_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "list"])))
                                                                    [tyentry]),
                                                                    FStarC_Reflection_V2_Data.Q_Implicit);
                                                                    (t_a_star_b,
                                                                    FStarC_Reflection_V2_Data.Q_Implicit);
                                                                    (tlist,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit);
                                                                    (tpair,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)]))))
                                                               uu___5)))
                                                    uu___4))) uu___3)))
                              uu___2))) uu___1)
let rec (quote_exp :
  exp -> (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun e ->
       match e with
       | Unit ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar"; "Tactics"; "CanonCommMonoid"; "Unit"])))))
       | Var x ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      FStar_Reflection_V2_Derived.mk_e_app
                        (FStarC_Reflection_V2_Builtins.pack_ln
                           (FStarC_Reflection_V2_Data.Tv_FVar
                              (FStarC_Reflection_V2_Builtins.pack_fv
                                 ["FStar";
                                 "Tactics";
                                 "CanonCommMonoid";
                                 "Var"])))
                        [FStar_Tactics_NamedView.pack
                           (FStar_Tactics_NamedView.Tv_Const
                              (FStarC_Reflection_V2_Data.C_Int x))])))
       | Mult (e1, e2) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = quote_exp e1 in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.CanonCommMonoid.fst"
                              (Prims.of_int (331)) (Prims.of_int (36))
                              (Prims.of_int (331)) (Prims.of_int (48)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.CanonCommMonoid.fst"
                              (Prims.of_int (331)) (Prims.of_int (35))
                              (Prims.of_int (331)) (Prims.of_int (63)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             let uu___4 = quote_exp e2 in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.CanonCommMonoid.fst"
                                        (Prims.of_int (331))
                                        (Prims.of_int (50))
                                        (Prims.of_int (331))
                                        (Prims.of_int (62)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.CanonCommMonoid.fst"
                                        (Prims.of_int (331))
                                        (Prims.of_int (35))
                                        (Prims.of_int (331))
                                        (Prims.of_int (63)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 -> [uu___5])) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.CanonCommMonoid.fst"
                                         (Prims.of_int (331))
                                         (Prims.of_int (35))
                                         (Prims.of_int (331))
                                         (Prims.of_int (63)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.CanonCommMonoid.fst"
                                         (Prims.of_int (331))
                                         (Prims.of_int (35))
                                         (Prims.of_int (331))
                                         (Prims.of_int (63)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 -> uu___2 :: uu___4))))
                          uu___2) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.CanonCommMonoid.fst"
                            (Prims.of_int (331)) (Prims.of_int (35))
                            (Prims.of_int (331)) (Prims.of_int (63)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.CanonCommMonoid.fst"
                            (Prims.of_int (331)) (Prims.of_int (18))
                            (Prims.of_int (331)) (Prims.of_int (63)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           FStar_Reflection_V2_Derived.mk_e_app
                             (FStarC_Reflection_V2_Builtins.pack_ln
                                (FStarC_Reflection_V2_Data.Tv_FVar
                                   (FStarC_Reflection_V2_Builtins.pack_fv
                                      ["FStar";
                                      "Tactics";
                                      "CanonCommMonoid";
                                      "Mult"]))) uu___1))))) uu___
let canon_monoid_aux :
  'a 'b .
    FStar_Tactics_NamedView.term ->
      (FStar_Tactics_NamedView.term ->
         ('a, unit) FStar_Tactics_Effect.tac_repr)
        ->
        ('a ->
           (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
          ->
          FStar_Tactics_NamedView.term ->
            FStar_Tactics_NamedView.term ->
              FStar_Tactics_NamedView.term ->
                'a ->
                  FStar_Tactics_NamedView.term ->
                    ('b ->
                       (FStar_Tactics_NamedView.term, unit)
                         FStar_Tactics_Effect.tac_repr)
                      ->
                      (FStar_Tactics_NamedView.term ->
                         ('b, unit) FStar_Tactics_Effect.tac_repr)
                        ->
                        'b ->
                          FStar_Tactics_NamedView.term ->
                            FStar_Tactics_NamedView.term ->
                              (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun ta ->
    fun unquotea ->
      fun quotea ->
        fun tm ->
          fun tmult ->
            fun tunit ->
              fun munit ->
                fun tb ->
                  fun quoteb ->
                    fun f ->
                      fun def ->
                        fun tp ->
                          fun tpc ->
                            let uu___ = FStarC_Tactics_V2_Builtins.norm [] in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonCommMonoid.fst"
                                       (Prims.of_int (338))
                                       (Prims.of_int (2))
                                       (Prims.of_int (338))
                                       (Prims.of_int (9)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonCommMonoid.fst"
                                       (Prims.of_int (339))
                                       (Prims.of_int (2))
                                       (Prims.of_int (415))
                                       (Prims.of_int (42)))))
                              (Obj.magic uu___)
                              (fun uu___1 ->
                                 (fun uu___1 ->
                                    let uu___2 =
                                      let uu___3 =
                                        FStar_Tactics_V2_Derived.cur_goal () in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.CanonCommMonoid.fst"
                                                 (Prims.of_int (339))
                                                 (Prims.of_int (24))
                                                 (Prims.of_int (339))
                                                 (Prims.of_int (37)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.CanonCommMonoid.fst"
                                                 (Prims.of_int (339))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (339))
                                                 (Prims.of_int (37)))))
                                        (Obj.magic uu___3)
                                        (fun uu___4 ->
                                           (fun uu___4 ->
                                              Obj.magic
                                                (FStar_Reflection_V2_Formula.term_as_formula
                                                   uu___4)) uu___4) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.CanonCommMonoid.fst"
                                                  (Prims.of_int (339))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (339))
                                                  (Prims.of_int (37)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.CanonCommMonoid.fst"
                                                  (Prims.of_int (339))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (415))
                                                  (Prims.of_int (42)))))
                                         (Obj.magic uu___2)
                                         (fun uu___3 ->
                                            (fun uu___3 ->
                                               match uu___3 with
                                               | FStar_Reflection_V2_Formula.Comp
                                                   (FStar_Reflection_V2_Formula.Eq
                                                    (FStar_Pervasives_Native.Some
                                                    t), t1, t2)
                                                   ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (let uu___4 =
                                                           FStarC_Tactics_V2_Builtins.term_eq_old
                                                             t ta in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (25)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (69)))))
                                                           (Obj.magic uu___4)
                                                           (fun uu___5 ->
                                                              (fun uu___5 ->
                                                                 if uu___5
                                                                 then
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___6
                                                                    =
                                                                    Obj.magic
                                                                    (reification
                                                                    f def ()
                                                                    (fun
                                                                    uu___7 ->
                                                                    (Obj.magic
                                                                    unquotea)
                                                                    uu___7)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (Obj.magic
                                                                    quotea)
                                                                    uu___7)
                                                                    tmult
                                                                    tunit
                                                                    (Obj.magic
                                                                    munit)
                                                                    [t1; t2]) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (344))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (r1::r2::[],
                                                                    vm) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___8
                                                                    =
                                                                    quote_vm
                                                                    ta tb
                                                                    quotea
                                                                    quoteb vm in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun tvm
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    quote_exp
                                                                    r1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun tr1
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    quote_exp
                                                                    r2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (354))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun tr2
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Reflection_V2_Derived.mk_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "eq2"])))
                                                                    [
                                                                    (ta,
                                                                    FStarC_Reflection_V2_Data.Q_Implicit);
                                                                    ((FStar_Reflection_V2_Derived.mk_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "mdenote"])))
                                                                    [
                                                                    (ta,
                                                                    FStarC_Reflection_V2_Data.Q_Implicit);
                                                                    (tb,
                                                                    FStarC_Reflection_V2_Data.Q_Implicit);
                                                                    (tm,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit);
                                                                    (tvm,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit);
                                                                    (tr1,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)]),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit);
                                                                    ((FStar_Reflection_V2_Derived.mk_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "mdenote"])))
                                                                    [
                                                                    (ta,
                                                                    FStarC_Reflection_V2_Data.Q_Implicit);
                                                                    (tb,
                                                                    FStarC_Reflection_V2_Data.Q_Implicit);
                                                                    (tm,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit);
                                                                    (tvm,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit);
                                                                    (tr2,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)]),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun teq
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    FStar_Tactics_V2_Derived.change_sq
                                                                    teq in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (36)))))
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
                                                                    FStar_Tactics_MApply0.mapply0
                                                                    (FStar_Reflection_V2_Derived.mk_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "monoid_reflect"])))
                                                                    [
                                                                    (ta,
                                                                    FStarC_Reflection_V2_Data.Q_Implicit);
                                                                    (tb,
                                                                    FStarC_Reflection_V2_Data.Q_Implicit);
                                                                    (tp,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit);
                                                                    (tpc,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)]) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (372))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (36)))))
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
                                                                    unfold_topdown
                                                                    [
                                                                    FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "canon"]));
                                                                    FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "xsdenote"]));
                                                                    tp] in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (374))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (378))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V2_Builtins.norm
                                                                    [
                                                                    FStar_Pervasives.delta_only
                                                                    ["FStar.Tactics.CanonCommMonoid.canon";
                                                                    "FStar.Tactics.CanonCommMonoid.xsdenote";
                                                                    "FStar.Tactics.CanonCommMonoid.flatten";
                                                                    "FStar.Tactics.CanonCommMonoid.select";
                                                                    "FStar.Tactics.CanonCommMonoid.select_extra";
                                                                    "FStar.Tactics.CanonCommMonoid.quote_list";
                                                                    "FStar.Tactics.CanonCommMonoid.quote_vm";
                                                                    "FStar.Tactics.CanonCommMonoid.quote_exp";
                                                                    "FStar.Tactics.CanonCommMonoid.const_compare";
                                                                    "FStar.Tactics.CanonCommMonoid.special_compare";
                                                                    "FStar.Pervasives.Native.fst";
                                                                    "FStar.Pervasives.Native.snd";
                                                                    "FStar.Pervasives.Native.__proj__Mktuple2__item___1";
                                                                    "FStar.Pervasives.Native.__proj__Mktuple2__item___2";
                                                                    "FStar.List.Tot.Base.assoc";
                                                                    "FStar.List.Tot.Base.op_At";
                                                                    "FStar.List.Tot.Base.append";
                                                                    "SL.AutoTactic.compare_b";
                                                                    "SL.AutoTactic.compare_v";
                                                                    "FStar.Order.int_of_order";
                                                                    "FStar.Reflection.V2.Compare.compare_term";
                                                                    "FStar.List.Tot.Base.sortWith";
                                                                    "FStar.List.Tot.Base.partition";
                                                                    "FStar.List.Tot.Base.bool_of_compare";
                                                                    "FStar.List.Tot.Base.compare_of_bool"];
                                                                    FStar_Pervasives.zeta;
                                                                    FStar_Pervasives.iota;
                                                                    FStar_Pervasives.primops]))
                                                                    uu___17)))
                                                                    uu___15)))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    | 
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Unexpected")))
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
                                                           "Goal should be an equality")))
                                              uu___3))) uu___1)
let canon_monoid_with :
  'b .
    (FStar_Tactics_NamedView.term -> ('b, unit) FStar_Tactics_Effect.tac_repr)
      ->
      'b ->
        'b permute ->
          unit ->
            unit ->
              Obj.t FStar_Algebra_CommMonoid.cm ->
                (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    fun def ->
      fun p ->
        fun pc ->
          fun a ->
            fun m ->
              let uu___ =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (failwith
                                "Cannot evaluate open quotation at runtime"))
                          uu___1)) in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "FStar.Tactics.CanonCommMonoid.fst"
                         (Prims.of_int (421)) (Prims.of_int (4))
                         (Prims.of_int (421)) (Prims.of_int (13)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "FStar.Tactics.CanonCommMonoid.fst"
                         (Prims.of_int (420)) (Prims.of_int (2))
                         (Prims.of_int (423)) (Prims.of_int (86)))))
                (Obj.magic uu___)
                (fun uu___1 ->
                   (fun uu___1 ->
                      let uu___2 =
                        Obj.magic
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 ->
                                (fun uu___3 ->
                                   Obj.magic
                                     (failwith
                                        "Cannot evaluate open quotation at runtime"))
                                  uu___3)) in
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommMonoid.fst"
                                    (Prims.of_int (422)) (Prims.of_int (4))
                                    (Prims.of_int (422)) (Prims.of_int (13)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommMonoid.fst"
                                    (Prims.of_int (420)) (Prims.of_int (2))
                                    (Prims.of_int (423)) (Prims.of_int (86)))))
                           (Obj.magic uu___2)
                           (fun uu___3 ->
                              (fun uu___3 ->
                                 let uu___4 =
                                   Obj.magic
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___5 ->
                                           (fun uu___5 ->
                                              Obj.magic
                                                (failwith
                                                   "Cannot evaluate open quotation at runtime"))
                                             uu___5)) in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.CanonCommMonoid.fst"
                                               (Prims.of_int (422))
                                               (Prims.of_int (14))
                                               (Prims.of_int (422))
                                               (Prims.of_int (34)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.CanonCommMonoid.fst"
                                               (Prims.of_int (420))
                                               (Prims.of_int (2))
                                               (Prims.of_int (423))
                                               (Prims.of_int (86)))))
                                      (Obj.magic uu___4)
                                      (fun uu___5 ->
                                         (fun uu___5 ->
                                            let uu___6 =
                                              Obj.magic
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___7 ->
                                                      (fun uu___7 ->
                                                         Obj.magic
                                                           (failwith
                                                              "Cannot evaluate open quotation at runtime"))
                                                        uu___7)) in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommMonoid.fst"
                                                          (Prims.of_int (422))
                                                          (Prims.of_int (35))
                                                          (Prims.of_int (422))
                                                          (Prims.of_int (55)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommMonoid.fst"
                                                          (Prims.of_int (420))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (423))
                                                          (Prims.of_int (86)))))
                                                 (Obj.magic uu___6)
                                                 (fun uu___7 ->
                                                    (fun uu___7 ->
                                                       let uu___8 =
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___9 ->
                                                                 (fun uu___9
                                                                    ->
                                                                    Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))
                                                                   uu___9)) in
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (13)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (86)))))
                                                            (Obj.magic uu___8)
                                                            (fun uu___9 ->
                                                               (fun uu___9 ->
                                                                  let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))
                                                                    uu___11)) in
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (86)))))
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
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))
                                                                    uu___13)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (canon_monoid_aux
                                                                    uu___1
                                                                    FStarC_Tactics_V2_Builtins.unquote
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))
                                                                    uu___14)))
                                                                    uu___14)
                                                                    uu___3
                                                                    uu___5
                                                                    uu___7
                                                                    (FStar_Algebra_CommMonoid.__proj__CM__item__unit
                                                                    m) uu___9
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))
                                                                    uu___14)))
                                                                    uu___14)
                                                                    f def
                                                                    uu___11
                                                                    uu___13))
                                                                    uu___13)))
                                                                    uu___11)))
                                                                 uu___9)))
                                                      uu___7))) uu___5)))
                                uu___3))) uu___1)
let canon_monoid :
  'a .
    'a FStar_Algebra_CommMonoid.cm ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun cm ->
    canon_monoid_with
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ())))
           uu___) () (fun a1 -> sort ()) () () (Obj.magic cm)
let (is_const :
  FStar_Tactics_NamedView.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Tactics_NamedView.inspect t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
               (Prims.of_int (441)) (Prims.of_int (45)) (Prims.of_int (441))
               (Prims.of_int (56)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
               (Prims.of_int (441)) (Prims.of_int (35)) (Prims.of_int (441))
               (Prims.of_int (56))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Tactics_NamedView.uu___is_Tv_Const uu___1))
let const_compare : 'a . ('a, Prims.bool) vmap -> var -> var -> Prims.int =
  fun vm ->
    fun x ->
      fun y ->
        match ((select_extra x vm), (select_extra y vm)) with
        | (false, false) -> FStar_List_Tot_Base.compare_of_bool (<) x y
        | (true, true) -> FStar_List_Tot_Base.compare_of_bool (<) x y
        | (false, true) -> Prims.int_one
        | (true, false) -> (Prims.of_int (-1))
let const_last :
  'a . ('a, Prims.bool) vmap -> var Prims.list -> var Prims.list =
  fun vm -> fun xs -> FStar_List_Tot_Base.sortWith (const_compare vm) xs
let canon_monoid_const :
  'a .
    'a FStar_Algebra_CommMonoid.cm ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun cm ->
    canon_monoid_with is_const false (fun a1 -> const_last) () ()
      (Obj.magic cm)
let (is_special :
  FStar_Tactics_NamedView.term Prims.list ->
    FStar_Tactics_NamedView.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  = fun ts -> fun t -> term_mem t ts
let special_compare : 'a . ('a, Prims.bool) vmap -> var -> var -> Prims.int =
  fun vm ->
    fun x ->
      fun y ->
        match ((select_extra x vm), (select_extra y vm)) with
        | (false, false) -> Prims.int_zero
        | (true, true) -> FStar_List_Tot_Base.compare_of_bool (<) x y
        | (false, true) -> (Prims.of_int (-1))
        | (true, false) -> Prims.int_one
let special_first :
  'a . ('a, Prims.bool) vmap -> var Prims.list -> var Prims.list =
  fun vm -> fun xs -> FStar_List_Tot_Base.sortWith (special_compare vm) xs

let canon_monoid_special :
  'uuuuu .
    FStar_Tactics_NamedView.term Prims.list ->
      'uuuuu FStar_Algebra_CommMonoid.cm ->
        (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun ts ->
         Obj.magic
           (canon_monoid_with (is_special ts) false (fun a -> special_first)
              () ())) uu___1 uu___