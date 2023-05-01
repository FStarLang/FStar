open Prims
let (dump : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun m ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
         (Prims.of_int (32)) (Prims.of_int (24)) (Prims.of_int (32))
         (Prims.of_int (36)))
      (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
         (Prims.of_int (32)) (Prims.of_int (21)) (Prims.of_int (32))
         (Prims.of_int (48)))
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
                              "FStar.Tactics.CanonCommMonoid.fst"
                              (Prims.of_int (236)) (Prims.of_int (18))
                              (Prims.of_int (236)) (Prims.of_int (34)))
                           (FStar_Range.mk_range
                              "FStar.Tactics.CanonCommMonoid.fst"
                              (Prims.of_int (236)) (Prims.of_int (15))
                              (Prims.of_int (236)) (Prims.of_int (73)))
                           (Obj.magic
                              (FStar_Tactics_Builtins.term_eq_old x x'))
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
  'a 'b .
    (FStar_Reflection_Types.term -> ('a, unit) FStar_Tactics_Effect.tac_repr)
      ->
      FStar_Reflection_Types.term Prims.list ->
        ('a, 'b) vmap ->
          (FStar_Reflection_Types.term ->
             ('b, unit) FStar_Tactics_Effect.tac_repr)
            ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                FStar_Reflection_Types.term ->
                  ((exp * FStar_Reflection_Types.term Prims.list * ('a, 
                     'b) vmap),
                    unit) FStar_Tactics_Effect.tac_repr
  =
  fun unquotea ->
    fun ts ->
      fun vm ->
        fun f ->
          fun mult ->
            fun unit ->
              fun t ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                     (Prims.of_int (243)) (Prims.of_int (15))
                     (Prims.of_int (243)) (Prims.of_int (32)))
                  (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                     (Prims.of_int (243)) (Prims.of_int (2))
                     (Prims.of_int (260)) (Prims.of_int (21)))
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
                                    "FStar.Tactics.CanonCommMonoid.fst"
                                    (Prims.of_int (245)) (Prims.of_int (4))
                                    (Prims.of_int (248)) (Prims.of_int (62)))
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommMonoid.fst"
                                    (Prims.of_int (250)) (Prims.of_int (2))
                                    (Prims.of_int (260)) (Prims.of_int (21)))
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 ->
                                       fun t1 ->
                                         fun ts1 ->
                                           fun vm1 ->
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.CanonCommMonoid.fst"
                                                  (Prims.of_int (245))
                                                  (Prims.of_int (10))
                                                  (Prims.of_int (245))
                                                  (Prims.of_int (20)))
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.CanonCommMonoid.fst"
                                                  (Prims.of_int (245))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (248))
                                                  (Prims.of_int (62)))
                                               (Obj.magic (where t1 ts1))
                                               (fun uu___2 ->
                                                  (fun uu___2 ->
                                                     match uu___2 with
                                                     | FStar_Pervasives_Native.Some
                                                         v ->
                                                         Obj.magic
                                                           (Obj.repr
                                                              (FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___3
                                                                    ->
                                                                    ((Var v),
                                                                    ts1, vm1))))
                                                     | FStar_Pervasives_Native.None
                                                         ->
                                                         Obj.magic
                                                           (Obj.repr
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (36)))
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62)))
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    FStar_List_Tot_Base.length
                                                                    ts1))
                                                                 (fun uu___3
                                                                    ->
                                                                    (fun
                                                                    vfresh ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (58)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62)))
                                                                    (Obj.magic
                                                                    (unquotea
                                                                    t1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun z ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (61)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (62)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (58)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (248))
                                                                    (Prims.of_int (61)))
                                                                    (Obj.magic
                                                                    (f t1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    update
                                                                    vfresh z
                                                                    uu___3
                                                                    vm1))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ((Var
                                                                    vfresh),
                                                                    (FStar_List_Tot_Base.op_At
                                                                    ts1 
                                                                    [t1]),
                                                                    uu___3)))))
                                                                    uu___3)))
                                                                    uu___3))))
                                                    uu___2)))
                                 (fun uu___1 ->
                                    (fun fvar ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.CanonCommMonoid.fst"
                                               (Prims.of_int (250))
                                               (Prims.of_int (8))
                                               (Prims.of_int (250))
                                               (Prims.of_int (33)))
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.CanonCommMonoid.fst"
                                               (Prims.of_int (250))
                                               (Prims.of_int (2))
                                               (Prims.of_int (260))
                                               (Prims.of_int (21)))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.CanonCommMonoid.fst"
                                                     (Prims.of_int (250))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (250))
                                                     (Prims.of_int (18)))
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.CanonCommMonoid.fst"
                                                     (Prims.of_int (250))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (250))
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
                                                              "FStar.Tactics.CanonCommMonoid.fst"
                                                              (Prims.of_int (252))
                                                              (Prims.of_int (7))
                                                              (Prims.of_int (252))
                                                              (Prims.of_int (43)))
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.CanonCommMonoid.fst"
                                                              (Prims.of_int (252))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (256))
                                                              (Prims.of_int (21)))
                                                           (Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (38)))
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (43)))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    fv)))
                                                                 (fun uu___2
                                                                    ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.term_eq_old
                                                                    uu___2
                                                                    mult))
                                                                    uu___2)))
                                                           (fun uu___2 ->
                                                              (fun uu___2 ->
                                                                 if uu___2
                                                                 then
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (72)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (reification_aux
                                                                    unquotea
                                                                    ts vm f
                                                                    mult unit
                                                                    t1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (e1, ts1,
                                                                    vm1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (72)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (30)))
                                                                    (Obj.magic
                                                                    (reification_aux
                                                                    unquotea
                                                                    ts1 vm1 f
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
                                                                    vm2) ->
                                                                    ((Mult
                                                                    (e1, e2)),
                                                                    ts2, vm2)))))
                                                                    uu___3))
                                                                 else
                                                                   Obj.magic
                                                                    (fvar t
                                                                    ts vm))
                                                                uu___2))
                                                  | (uu___2, uu___3) ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.CanonCommMonoid.fst"
                                                              (Prims.of_int (258))
                                                              (Prims.of_int (7))
                                                              (Prims.of_int (258))
                                                              (Prims.of_int (25)))
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.CanonCommMonoid.fst"
                                                              (Prims.of_int (258))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (260))
                                                              (Prims.of_int (21)))
                                                           (Obj.magic
                                                              (FStar_Tactics_Builtins.term_eq_old
                                                                 t unit))
                                                           (fun uu___4 ->
                                                              (fun uu___4 ->
                                                                 if uu___4
                                                                 then
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    (Unit,
                                                                    ts, vm))))
                                                                 else
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (fvar t
                                                                    ts vm)))
                                                                uu___4)))
                                                 uu___1))) uu___1))) uu___)
let reification :
  'b .
    (FStar_Reflection_Types.term -> ('b, unit) FStar_Tactics_Effect.tac_repr)
      ->
      'b ->
        unit ->
          (FStar_Reflection_Types.term ->
             (Obj.t, unit) FStar_Tactics_Effect.tac_repr)
            ->
            (Obj.t ->
               (FStar_Reflection_Types.term, unit)
                 FStar_Tactics_Effect.tac_repr)
              ->
              FStar_Reflection_Types.term ->
                FStar_Reflection_Types.term ->
                  Obj.t ->
                    FStar_Reflection_Types.term Prims.list ->
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
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range
                         "FStar.Tactics.CanonCommMonoid.fst"
                         (Prims.of_int (267)) (Prims.of_int (20))
                         (Prims.of_int (267)) (Prims.of_int (53)))
                      (FStar_Range.mk_range
                         "FStar.Tactics.CanonCommMonoid.fst"
                         (Prims.of_int (268)) (Prims.of_int (2))
                         (Prims.of_int (279)) (Prims.of_int (30)))
                      (Obj.magic
                         (FStar_Tactics_Derived.norm_term
                            [FStar_Pervasives.delta;
                            FStar_Pervasives.zeta;
                            FStar_Pervasives.iota] tmult))
                      (fun uu___ ->
                         (fun tmult1 ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommMonoid.fst"
                                    (Prims.of_int (268)) (Prims.of_int (20))
                                    (Prims.of_int (268)) (Prims.of_int (53)))
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommMonoid.fst"
                                    (Prims.of_int (269)) (Prims.of_int (2))
                                    (Prims.of_int (279)) (Prims.of_int (30)))
                                 (Obj.magic
                                    (FStar_Tactics_Derived.norm_term
                                       [FStar_Pervasives.delta;
                                       FStar_Pervasives.zeta;
                                       FStar_Pervasives.iota] tunit))
                                 (fun uu___ ->
                                    (fun tunit1 ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.CanonCommMonoid.fst"
                                               (Prims.of_int (269))
                                               (Prims.of_int (13))
                                               (Prims.of_int (269))
                                               (Prims.of_int (62)))
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.CanonCommMonoid.fst"
                                               (Prims.of_int (273))
                                               (Prims.of_int (2))
                                               (Prims.of_int (279))
                                               (Prims.of_int (30)))
                                            (Obj.magic
                                               (FStar_Tactics_Util.map
                                                  (FStar_Tactics_Derived.norm_term
                                                     [FStar_Pervasives.delta;
                                                     FStar_Pervasives.zeta;
                                                     FStar_Pervasives.iota])
                                                  ts))
                                            (fun uu___ ->
                                               (fun ts1 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommMonoid.fst"
                                                          (Prims.of_int (274))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (278))
                                                          (Prims.of_int (33)))
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.CanonCommMonoid.fst"
                                                          (Prims.of_int (273))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (279))
                                                          (Prims.of_int (30)))
                                                       (Obj.magic
                                                          (FStar_Tactics_Util.fold_left
                                                             (fun uu___ ->
                                                                fun t ->
                                                                  match uu___
                                                                  with
                                                                  | (es, vs,
                                                                    vm) ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (70)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (24)))
                                                                    (Obj.magic
                                                                    (reification_aux
                                                                    unquotea
                                                                    vs vm f
                                                                    tmult1
                                                                    tunit1 t))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    (e, vs1,
                                                                    vm1) ->
                                                                    ((e ::
                                                                    es), vs1,
                                                                    vm1))))
                                                             ([], [],
                                                               (const munit
                                                                  def)) ts1))
                                                       (fun uu___ ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___1 ->
                                                               match uu___
                                                               with
                                                               | (es, uu___2,
                                                                  vm) ->
                                                                   ((FStar_List_Tot_Base.rev
                                                                    es), vm)))))
                                                 uu___))) uu___))) uu___)
let rec (term_mem :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list ->
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
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range
                          "FStar.Tactics.CanonCommMonoid.fst"
                          (Prims.of_int (284)) (Prims.of_int (17))
                          (Prims.of_int (284)) (Prims.of_int (33)))
                       (FStar_Range.mk_range
                          "FStar.Tactics.CanonCommMonoid.fst"
                          (Prims.of_int (284)) (Prims.of_int (14))
                          (Prims.of_int (284)) (Prims.of_int (62)))
                       (Obj.magic (FStar_Tactics_Builtins.term_eq_old hd x))
                       (fun uu___1 ->
                          (fun uu___1 ->
                             if uu___1
                             then
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 -> true)))
                             else Obj.magic (Obj.repr (term_mem x tl)))
                            uu___1)))) uu___1 uu___
let (unfold_topdown :
  FStar_Reflection_Types.term Prims.list ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ts ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
         (Prims.of_int (288)) (Prims.of_int (4)) (Prims.of_int (288))
         (Prims.of_int (22)))
      (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
         (Prims.of_int (290)) (Prims.of_int (2)) (Prims.of_int (294))
         (Prims.of_int (40)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ ->
            fun s ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                   (Prims.of_int (288)) (Prims.of_int (5))
                   (Prims.of_int (288)) (Prims.of_int (18)))
                (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                   (Prims.of_int (288)) (Prims.of_int (4))
                   (Prims.of_int (288)) (Prims.of_int (22)))
                (Obj.magic (term_mem s ts))
                (fun uu___1 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 -> (uu___1, Prims.int_zero)))))
      (fun uu___ ->
         (fun should_rewrite ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                    (Prims.of_int (291)) (Prims.of_int (4))
                    (Prims.of_int (292)) (Prims.of_int (11)))
                 (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                    (Prims.of_int (294)) (Prims.of_int (2))
                    (Prims.of_int (294)) (Prims.of_int (40)))
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       fun uu___1 ->
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range
                              "FStar.Tactics.CanonCommMonoid.fst"
                              (Prims.of_int (291)) (Prims.of_int (4))
                              (Prims.of_int (291)) (Prims.of_int (16)))
                           (FStar_Range.mk_range
                              "FStar.Tactics.CanonCommMonoid.fst"
                              (Prims.of_int (292)) (Prims.of_int (4))
                              (Prims.of_int (292)) (Prims.of_int (11)))
                           (Obj.magic
                              (FStar_Tactics_Builtins.norm
                                 [FStar_Pervasives.delta]))
                           (fun uu___2 ->
                              (fun uu___2 ->
                                 Obj.magic (FStar_Tactics_Derived.trefl ()))
                                uu___2)))
                 (fun uu___ ->
                    (fun rewrite ->
                       Obj.magic
                         (FStar_Tactics_Derived.topdown_rewrite
                            should_rewrite rewrite)) uu___))) uu___)
let rec quote_list :
  'a .
    FStar_Reflection_Types.term ->
      ('a ->
         (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
        ->
        'a Prims.list ->
          (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr
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
                              FStar_Reflection_Derived.mk_app
                                (FStar_Reflection_Builtins.pack_ln
                                   (FStar_Reflection_Data.Tv_FVar
                                      (FStar_Reflection_Builtins.pack_fv
                                         ["Prims"; "Nil"])))
                                [(ta, FStar_Reflection_Data.Q_Implicit)])))
               | x::xs' ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range
                              "FStar.Tactics.CanonCommMonoid.fst"
                              (Prims.of_int (300)) (Prims.of_int (29))
                              (Prims.of_int (302)) (Prims.of_int (69)))
                           (FStar_Range.mk_range
                              "FStar.Tactics.CanonCommMonoid.fst"
                              (Prims.of_int (300)) (Prims.of_int (14))
                              (Prims.of_int (302)) (Prims.of_int (69)))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommMonoid.fst"
                                    (Prims.of_int (300)) (Prims.of_int (29))
                                    (Prims.of_int (302)) (Prims.of_int (69)))
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.CanonCommMonoid.fst"
                                    (Prims.of_int (300)) (Prims.of_int (29))
                                    (Prims.of_int (302)) (Prims.of_int (69)))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.CanonCommMonoid.fst"
                                          (Prims.of_int (301))
                                          (Prims.of_int (30))
                                          (Prims.of_int (301))
                                          (Prims.of_int (52)))
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.CanonCommMonoid.fst"
                                          (Prims.of_int (300))
                                          (Prims.of_int (29))
                                          (Prims.of_int (302))
                                          (Prims.of_int (69)))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.CanonCommMonoid.fst"
                                                (Prims.of_int (301))
                                                (Prims.of_int (31))
                                                (Prims.of_int (301))
                                                (Prims.of_int (39)))
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.CanonCommMonoid.fst"
                                                (Prims.of_int (301))
                                                (Prims.of_int (30))
                                                (Prims.of_int (301))
                                                (Prims.of_int (52)))
                                             (Obj.magic (quotea x))
                                             (fun uu___ ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___1 ->
                                                     (uu___,
                                                       FStar_Reflection_Data.Q_Explicit)))))
                                       (fun uu___ ->
                                          (fun uu___ ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.CanonCommMonoid.fst"
                                                     (Prims.of_int (300))
                                                     (Prims.of_int (29))
                                                     (Prims.of_int (302))
                                                     (Prims.of_int (69)))
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.CanonCommMonoid.fst"
                                                     (Prims.of_int (300))
                                                     (Prims.of_int (29))
                                                     (Prims.of_int (302))
                                                     (Prims.of_int (69)))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.CanonCommMonoid.fst"
                                                           (Prims.of_int (302))
                                                           (Prims.of_int (30))
                                                           (Prims.of_int (302))
                                                           (Prims.of_int (68)))
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.CanonCommMonoid.fst"
                                                           (Prims.of_int (300))
                                                           (Prims.of_int (29))
                                                           (Prims.of_int (302))
                                                           (Prims.of_int (69)))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.CanonCommMonoid.fst"
                                                                 (Prims.of_int (302))
                                                                 (Prims.of_int (31))
                                                                 (Prims.of_int (302))
                                                                 (Prims.of_int (55)))
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.CanonCommMonoid.fst"
                                                                 (Prims.of_int (302))
                                                                 (Prims.of_int (30))
                                                                 (Prims.of_int (302))
                                                                 (Prims.of_int (68)))
                                                              (Obj.magic
                                                                 (quote_list
                                                                    ta quotea
                                                                    xs'))
                                                              (fun uu___1 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___2 ->
                                                                    (uu___1,
                                                                    FStar_Reflection_Data.Q_Explicit)))))
                                                        (fun uu___1 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___2 ->
                                                                [uu___1]))))
                                                  (fun uu___1 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___2 -> uu___
                                                          :: uu___1)))) uu___)))
                                 (fun uu___ ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___1 ->
                                         (ta,
                                           FStar_Reflection_Data.Q_Implicit)
                                         :: uu___))))
                           (fun uu___ ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 ->
                                   FStar_Reflection_Derived.mk_app
                                     (FStar_Reflection_Builtins.pack_ln
                                        (FStar_Reflection_Data.Tv_FVar
                                           (FStar_Reflection_Builtins.pack_fv
                                              ["Prims"; "Cons"]))) uu___)))))
          uu___2 uu___1 uu___
let quote_vm :
  'a 'b .
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        ('a ->
           (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
          ->
          ('b ->
             (FStar_Reflection_Types.term, unit)
               FStar_Tactics_Effect.tac_repr)
            ->
            ('a, 'b) vmap ->
              (FStar_Reflection_Types.term, unit)
                FStar_Tactics_Effect.tac_repr
  =
  fun ta ->
    fun tb ->
      fun quotea ->
        fun quoteb ->
          fun vm ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                 (Prims.of_int (307)) (Prims.of_int (4)) (Prims.of_int (308))
                 (Prims.of_int (70)))
              (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                 (Prims.of_int (309)) (Prims.of_int (2)) (Prims.of_int (322))
                 (Prims.of_int (63)))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    fun p ->
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range
                           "FStar.Tactics.CanonCommMonoid.fst"
                           (Prims.of_int (307)) (Prims.of_int (23))
                           (Prims.of_int (308)) (Prims.of_int (70)))
                        (FStar_Range.mk_range
                           "FStar.Tactics.CanonCommMonoid.fst"
                           (Prims.of_int (307)) (Prims.of_int (4))
                           (Prims.of_int (308)) (Prims.of_int (70)))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CanonCommMonoid.fst"
                                 (Prims.of_int (307)) (Prims.of_int (23))
                                 (Prims.of_int (308)) (Prims.of_int (70)))
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CanonCommMonoid.fst"
                                 (Prims.of_int (307)) (Prims.of_int (23))
                                 (Prims.of_int (308)) (Prims.of_int (70)))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonCommMonoid.fst"
                                       (Prims.of_int (307))
                                       (Prims.of_int (23))
                                       (Prims.of_int (308))
                                       (Prims.of_int (70)))
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonCommMonoid.fst"
                                       (Prims.of_int (307))
                                       (Prims.of_int (23))
                                       (Prims.of_int (308))
                                       (Prims.of_int (70)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.CanonCommMonoid.fst"
                                             (Prims.of_int (308))
                                             (Prims.of_int (11))
                                             (Prims.of_int (308))
                                             (Prims.of_int (39)))
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.CanonCommMonoid.fst"
                                             (Prims.of_int (307))
                                             (Prims.of_int (23))
                                             (Prims.of_int (308))
                                             (Prims.of_int (70)))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.CanonCommMonoid.fst"
                                                   (Prims.of_int (308))
                                                   (Prims.of_int (12))
                                                   (Prims.of_int (308))
                                                   (Prims.of_int (26)))
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.CanonCommMonoid.fst"
                                                   (Prims.of_int (308))
                                                   (Prims.of_int (11))
                                                   (Prims.of_int (308))
                                                   (Prims.of_int (39)))
                                                (Obj.magic
                                                   (quotea
                                                      (FStar_Pervasives_Native.fst
                                                         p)))
                                                (fun uu___1 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        (uu___1,
                                                          FStar_Reflection_Data.Q_Explicit)))))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.CanonCommMonoid.fst"
                                                        (Prims.of_int (307))
                                                        (Prims.of_int (23))
                                                        (Prims.of_int (308))
                                                        (Prims.of_int (70)))
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.CanonCommMonoid.fst"
                                                        (Prims.of_int (307))
                                                        (Prims.of_int (23))
                                                        (Prims.of_int (308))
                                                        (Prims.of_int (70)))
                                                     (Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.CanonCommMonoid.fst"
                                                              (Prims.of_int (308))
                                                              (Prims.of_int (41))
                                                              (Prims.of_int (308))
                                                              (Prims.of_int (69)))
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.CanonCommMonoid.fst"
                                                              (Prims.of_int (307))
                                                              (Prims.of_int (23))
                                                              (Prims.of_int (308))
                                                              (Prims.of_int (70)))
                                                           (Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (56)))
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (69)))
                                                                 (Obj.magic
                                                                    (
                                                                    quoteb
                                                                    (FStar_Pervasives_Native.snd
                                                                    p)))
                                                                 (fun uu___2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (uu___2,
                                                                    FStar_Reflection_Data.Q_Explicit)))))
                                                           (fun uu___2 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___3
                                                                   ->
                                                                   [uu___2]))))
                                                     (fun uu___2 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___3 ->
                                                             uu___1 :: uu___2))))
                                               uu___1)))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            (tb,
                                              FStar_Reflection_Data.Q_Implicit)
                                            :: uu___1))))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 ->
                                      (ta, FStar_Reflection_Data.Q_Implicit)
                                      :: uu___1))))
                        (fun uu___1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 ->
                                FStar_Reflection_Derived.mk_app
                                  (FStar_Reflection_Builtins.pack_ln
                                     (FStar_Reflection_Data.Tv_FVar
                                        (FStar_Reflection_Builtins.pack_fv
                                           ["FStar";
                                           "Pervasives";
                                           "Native";
                                           "Mktuple2"]))) uu___1))))
              (fun uu___ ->
                 (fun quote_pair ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range
                            "FStar.Tactics.CanonCommMonoid.fst"
                            (Prims.of_int (309)) (Prims.of_int (19))
                            (Prims.of_int (309)) (Prims.of_int (45)))
                         (FStar_Range.mk_range
                            "FStar.Tactics.CanonCommMonoid.fst"
                            (Prims.of_int (310)) (Prims.of_int (2))
                            (Prims.of_int (322)) (Prims.of_int (63)))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ ->
                               FStar_Reflection_Derived.mk_e_app
                                 (FStar_Reflection_Builtins.pack_ln
                                    (FStar_Reflection_Data.Tv_FVar
                                       (FStar_Reflection_Builtins.pack_fv
                                          ["FStar";
                                          "Pervasives";
                                          "Native";
                                          "tuple2"]))) [ta; tb]))
                         (fun uu___ ->
                            (fun t_a_star_b ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonCommMonoid.fst"
                                       (Prims.of_int (311))
                                       (Prims.of_int (4))
                                       (Prims.of_int (313))
                                       (Prims.of_int (39)))
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonCommMonoid.fst"
                                       (Prims.of_int (314))
                                       (Prims.of_int (2))
                                       (Prims.of_int (322))
                                       (Prims.of_int (63)))
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___ ->
                                          fun p ->
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.CanonCommMonoid.fst"
                                                 (Prims.of_int (311))
                                                 (Prims.of_int (23))
                                                 (Prims.of_int (313))
                                                 (Prims.of_int (39)))
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.CanonCommMonoid.fst"
                                                 (Prims.of_int (311))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (313))
                                                 (Prims.of_int (39)))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.CanonCommMonoid.fst"
                                                       (Prims.of_int (311))
                                                       (Prims.of_int (23))
                                                       (Prims.of_int (313))
                                                       (Prims.of_int (39)))
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.CanonCommMonoid.fst"
                                                       (Prims.of_int (311))
                                                       (Prims.of_int (23))
                                                       (Prims.of_int (313))
                                                       (Prims.of_int (39)))
                                                    (Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.CanonCommMonoid.fst"
                                                             (Prims.of_int (311))
                                                             (Prims.of_int (23))
                                                             (Prims.of_int (313))
                                                             (Prims.of_int (39)))
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.CanonCommMonoid.fst"
                                                             (Prims.of_int (311))
                                                             (Prims.of_int (23))
                                                             (Prims.of_int (313))
                                                             (Prims.of_int (39)))
                                                          (Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.CanonCommMonoid.fst"
                                                                   (Prims.of_int (312))
                                                                   (Prims.of_int (6))
                                                                   (Prims.of_int (312))
                                                                   (Prims.of_int (51)))
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.CanonCommMonoid.fst"
                                                                   (Prims.of_int (311))
                                                                   (Prims.of_int (23))
                                                                   (Prims.of_int (313))
                                                                   (Prims.of_int (39)))
                                                                (Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (38)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (51)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_Const
                                                                    (FStar_Reflection_Data.C_Int
                                                                    (FStar_Pervasives_Native.fst
                                                                    p)))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    (uu___1,
                                                                    FStar_Reflection_Data.Q_Explicit)))))
                                                                (fun uu___1
                                                                   ->
                                                                   (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (38)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (39)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (25)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (38)))
                                                                    (Obj.magic
                                                                    (quote_pair
                                                                    (FStar_Pervasives_Native.snd
                                                                    p)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (uu___2,
                                                                    FStar_Reflection_Data.Q_Explicit)))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    [uu___2]))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    uu___1 ::
                                                                    uu___2))))
                                                                    uu___1)))
                                                          (fun uu___1 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___2 ->
                                                                  (t_a_star_b,
                                                                    FStar_Reflection_Data.Q_Implicit)
                                                                  :: uu___1))))
                                                    (fun uu___1 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___2 ->
                                                            ((FStar_Reflection_Builtins.pack_ln
                                                                (FStar_Reflection_Data.Tv_FVar
                                                                   (FStar_Reflection_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "nat"]))),
                                                              FStar_Reflection_Data.Q_Implicit)
                                                            :: uu___1))))
                                              (fun uu___1 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___2 ->
                                                      FStar_Reflection_Derived.mk_app
                                                        (FStar_Reflection_Builtins.pack_ln
                                                           (FStar_Reflection_Data.Tv_FVar
                                                              (FStar_Reflection_Builtins.pack_fv
                                                                 ["FStar";
                                                                 "Pervasives";
                                                                 "Native";
                                                                 "Mktuple2"])))
                                                        uu___1))))
                                    (fun uu___ ->
                                       (fun quote_map_entry ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.CanonCommMonoid.fst"
                                                  (Prims.of_int (314))
                                                  (Prims.of_int (16))
                                                  (Prims.of_int (314))
                                                  (Prims.of_int (55)))
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.CanonCommMonoid.fst"
                                                  (Prims.of_int (315))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (322))
                                                  (Prims.of_int (63)))
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___ ->
                                                     FStar_Reflection_Derived.mk_e_app
                                                       (FStar_Reflection_Builtins.pack_ln
                                                          (FStar_Reflection_Data.Tv_FVar
                                                             (FStar_Reflection_Builtins.pack_fv
                                                                ["FStar";
                                                                "Pervasives";
                                                                "Native";
                                                                "tuple2"])))
                                                       [FStar_Reflection_Builtins.pack_ln
                                                          (FStar_Reflection_Data.Tv_FVar
                                                             (FStar_Reflection_Builtins.pack_fv
                                                                ["Prims";
                                                                "nat"]));
                                                       t_a_star_b]))
                                               (fun uu___ ->
                                                  (fun tyentry ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.CanonCommMonoid.fst"
                                                             (Prims.of_int (315))
                                                             (Prims.of_int (14))
                                                             (Prims.of_int (315))
                                                             (Prims.of_int (57)))
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.CanonCommMonoid.fst"
                                                             (Prims.of_int (317))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (322))
                                                             (Prims.of_int (63)))
                                                          (Obj.magic
                                                             (quote_list
                                                                tyentry
                                                                quote_map_entry
                                                                (FStar_Pervasives_Native.fst
                                                                   vm)))
                                                          (fun uu___ ->
                                                             (fun tlist ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (33)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (321))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (63)))
                                                                    (Obj.magic
                                                                    (quote_pair
                                                                    (FStar_Pervasives_Native.snd
                                                                    vm)))
                                                                    (fun
                                                                    tpair ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___ ->
                                                                    FStar_Reflection_Derived.mk_app
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Native";
                                                                    "Mktuple2"])))
                                                                    [
                                                                    ((FStar_Reflection_Derived.mk_e_app
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "list"])))
                                                                    [tyentry]),
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (t_a_star_b,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (tlist,
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    (tpair,
                                                                    FStar_Reflection_Data.Q_Explicit)]))))
                                                               uu___))) uu___)))
                                         uu___))) uu___))) uu___)
let rec (quote_exp :
  exp -> (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    (fun e ->
       match e with
       | Unit ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      FStar_Reflection_Builtins.pack_ln
                        (FStar_Reflection_Data.Tv_FVar
                           (FStar_Reflection_Builtins.pack_fv
                              ["FStar"; "Tactics"; "CanonCommMonoid"; "Unit"])))))
       | Var x ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                      (Prims.of_int (327)) (Prims.of_int (29))
                      (Prims.of_int (327)) (Prims.of_int (56)))
                   (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                      (Prims.of_int (327)) (Prims.of_int (13))
                      (Prims.of_int (327)) (Prims.of_int (56)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range
                            "FStar.Tactics.CanonCommMonoid.fst"
                            (Prims.of_int (327)) (Prims.of_int (30))
                            (Prims.of_int (327)) (Prims.of_int (55)))
                         (FStar_Range.mk_range
                            "FStar.Tactics.CanonCommMonoid.fst"
                            (Prims.of_int (327)) (Prims.of_int (29))
                            (Prims.of_int (327)) (Prims.of_int (56)))
                         (Obj.magic
                            (FStar_Tactics_Builtins.pack
                               (FStar_Reflection_Data.Tv_Const
                                  (FStar_Reflection_Data.C_Int x))))
                         (fun uu___ ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> [uu___]))))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           FStar_Reflection_Derived.mk_e_app
                             (FStar_Reflection_Builtins.pack_ln
                                (FStar_Reflection_Data.Tv_FVar
                                   (FStar_Reflection_Builtins.pack_fv
                                      ["FStar";
                                      "Tactics";
                                      "CanonCommMonoid";
                                      "Var"]))) uu___))))
       | Mult (e1, e2) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                      (Prims.of_int (328)) (Prims.of_int (35))
                      (Prims.of_int (328)) (Prims.of_int (63)))
                   (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                      (Prims.of_int (328)) (Prims.of_int (18))
                      (Prims.of_int (328)) (Prims.of_int (63)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range
                            "FStar.Tactics.CanonCommMonoid.fst"
                            (Prims.of_int (328)) (Prims.of_int (36))
                            (Prims.of_int (328)) (Prims.of_int (48)))
                         (FStar_Range.mk_range
                            "FStar.Tactics.CanonCommMonoid.fst"
                            (Prims.of_int (328)) (Prims.of_int (35))
                            (Prims.of_int (328)) (Prims.of_int (63)))
                         (Obj.magic (quote_exp e1))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonCommMonoid.fst"
                                       (Prims.of_int (328))
                                       (Prims.of_int (35))
                                       (Prims.of_int (328))
                                       (Prims.of_int (63)))
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonCommMonoid.fst"
                                       (Prims.of_int (328))
                                       (Prims.of_int (35))
                                       (Prims.of_int (328))
                                       (Prims.of_int (63)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.CanonCommMonoid.fst"
                                             (Prims.of_int (328))
                                             (Prims.of_int (50))
                                             (Prims.of_int (328))
                                             (Prims.of_int (62)))
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.CanonCommMonoid.fst"
                                             (Prims.of_int (328))
                                             (Prims.of_int (35))
                                             (Prims.of_int (328))
                                             (Prims.of_int (63)))
                                          (Obj.magic (quote_exp e2))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 -> [uu___1]))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 -> uu___ :: uu___1))))
                              uu___)))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           FStar_Reflection_Derived.mk_e_app
                             (FStar_Reflection_Builtins.pack_ln
                                (FStar_Reflection_Data.Tv_FVar
                                   (FStar_Reflection_Builtins.pack_fv
                                      ["FStar";
                                      "Tactics";
                                      "CanonCommMonoid";
                                      "Mult"]))) uu___))))) uu___
let canon_monoid_aux :
  'a 'b .
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term ->
         ('a, unit) FStar_Tactics_Effect.tac_repr)
        ->
        ('a ->
           (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
          ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.term ->
              FStar_Reflection_Types.term ->
                'a ->
                  FStar_Reflection_Types.term ->
                    ('b ->
                       (FStar_Reflection_Types.term, unit)
                         FStar_Tactics_Effect.tac_repr)
                      ->
                      (FStar_Reflection_Types.term ->
                         ('b, unit) FStar_Tactics_Effect.tac_repr)
                        ->
                        'b ->
                          FStar_Reflection_Types.term ->
                            FStar_Reflection_Types.term ->
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
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CanonCommMonoid.fst"
                                 (Prims.of_int (335)) (Prims.of_int (2))
                                 (Prims.of_int (335)) (Prims.of_int (9)))
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CanonCommMonoid.fst"
                                 (Prims.of_int (336)) (Prims.of_int (2))
                                 (Prims.of_int (412)) (Prims.of_int (42)))
                              (Obj.magic (FStar_Tactics_Builtins.norm []))
                              (fun uu___ ->
                                 (fun uu___ ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.CanonCommMonoid.fst"
                                            (Prims.of_int (336))
                                            (Prims.of_int (8))
                                            (Prims.of_int (336))
                                            (Prims.of_int (37)))
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.CanonCommMonoid.fst"
                                            (Prims.of_int (336))
                                            (Prims.of_int (2))
                                            (Prims.of_int (412))
                                            (Prims.of_int (42)))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.CanonCommMonoid.fst"
                                                  (Prims.of_int (336))
                                                  (Prims.of_int (24))
                                                  (Prims.of_int (336))
                                                  (Prims.of_int (37)))
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.CanonCommMonoid.fst"
                                                  (Prims.of_int (336))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (336))
                                                  (Prims.of_int (37)))
                                               (Obj.magic
                                                  (FStar_Tactics_Derived.cur_goal
                                                     ()))
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
                                                    (FStar_Pervasives_Native.Some
                                                    t), t1, t2)
                                                   ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.CanonCommMonoid.fst"
                                                              (Prims.of_int (340))
                                                              (Prims.of_int (9))
                                                              (Prims.of_int (340))
                                                              (Prims.of_int (25)))
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.CanonCommMonoid.fst"
                                                              (Prims.of_int (340))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (411))
                                                              (Prims.of_int (69)))
                                                           (Obj.magic
                                                              (FStar_Tactics_Builtins.term_eq_old
                                                                 t ta))
                                                           (fun uu___2 ->
                                                              (fun uu___2 ->
                                                                 if uu___2
                                                                 then
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (75)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (32)))
                                                                    (Obj.magic
                                                                    (reification
                                                                    f def ()
                                                                    (fun
                                                                    uu___3 ->
                                                                    (Obj.magic
                                                                    unquotea)
                                                                    uu___3)
                                                                    (fun
                                                                    uu___3 ->
                                                                    (Obj.magic
                                                                    quotea)
                                                                    uu___3)
                                                                    tmult
                                                                    tunit
                                                                    (Obj.magic
                                                                    munit)
                                                                    [t1; t2]))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (r1::r2::[],
                                                                    vm) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (349))
                                                                    (Prims.of_int (51)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (36)))
                                                                    (Obj.magic
                                                                    (quote_vm
                                                                    ta tb
                                                                    quotea
                                                                    quoteb vm))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun tvm
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (32)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (36)))
                                                                    (Obj.magic
                                                                    (quote_exp
                                                                    r1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun tr1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (32)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (36)))
                                                                    (Obj.magic
                                                                    (quote_exp
                                                                    r2))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun tr2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (83)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (36)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Reflection_Derived.mk_app
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "eq2"])))
                                                                    [
                                                                    (ta,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    ((FStar_Reflection_Derived.mk_app
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "mdenote"])))
                                                                    [
                                                                    (ta,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (tb,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (tm,
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    (tvm,
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    (tr1,
                                                                    FStar_Reflection_Data.Q_Explicit)]),
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    ((FStar_Reflection_Derived.mk_app
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "mdenote"])))
                                                                    [
                                                                    (ta,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (tb,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (tm,
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    (tvm,
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    (tr2,
                                                                    FStar_Reflection_Data.Q_Explicit)]),
                                                                    FStar_Reflection_Data.Q_Explicit)]))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun teq
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (23)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (366))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (36)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.change_sq
                                                                    teq))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (366))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (63)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (36)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.mapply
                                                                    (FStar_Reflection_Derived.mk_app
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "monoid_reflect"])))
                                                                    [
                                                                    (ta,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (tb,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (tp,
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    (tpc,
                                                                    FStar_Reflection_Data.Q_Explicit)])))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (52)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (36)))
                                                                    (Obj.magic
                                                                    (unfold_topdown
                                                                    [
                                                                    FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "canon"]));
                                                                    FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonCommMonoid";
                                                                    "xsdenote"]));
                                                                    tp]))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.norm
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
                                                                    "FStar.Reflection.Compare.compare_term";
                                                                    "FStar.List.Tot.Base.sortWith";
                                                                    "FStar.List.Tot.Base.partition";
                                                                    "FStar.List.Tot.Base.bool_of_compare";
                                                                    "FStar.List.Tot.Base.compare_of_bool"];
                                                                    FStar_Pervasives.zeta;
                                                                    FStar_Pervasives.iota;
                                                                    FStar_Pervasives.primops]))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "Unexpected")))
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
                                                           "Goal should be an equality")))
                                              uu___1))) uu___)
let canon_monoid_with :
  'b .
    (FStar_Reflection_Types.term -> ('b, unit) FStar_Tactics_Effect.tac_repr)
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
              FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                   (Prims.of_int (418)) (Prims.of_int (4))
                   (Prims.of_int (418)) (Prims.of_int (13)))
                (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
                   (Prims.of_int (417)) (Prims.of_int (2))
                   (Prims.of_int (420)) (Prims.of_int (86)))
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
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range
                              "FStar.Tactics.CanonCommMonoid.fst"
                              (Prims.of_int (419)) (Prims.of_int (4))
                              (Prims.of_int (419)) (Prims.of_int (13)))
                           (FStar_Range.mk_range
                              "FStar.Tactics.CanonCommMonoid.fst"
                              (Prims.of_int (417)) (Prims.of_int (2))
                              (Prims.of_int (420)) (Prims.of_int (86)))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 (fun uu___1 ->
                                    Obj.magic
                                      (failwith
                                         "Cannot evaluate open quotation at runtime"))
                                   uu___1))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.CanonCommMonoid.fst"
                                         (Prims.of_int (419))
                                         (Prims.of_int (14))
                                         (Prims.of_int (419))
                                         (Prims.of_int (34)))
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.CanonCommMonoid.fst"
                                         (Prims.of_int (417))
                                         (Prims.of_int (2))
                                         (Prims.of_int (420))
                                         (Prims.of_int (86)))
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            (fun uu___2 ->
                                               Obj.magic
                                                 (failwith
                                                    "Cannot evaluate open quotation at runtime"))
                                              uu___2))
                                      (fun uu___2 ->
                                         (fun uu___2 ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                    (Prims.of_int (419))
                                                    (Prims.of_int (35))
                                                    (Prims.of_int (419))
                                                    (Prims.of_int (55)))
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                    (Prims.of_int (417))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (420))
                                                    (Prims.of_int (86)))
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___3 ->
                                                       (fun uu___3 ->
                                                          Obj.magic
                                                            (failwith
                                                               "Cannot evaluate open quotation at runtime"))
                                                         uu___3))
                                                 (fun uu___3 ->
                                                    (fun uu___3 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.CanonCommMonoid.fst"
                                                               (Prims.of_int (420))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (420))
                                                               (Prims.of_int (13)))
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.CanonCommMonoid.fst"
                                                               (Prims.of_int (417))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (420))
                                                               (Prims.of_int (86)))
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___4 ->
                                                                  (fun uu___4
                                                                    ->
                                                                    Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))
                                                                    uu___4))
                                                            (fun uu___4 ->
                                                               (fun uu___4 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (52)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (86)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))
                                                                    uu___5))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (86)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonCommMonoid.fst"
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (86)))
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
                                                                    (canon_monoid_aux
                                                                    uu___
                                                                    FStar_Tactics_Builtins.unquote
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))
                                                                    uu___7)))
                                                                    uu___7)
                                                                    uu___1
                                                                    uu___2
                                                                    uu___3
                                                                    (FStar_Algebra_CommMonoid.__proj__CM__item__unit
                                                                    m) uu___4
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))
                                                                    uu___7)))
                                                                    uu___7) f
                                                                    def
                                                                    uu___5
                                                                    uu___6))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                 uu___4)))
                                                      uu___3))) uu___2)))
                                uu___1))) uu___)
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
  FStar_Reflection_Types.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
         (Prims.of_int (438)) (Prims.of_int (45)) (Prims.of_int (438))
         (Prims.of_int (56)))
      (FStar_Range.mk_range "FStar.Tactics.CanonCommMonoid.fst"
         (Prims.of_int (438)) (Prims.of_int (35)) (Prims.of_int (438))
         (Prims.of_int (56))) (Obj.magic (FStar_Tactics_Builtins.inspect t))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_Reflection_Data.uu___is_Tv_Const uu___))
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
  FStar_Reflection_Types.term Prims.list ->
    FStar_Reflection_Types.term ->
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
    FStar_Reflection_Types.term Prims.list ->
      'uuuuu FStar_Algebra_CommMonoid.cm ->
        (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun ts ->
         Obj.magic
           (canon_monoid_with (is_special ts) false (fun a -> special_first)
              () ())) uu___1 uu___
