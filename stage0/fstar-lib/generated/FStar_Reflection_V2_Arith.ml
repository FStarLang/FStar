open Prims
type expr =
  | Lit of Prims.int 
  | Atom of Prims.nat * FStarC_Reflection_Types.term 
  | Plus of expr * expr 
  | Mult of expr * expr 
  | Minus of expr * expr 
  | Land of expr * expr 
  | Lxor of expr * expr 
  | Lor of expr * expr 
  | Ladd of expr * expr 
  | Lsub of expr * expr 
  | Shl of expr * expr 
  | Shr of expr * expr 
  | Neg of expr 
  | Udiv of expr * expr 
  | Umod of expr * expr 
  | MulMod of expr * expr 
  | NatToBv of expr 
let (uu___is_Lit : expr -> Prims.bool) =
  fun projectee -> match projectee with | Lit _0 -> true | uu___ -> false
let (__proj__Lit__item___0 : expr -> Prims.int) =
  fun projectee -> match projectee with | Lit _0 -> _0
let (uu___is_Atom : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Atom (_0, _1) -> true | uu___ -> false
let (__proj__Atom__item___0 : expr -> Prims.nat) =
  fun projectee -> match projectee with | Atom (_0, _1) -> _0
let (__proj__Atom__item___1 : expr -> FStarC_Reflection_Types.term) =
  fun projectee -> match projectee with | Atom (_0, _1) -> _1
let (uu___is_Plus : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Plus (_0, _1) -> true | uu___ -> false
let (__proj__Plus__item___0 : expr -> expr) =
  fun projectee -> match projectee with | Plus (_0, _1) -> _0
let (__proj__Plus__item___1 : expr -> expr) =
  fun projectee -> match projectee with | Plus (_0, _1) -> _1
let (uu___is_Mult : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Mult (_0, _1) -> true | uu___ -> false
let (__proj__Mult__item___0 : expr -> expr) =
  fun projectee -> match projectee with | Mult (_0, _1) -> _0
let (__proj__Mult__item___1 : expr -> expr) =
  fun projectee -> match projectee with | Mult (_0, _1) -> _1
let (uu___is_Minus : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Minus (_0, _1) -> true | uu___ -> false
let (__proj__Minus__item___0 : expr -> expr) =
  fun projectee -> match projectee with | Minus (_0, _1) -> _0
let (__proj__Minus__item___1 : expr -> expr) =
  fun projectee -> match projectee with | Minus (_0, _1) -> _1
let (uu___is_Land : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Land (_0, _1) -> true | uu___ -> false
let (__proj__Land__item___0 : expr -> expr) =
  fun projectee -> match projectee with | Land (_0, _1) -> _0
let (__proj__Land__item___1 : expr -> expr) =
  fun projectee -> match projectee with | Land (_0, _1) -> _1
let (uu___is_Lxor : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Lxor (_0, _1) -> true | uu___ -> false
let (__proj__Lxor__item___0 : expr -> expr) =
  fun projectee -> match projectee with | Lxor (_0, _1) -> _0
let (__proj__Lxor__item___1 : expr -> expr) =
  fun projectee -> match projectee with | Lxor (_0, _1) -> _1
let (uu___is_Lor : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Lor (_0, _1) -> true | uu___ -> false
let (__proj__Lor__item___0 : expr -> expr) =
  fun projectee -> match projectee with | Lor (_0, _1) -> _0
let (__proj__Lor__item___1 : expr -> expr) =
  fun projectee -> match projectee with | Lor (_0, _1) -> _1
let (uu___is_Ladd : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Ladd (_0, _1) -> true | uu___ -> false
let (__proj__Ladd__item___0 : expr -> expr) =
  fun projectee -> match projectee with | Ladd (_0, _1) -> _0
let (__proj__Ladd__item___1 : expr -> expr) =
  fun projectee -> match projectee with | Ladd (_0, _1) -> _1
let (uu___is_Lsub : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Lsub (_0, _1) -> true | uu___ -> false
let (__proj__Lsub__item___0 : expr -> expr) =
  fun projectee -> match projectee with | Lsub (_0, _1) -> _0
let (__proj__Lsub__item___1 : expr -> expr) =
  fun projectee -> match projectee with | Lsub (_0, _1) -> _1
let (uu___is_Shl : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Shl (_0, _1) -> true | uu___ -> false
let (__proj__Shl__item___0 : expr -> expr) =
  fun projectee -> match projectee with | Shl (_0, _1) -> _0
let (__proj__Shl__item___1 : expr -> expr) =
  fun projectee -> match projectee with | Shl (_0, _1) -> _1
let (uu___is_Shr : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Shr (_0, _1) -> true | uu___ -> false
let (__proj__Shr__item___0 : expr -> expr) =
  fun projectee -> match projectee with | Shr (_0, _1) -> _0
let (__proj__Shr__item___1 : expr -> expr) =
  fun projectee -> match projectee with | Shr (_0, _1) -> _1
let (uu___is_Neg : expr -> Prims.bool) =
  fun projectee -> match projectee with | Neg _0 -> true | uu___ -> false
let (__proj__Neg__item___0 : expr -> expr) =
  fun projectee -> match projectee with | Neg _0 -> _0
let (uu___is_Udiv : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Udiv (_0, _1) -> true | uu___ -> false
let (__proj__Udiv__item___0 : expr -> expr) =
  fun projectee -> match projectee with | Udiv (_0, _1) -> _0
let (__proj__Udiv__item___1 : expr -> expr) =
  fun projectee -> match projectee with | Udiv (_0, _1) -> _1
let (uu___is_Umod : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Umod (_0, _1) -> true | uu___ -> false
let (__proj__Umod__item___0 : expr -> expr) =
  fun projectee -> match projectee with | Umod (_0, _1) -> _0
let (__proj__Umod__item___1 : expr -> expr) =
  fun projectee -> match projectee with | Umod (_0, _1) -> _1
let (uu___is_MulMod : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | MulMod (_0, _1) -> true | uu___ -> false
let (__proj__MulMod__item___0 : expr -> expr) =
  fun projectee -> match projectee with | MulMod (_0, _1) -> _0
let (__proj__MulMod__item___1 : expr -> expr) =
  fun projectee -> match projectee with | MulMod (_0, _1) -> _1
let (uu___is_NatToBv : expr -> Prims.bool) =
  fun projectee -> match projectee with | NatToBv _0 -> true | uu___ -> false
let (__proj__NatToBv__item___0 : expr -> expr) =
  fun projectee -> match projectee with | NatToBv _0 -> _0
type connective =
  | C_Lt 
  | C_Eq 
  | C_Gt 
  | C_Ne 
let (uu___is_C_Lt : connective -> Prims.bool) =
  fun projectee -> match projectee with | C_Lt -> true | uu___ -> false
let (uu___is_C_Eq : connective -> Prims.bool) =
  fun projectee -> match projectee with | C_Eq -> true | uu___ -> false
let (uu___is_C_Gt : connective -> Prims.bool) =
  fun projectee -> match projectee with | C_Gt -> true | uu___ -> false
let (uu___is_C_Ne : connective -> Prims.bool) =
  fun projectee -> match projectee with | C_Ne -> true | uu___ -> false
type prop =
  | CompProp of expr * connective * expr 
  | AndProp of prop * prop 
  | OrProp of prop * prop 
  | NotProp of prop 
let (uu___is_CompProp : prop -> Prims.bool) =
  fun projectee ->
    match projectee with | CompProp (_0, _1, _2) -> true | uu___ -> false
let (__proj__CompProp__item___0 : prop -> expr) =
  fun projectee -> match projectee with | CompProp (_0, _1, _2) -> _0
let (__proj__CompProp__item___1 : prop -> connective) =
  fun projectee -> match projectee with | CompProp (_0, _1, _2) -> _1
let (__proj__CompProp__item___2 : prop -> expr) =
  fun projectee -> match projectee with | CompProp (_0, _1, _2) -> _2
let (uu___is_AndProp : prop -> Prims.bool) =
  fun projectee ->
    match projectee with | AndProp (_0, _1) -> true | uu___ -> false
let (__proj__AndProp__item___0 : prop -> prop) =
  fun projectee -> match projectee with | AndProp (_0, _1) -> _0
let (__proj__AndProp__item___1 : prop -> prop) =
  fun projectee -> match projectee with | AndProp (_0, _1) -> _1
let (uu___is_OrProp : prop -> Prims.bool) =
  fun projectee ->
    match projectee with | OrProp (_0, _1) -> true | uu___ -> false
let (__proj__OrProp__item___0 : prop -> prop) =
  fun projectee -> match projectee with | OrProp (_0, _1) -> _0
let (__proj__OrProp__item___1 : prop -> prop) =
  fun projectee -> match projectee with | OrProp (_0, _1) -> _1
let (uu___is_NotProp : prop -> Prims.bool) =
  fun projectee -> match projectee with | NotProp _0 -> true | uu___ -> false
let (__proj__NotProp__item___0 : prop -> prop) =
  fun projectee -> match projectee with | NotProp _0 -> _0
let (lt : expr -> expr -> prop) = fun e1 -> fun e2 -> CompProp (e1, C_Lt, e2)
let (le : expr -> expr -> prop) =
  fun e1 -> fun e2 -> CompProp (e1, C_Lt, (Plus ((Lit Prims.int_one), e2)))
let (eq : expr -> expr -> prop) = fun e1 -> fun e2 -> CompProp (e1, C_Eq, e2)
let (ne : expr -> expr -> prop) = fun e1 -> fun e2 -> CompProp (e1, C_Ne, e2)
let (gt : expr -> expr -> prop) = fun e1 -> fun e2 -> CompProp (e1, C_Gt, e2)
let (ge : expr -> expr -> prop) =
  fun e1 -> fun e2 -> CompProp ((Plus ((Lit Prims.int_one), e1)), C_Gt, e2)
type st = (Prims.nat * FStarC_Reflection_Types.term Prims.list)
type 'a tm =
  st ->
    ((Prims.string, ('a * st)) FStar_Pervasives.either, unit)
      FStar_Tactics_Effect.tac_repr
let return : 'a . 'a -> 'a tm =
  fun uu___ ->
    (fun x ->
       fun i ->
         Obj.magic
           (FStar_Tactics_Effect.lift_div_tac
              (fun uu___ -> FStar_Pervasives.Inr (x, i)))) uu___
let op_let_Bang : 'a 'b . 'a tm -> ('a -> 'b tm) -> 'b tm =
  fun m ->
    fun f ->
      fun i ->
        let uu___ = m i in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Reflection.V2.Arith.fst"
                   (Prims.of_int (77)) (Prims.of_int (19))
                   (Prims.of_int (77)) (Prims.of_int (22)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Reflection.V2.Arith.fst"
                   (Prims.of_int (77)) (Prims.of_int (13))
                   (Prims.of_int (79)) (Prims.of_int (34)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | FStar_Pervasives.Inr (x, j) -> Obj.magic (Obj.repr (f x j))
                | s ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               FStar_Pervasives.Inl
                                 (FStar_Pervasives.__proj__Inl__item__v s)))))
               uu___1)
let lift :
  'a 'b . ('a -> ('b, unit) FStar_Tactics_Effect.tac_repr) -> 'a -> 'b tm =
  fun f ->
    fun x ->
      fun st1 ->
        let uu___ =
          let uu___1 = f x in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Reflection.V2.Arith.fst"
                     (Prims.of_int (83)) (Prims.of_int (9))
                     (Prims.of_int (83)) (Prims.of_int (12)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Reflection.V2.Arith.fst"
                     (Prims.of_int (83)) (Prims.of_int (8))
                     (Prims.of_int (83)) (Prims.of_int (17)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___3 -> (uu___2, st1))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Reflection.V2.Arith.fst"
                   (Prims.of_int (83)) (Prims.of_int (8)) (Prims.of_int (83))
                   (Prims.of_int (17)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Reflection.V2.Arith.fst"
                   (Prims.of_int (83)) (Prims.of_int (4)) (Prims.of_int (83))
                   (Prims.of_int (17))))) (Obj.magic uu___)
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 -> FStar_Pervasives.Inr uu___1))
let liftM : 'a 'b . ('a -> 'b) -> 'a tm -> 'b tm =
  fun f -> fun x -> op_let_Bang x (fun xx -> return (f xx))
let liftM2 : 'a 'b 'c . ('a -> 'b -> 'c) -> 'a tm -> 'b tm -> 'c tm =
  fun f ->
    fun x ->
      fun y ->
        op_let_Bang x (fun xx -> op_let_Bang y (fun yy -> return (f xx yy)))
let liftM3 :
  'a 'b 'c 'd . ('a -> 'b -> 'c -> 'd) -> 'a tm -> 'b tm -> 'c tm -> 'd tm =
  fun f ->
    fun x ->
      fun y ->
        fun z ->
          op_let_Bang x
            (fun xx ->
               op_let_Bang y
                 (fun yy -> op_let_Bang z (fun zz -> return (f xx yy zz))))
let rec find_idx :
  'a .
    ('a -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list ->
        ((Prims.nat * 'a) FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun l ->
           match l with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> FStar_Pervasives_Native.None)))
           | x::xs ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = f x in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Reflection.V2.Arith.fst"
                                (Prims.of_int (108)) (Prims.of_int (11))
                                (Prims.of_int (108)) (Prims.of_int (14)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Reflection.V2.Arith.fst"
                                (Prims.of_int (108)) (Prims.of_int (8))
                                (Prims.of_int (113)) (Prims.of_int (16)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             if uu___1
                             then
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 ->
                                          FStar_Pervasives_Native.Some
                                            (Prims.int_zero, x))))
                             else
                               Obj.magic
                                 (Obj.repr
                                    (let uu___3 = find_idx f xs in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Reflection.V2.Arith.fst"
                                                (Prims.of_int (110))
                                                (Prims.of_int (25))
                                                (Prims.of_int (110))
                                                (Prims.of_int (38)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Reflection.V2.Arith.fst"
                                                (Prims.of_int (110))
                                                (Prims.of_int (19))
                                                (Prims.of_int (112))
                                                (Prims.of_int (43)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___5 ->
                                               match uu___4 with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Pervasives_Native.Some
                                                   (i, x1) ->
                                                   FStar_Pervasives_Native.Some
                                                     ((i + Prims.int_one),
                                                       x1)))))) uu___1))))
        uu___1 uu___
let (atom : FStarC_Reflection_Types.term -> expr tm) =
  fun t ->
    fun uu___ ->
      match uu___ with
      | (n, atoms) ->
          let uu___1 =
            find_idx (FStarC_Tactics_V2_Builtins.term_eq_old t) atoms in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Reflection.V2.Arith.fst"
                     (Prims.of_int (116)) (Prims.of_int (10))
                     (Prims.of_int (116)) (Prims.of_int (40)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Reflection.V2.Arith.fst"
                     (Prims.of_int (116)) (Prims.of_int (4))
                     (Prims.of_int (118)) (Prims.of_int (57)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___3 ->
                    match uu___2 with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives.Inr
                          ((Atom (n, t)),
                            ((n + Prims.int_one), (t :: atoms)))
                    | FStar_Pervasives_Native.Some (i, t1) ->
                        FStar_Pervasives.Inr
                          ((Atom (((n - Prims.int_one) - i), t1)),
                            (n, atoms))))
let fail : 'a . Prims.string -> 'a tm =
  fun uu___ ->
    (fun s ->
       fun i ->
         Obj.magic
           (FStar_Tactics_Effect.lift_div_tac
              (fun uu___ -> FStar_Pervasives.Inl s))) uu___
let rec (as_arith_expr : FStarC_Reflection_Types.term -> expr tm) =
  fun t ->
    let uu___ = FStar_Reflection_V2_Collect.collect_app_ln t in
    match uu___ with
    | (hd, tl) ->
        (match ((FStarC_Reflection_V2_Builtins.inspect_ln hd), tl) with
         | (FStarC_Reflection_V2_Data.Tv_FVar fv,
            (e1, FStarC_Reflection_V2_Data.Q_Implicit)::(e2,
                                                         FStarC_Reflection_V2_Data.Q_Explicit)::
            (e3, FStarC_Reflection_V2_Data.Q_Explicit)::[]) ->
             let qn = FStarC_Reflection_V2_Builtins.inspect_fv fv in
             let e2' = as_arith_expr e2 in
             let e3' = as_arith_expr e3 in
             if qn = FStar_Reflection_Const.land_qn
             then
               liftM2 (fun uu___1 -> fun uu___2 -> Land (uu___1, uu___2)) e2'
                 e3'
             else
               if qn = FStar_Reflection_Const.lxor_qn
               then
                 liftM2 (fun uu___2 -> fun uu___3 -> Lxor (uu___2, uu___3))
                   e2' e3'
               else
                 if qn = FStar_Reflection_Const.lor_qn
                 then
                   liftM2 (fun uu___3 -> fun uu___4 -> Lor (uu___3, uu___4))
                     e2' e3'
                 else
                   if qn = FStar_Reflection_Const.shiftr_qn
                   then
                     liftM2
                       (fun uu___4 -> fun uu___5 -> Shr (uu___4, uu___5)) e2'
                       e3'
                   else
                     if qn = FStar_Reflection_Const.shiftl_qn
                     then
                       liftM2
                         (fun uu___5 -> fun uu___6 -> Shl (uu___5, uu___6))
                         e2' e3'
                     else
                       if qn = FStar_Reflection_Const.udiv_qn
                       then
                         liftM2
                           (fun uu___6 -> fun uu___7 -> Udiv (uu___6, uu___7))
                           e2' e3'
                       else
                         if qn = FStar_Reflection_Const.umod_qn
                         then
                           liftM2
                             (fun uu___7 ->
                                fun uu___8 -> Umod (uu___7, uu___8)) e2' e3'
                         else
                           if qn = FStar_Reflection_Const.mul_mod_qn
                           then
                             liftM2
                               (fun uu___8 ->
                                  fun uu___9 -> MulMod (uu___8, uu___9)) e2'
                               e3'
                           else
                             if qn = FStar_Reflection_Const.ladd_qn
                             then
                               liftM2
                                 (fun uu___9 ->
                                    fun uu___10 -> Ladd (uu___9, uu___10))
                                 e2' e3'
                             else
                               if qn = FStar_Reflection_Const.lsub_qn
                               then
                                 liftM2
                                   (fun uu___10 ->
                                      fun uu___11 -> Lsub (uu___10, uu___11))
                                   e2' e3'
                               else atom t
         | (FStarC_Reflection_V2_Data.Tv_FVar fv,
            (l, FStarC_Reflection_V2_Data.Q_Explicit)::(r,
                                                        FStarC_Reflection_V2_Data.Q_Explicit)::[])
             ->
             let qn = FStarC_Reflection_V2_Builtins.inspect_fv fv in
             let ll = as_arith_expr l in
             let rr = as_arith_expr r in
             if qn = FStar_Reflection_Const.add_qn
             then
               liftM2 (fun uu___1 -> fun uu___2 -> Plus (uu___1, uu___2)) ll
                 rr
             else
               if qn = FStar_Reflection_Const.minus_qn
               then
                 liftM2 (fun uu___2 -> fun uu___3 -> Minus (uu___2, uu___3))
                   ll rr
               else
                 if qn = FStar_Reflection_Const.mult_qn
                 then
                   liftM2 (fun uu___3 -> fun uu___4 -> Mult (uu___3, uu___4))
                     ll rr
                 else
                   if qn = FStar_Reflection_Const.mult'_qn
                   then
                     liftM2
                       (fun uu___4 -> fun uu___5 -> Mult (uu___4, uu___5)) ll
                       rr
                   else atom t
         | (FStarC_Reflection_V2_Data.Tv_FVar fv,
            (l, FStarC_Reflection_V2_Data.Q_Implicit)::(r,
                                                        FStarC_Reflection_V2_Data.Q_Explicit)::[])
             ->
             let qn = FStarC_Reflection_V2_Builtins.inspect_fv fv in
             let ll = as_arith_expr l in
             let rr = as_arith_expr r in
             if qn = FStar_Reflection_Const.nat_bv_qn
             then liftM (fun uu___1 -> NatToBv uu___1) rr
             else atom t
         | (FStarC_Reflection_V2_Data.Tv_FVar fv,
            (a, FStarC_Reflection_V2_Data.Q_Explicit)::[]) ->
             let qn = FStarC_Reflection_V2_Builtins.inspect_fv fv in
             let aa = as_arith_expr a in
             if qn = FStar_Reflection_Const.neg_qn
             then liftM (fun uu___1 -> Neg uu___1) aa
             else atom t
         | (FStarC_Reflection_V2_Data.Tv_Const
            (FStarC_Reflection_V2_Data.C_Int i), uu___1) -> return (Lit i)
         | uu___1 -> atom t)
let (is_arith_expr : FStarC_Reflection_Types.term -> expr tm) =
  fun t ->
    op_let_Bang (as_arith_expr t)
      (fun a ->
         match a with
         | Atom (uu___, t1) ->
             let uu___1 =
               FStar_Reflection_V2_Derived_Lemmas.collect_app_ref t1 in
             (match uu___1 with
              | (hd, tl) ->
                  (match ((FStarC_Reflection_V2_Builtins.inspect_ln hd), tl)
                   with
                   | (FStarC_Reflection_V2_Data.Tv_FVar uu___2, []) ->
                       return a
                   | (FStarC_Reflection_V2_Data.Tv_BVar uu___2, []) ->
                       return a
                   | (FStarC_Reflection_V2_Data.Tv_Var uu___2, []) ->
                       return a
                   | uu___2 ->
                       op_let_Bang
                         (lift FStarC_Tactics_V2_Builtins.term_to_string t1)
                         (fun s ->
                            fail
                              (Prims.strcat "not an arithmetic expression: ("
                                 (Prims.strcat s ")")))))
         | uu___ -> return a)
let rec (is_arith_prop :
  FStarC_Reflection_Types.term ->
    st ->
      ((Prims.string, (prop * st)) FStar_Pervasives.either, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun i ->
      op_let_Bang
        (lift (fun t1 -> FStar_Reflection_V2_Formula.term_as_formula t1) t)
        (fun f ->
           match f with
           | FStar_Reflection_V2_Formula.Comp
               (FStar_Reflection_V2_Formula.Eq uu___, l, r) ->
               liftM2 eq (is_arith_expr l) (is_arith_expr r)
           | FStar_Reflection_V2_Formula.Comp
               (FStar_Reflection_V2_Formula.BoolEq uu___, l, r) ->
               liftM2 eq (is_arith_expr l) (is_arith_expr r)
           | FStar_Reflection_V2_Formula.Comp
               (FStar_Reflection_V2_Formula.Lt, l, r) ->
               liftM2 lt (is_arith_expr l) (is_arith_expr r)
           | FStar_Reflection_V2_Formula.Comp
               (FStar_Reflection_V2_Formula.Le, l, r) ->
               liftM2 le (is_arith_expr l) (is_arith_expr r)
           | FStar_Reflection_V2_Formula.And (l, r) ->
               liftM2 (fun uu___ -> fun uu___1 -> AndProp (uu___, uu___1))
                 (is_arith_prop l) (is_arith_prop r)
           | FStar_Reflection_V2_Formula.Or (l, r) ->
               liftM2 (fun uu___ -> fun uu___1 -> OrProp (uu___, uu___1))
                 (is_arith_prop l) (is_arith_prop r)
           | uu___ ->
               op_let_Bang (lift FStarC_Tactics_V2_Builtins.term_to_string t)
                 (fun s ->
                    fail (Prims.strcat "connector (" (Prims.strcat s ")"))))
        i
let run_tm :
  'a .
    'a tm ->
      ((Prims.string, 'a) FStar_Pervasives.either, unit)
        FStar_Tactics_Effect.tac_repr
  =
  fun m ->
    let uu___ = m (Prims.int_zero, []) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Reflection.V2.Arith.fst"
               (Prims.of_int (212)) (Prims.of_int (10)) (Prims.of_int (212))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Reflection.V2.Arith.fst"
               (Prims.of_int (212)) (Prims.of_int (4)) (Prims.of_int (214))
               (Prims.of_int (25))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 ->
              match uu___1 with
              | FStar_Pervasives.Inr (x, uu___3) -> FStar_Pervasives.Inr x
              | s ->
                  FStar_Pervasives.Inl
                    (FStar_Pervasives.__proj__Inl__item__v s)))
let rec (expr_to_string : expr -> Prims.string) =
  fun e ->
    match e with
    | Atom (i, uu___) -> Prims.strcat "a" (Prims.string_of_int i)
    | Lit i -> Prims.string_of_int i
    | Plus (l, r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " + " (Prims.strcat (expr_to_string r) ")")))
    | Minus (l, r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " - " (Prims.strcat (expr_to_string r) ")")))
    | Mult (l, r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " * " (Prims.strcat (expr_to_string r) ")")))
    | Neg l -> Prims.strcat "(- " (Prims.strcat (expr_to_string l) ")")
    | Land (l, r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " & " (Prims.strcat (expr_to_string r) ")")))
    | Lor (l, r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " | " (Prims.strcat (expr_to_string r) ")")))
    | Lxor (l, r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " ^ " (Prims.strcat (expr_to_string r) ")")))
    | Ladd (l, r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " >> " (Prims.strcat (expr_to_string r) ")")))
    | Lsub (l, r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " >> " (Prims.strcat (expr_to_string r) ")")))
    | Shl (l, r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " << " (Prims.strcat (expr_to_string r) ")")))
    | Shr (l, r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " >> " (Prims.strcat (expr_to_string r) ")")))
    | NatToBv l ->
        Prims.strcat "("
          (Prims.strcat "to_vec " (Prims.strcat (expr_to_string l) ")"))
    | Udiv (l, r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " / " (Prims.strcat (expr_to_string r) ")")))
    | Umod (l, r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " % " (Prims.strcat (expr_to_string r) ")")))
    | MulMod (l, r) ->
        Prims.strcat "("
          (Prims.strcat (expr_to_string l)
             (Prims.strcat " ** " (Prims.strcat (expr_to_string r) ")")))
let rec (compare_expr : expr -> expr -> FStar_Order.order) =
  fun e1 ->
    fun e2 ->
      match (e1, e2) with
      | (Lit i, Lit j) -> FStar_Order.compare_int i j
      | (Atom (uu___, t), Atom (uu___1, s)) ->
          FStar_Reflection_V2_Compare.compare_term t s
      | (Plus (l1, l2), Plus (r1, r2)) ->
          FStar_Order.lex (compare_expr l1 r1)
            (fun uu___ -> compare_expr l2 r2)
      | (Minus (l1, l2), Minus (r1, r2)) ->
          FStar_Order.lex (compare_expr l1 r1)
            (fun uu___ -> compare_expr l2 r2)
      | (Mult (l1, l2), Mult (r1, r2)) ->
          FStar_Order.lex (compare_expr l1 r1)
            (fun uu___ -> compare_expr l2 r2)
      | (Neg e11, Neg e21) -> compare_expr e11 e21
      | (Lit uu___, uu___1) -> FStar_Order.Lt
      | (uu___, Lit uu___1) -> FStar_Order.Gt
      | (Atom (uu___, uu___1), uu___2) -> FStar_Order.Lt
      | (uu___, Atom (uu___1, uu___2)) -> FStar_Order.Gt
      | (Plus (uu___, uu___1), uu___2) -> FStar_Order.Lt
      | (uu___, Plus (uu___1, uu___2)) -> FStar_Order.Gt
      | (Mult (uu___, uu___1), uu___2) -> FStar_Order.Lt
      | (uu___, Mult (uu___1, uu___2)) -> FStar_Order.Gt
      | (Neg uu___, uu___1) -> FStar_Order.Lt
      | (uu___, Neg uu___1) -> FStar_Order.Gt
      | uu___ -> FStar_Order.Gt