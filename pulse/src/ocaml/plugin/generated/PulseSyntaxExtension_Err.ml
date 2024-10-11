open Prims
let (hasRange_ident : FStarC_Ident.ident FStarC_Class_HasRange.hasRange) =
  {
    FStarC_Class_HasRange.pos = FStarC_Ident.range_of_id;
    FStarC_Class_HasRange.setPos = FStarC_Ident.set_id_range
  }
let (hasRange_lident : FStarC_Ident.lident FStarC_Class_HasRange.hasRange) =
  {
    FStarC_Class_HasRange.pos = FStarC_Ident.range_of_lid;
    FStarC_Class_HasRange.setPos =
      (fun x -> fun y -> FStarC_Ident.set_lid_range y x)
  }
type error =
  (Prims.string * FStarC_Compiler_Range_Type.range)
    FStar_Pervasives_Native.option
type 'a err = Prims.nat -> (('a, error) FStar_Pervasives.either * Prims.nat)
let bind_err :
  'a 'b .
    'a err ->
      ('a -> 'b err) ->
        Prims.nat -> (('b, error) FStar_Pervasives.either * Prims.nat)
  =
  fun f ->
    fun g ->
      fun ctr ->
        let uu___ = f ctr in
        match uu___ with
        | (FStar_Pervasives.Inl a1, ctr1) -> let uu___1 = g a1 in uu___1 ctr1
        | (FStar_Pervasives.Inr e, ctr1) -> ((FStar_Pervasives.Inr e), ctr1)
let return : 'a . 'a -> 'a err =
  fun x -> fun ctr -> ((FStar_Pervasives.Inl x), ctr)
let (err_monad : unit err FStarC_Class_Monad.monad) =
  {
    FStarC_Class_Monad.return =
      (fun uu___1 ->
         fun uu___ -> (fun uu___ -> Obj.magic return) uu___1 uu___);
    FStarC_Class_Monad.op_let_Bang =
      (fun uu___3 ->
         fun uu___2 ->
           fun uu___1 ->
             fun uu___ ->
               (fun uu___1 -> fun uu___ -> Obj.magic bind_err) uu___3 uu___2
                 uu___1 uu___)
  }
let fail : 'a . Prims.string -> FStarC_Compiler_Range_Type.range -> 'a err =
  fun message ->
    fun range ->
      fun ctr ->
        ((FStar_Pervasives.Inr
            (FStar_Pervasives_Native.Some (message, range))), ctr)
let (fail_if :
  Prims.bool -> Prims.string -> FStarC_Compiler_Range_Type.range -> unit err)
  =
  fun b ->
    fun message -> fun range -> if b then fail message range else return ()
let just_fail : 'a . unit -> 'a err =
  fun uu___ ->
    fun ctr -> ((FStar_Pervasives.Inr FStar_Pervasives_Native.None), ctr)
let (next_ctr : Prims.nat err) =
  fun ctr ->
    ((FStar_Pervasives.Inl (ctr + Prims.int_one)), (ctr + Prims.int_one))
let map_err_opt :
  'a 'b .
    ('a -> 'b err) ->
      'a FStar_Pervasives_Native.option ->
        'b FStar_Pervasives_Native.option err
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun o ->
           match o with
           | FStar_Pervasives_Native.None ->
               Obj.magic (Obj.repr (return FStar_Pervasives_Native.None))
           | FStar_Pervasives_Native.Some v ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = f v in
                     FStarC_Class_Monad.op_let_Bang err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun v' ->
                             let v' = Obj.magic v' in
                             Obj.magic
                               (return (FStar_Pervasives_Native.Some v')))
                            uu___1)))) uu___1 uu___
let rec map2 :
  'a 'b 'c .
    ('a -> 'b -> 'c) -> 'a Prims.list -> 'b Prims.list -> 'c Prims.list err
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun f ->
           fun xs ->
             fun ys ->
               match (xs, ys) with
               | ([], []) -> Obj.magic (Obj.repr (return []))
               | (x::xx, y::yy) ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ = map2 f xx yy in
                         FStarC_Class_Monad.op_let_Bang err_monad () ()
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun r ->
                                 let r = Obj.magic r in
                                 let uu___1 =
                                   let uu___2 = f x y in uu___2 :: r in
                                 Obj.magic (return uu___1)) uu___1)))
               | uu___ ->
                   Obj.magic
                     (Obj.repr
                        (fail "map2: mismatch"
                           FStarC_Compiler_Range_Type.dummyRange))) uu___2
          uu___1 uu___
let left :
  'a 'b .
    ('a, 'b) FStar_Pervasives.either ->
      FStarC_Compiler_Range_Type.range -> 'a err
  =
  fun f ->
    fun r ->
      match f with
      | FStar_Pervasives.Inl x -> return x
      | FStar_Pervasives.Inr uu___ -> fail "Unsupported case" r
let right :
  'a 'b .
    ('a, 'b) FStar_Pervasives.either ->
      FStarC_Compiler_Range_Type.range -> 'b err
  =
  fun f ->
    fun r ->
      match f with
      | FStar_Pervasives.Inr x -> return x
      | FStar_Pervasives.Inl uu___ -> fail "Unsupported case" r