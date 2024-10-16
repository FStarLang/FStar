open Prims
type 'a hashable = {
  hash: 'a -> FStarC_Hash.hash_code }
let __proj__Mkhashable__item__hash :
  'a . 'a hashable -> 'a -> FStarC_Hash.hash_code =
  fun projectee -> match projectee with | { hash;_} -> hash
let hash : 'a . 'a hashable -> 'a -> FStarC_Hash.hash_code =
  fun projectee -> match projectee with | { hash = hash1;_} -> hash1
let (showable_hash_code : FStarC_Hash.hash_code FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = FStarC_Hash.string_of_hash_code }
let (eq_hash_code : FStarC_Hash.hash_code FStarC_Class_Deq.deq) =
  { FStarC_Class_Deq.op_Equals_Question = (=) }
let (ord_hash_code : FStarC_Hash.hash_code FStarC_Class_Ord.ord) =
  {
    FStarC_Class_Ord.super = eq_hash_code;
    FStarC_Class_Ord.cmp =
      (fun x ->
         fun y ->
           let uu___ = FStarC_Hash.cmp_hash x y in
           FStarC_Compiler_Order.order_from_int uu___)
  }
let (hashable_int : Prims.int hashable) = { hash = FStarC_Hash.of_int }
let (hashable_string : Prims.string hashable) =
  { hash = FStarC_Hash.of_string }
let (hashable_bool : Prims.bool hashable) =
  {
    hash =
      (fun b ->
         if b
         then FStarC_Hash.of_int Prims.int_one
         else FStarC_Hash.of_int (Prims.of_int (2)))
  }
let hashable_list : 'a . 'a hashable -> 'a Prims.list hashable =
  fun uu___ ->
    {
      hash =
        (fun xs ->
           let uu___1 = FStarC_Hash.of_int Prims.int_zero in
           FStarC_Compiler_List.fold_left
             (fun h ->
                fun x ->
                  let uu___2 = hash uu___ x in FStarC_Hash.mix h uu___2)
             uu___1 xs)
    }
let hashable_option :
  'a . 'a hashable -> 'a FStar_Pervasives_Native.option hashable =
  fun uu___ ->
    {
      hash =
        (fun x ->
           match x with
           | FStar_Pervasives_Native.None ->
               FStarC_Hash.of_int Prims.int_zero
           | FStar_Pervasives_Native.Some x1 ->
               let uu___1 = FStarC_Hash.of_int Prims.int_one in
               let uu___2 = hash uu___ x1 in FStarC_Hash.mix uu___1 uu___2)
    }
let hashable_either :
  'a 'b .
    'a hashable -> 'b hashable -> ('a, 'b) FStar_Pervasives.either hashable
  =
  fun uu___ ->
    fun uu___1 ->
      {
        hash =
          (fun x ->
             match x with
             | FStar_Pervasives.Inl a1 ->
                 let uu___2 = FStarC_Hash.of_int Prims.int_zero in
                 let uu___3 = hash uu___ a1 in FStarC_Hash.mix uu___2 uu___3
             | FStar_Pervasives.Inr b1 ->
                 let uu___2 = FStarC_Hash.of_int Prims.int_one in
                 let uu___3 = hash uu___1 b1 in FStarC_Hash.mix uu___2 uu___3)
      }
let hashable_tuple2 :
  'a 'b . 'a hashable -> 'b hashable -> ('a * 'b) hashable =
  fun uu___ ->
    fun uu___1 ->
      {
        hash =
          (fun uu___2 ->
             match uu___2 with
             | (a1, b1) ->
                 let uu___3 = hash uu___ a1 in
                 let uu___4 = hash uu___1 b1 in FStarC_Hash.mix uu___3 uu___4)
      }
let hashable_tuple3 :
  'a 'b 'c .
    'a hashable -> 'b hashable -> 'c hashable -> ('a * 'b * 'c) hashable
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        {
          hash =
            (fun uu___3 ->
               match uu___3 with
               | (a1, b1, c1) ->
                   let uu___4 =
                     let uu___5 = hash uu___ a1 in
                     let uu___6 = hash uu___1 b1 in
                     FStarC_Hash.mix uu___5 uu___6 in
                   let uu___5 = hash uu___2 c1 in
                   FStarC_Hash.mix uu___4 uu___5)
        }
let hashable_tuple4 :
  'a 'b 'c 'd .
    'a hashable ->
      'b hashable ->
        'c hashable -> 'd hashable -> ('a * 'b * 'c * 'd) hashable
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          {
            hash =
              (fun uu___4 ->
                 match uu___4 with
                 | (a1, b1, c1, d1) ->
                     let uu___5 =
                       let uu___6 =
                         let uu___7 = hash uu___ a1 in
                         let uu___8 = hash uu___1 b1 in
                         FStarC_Hash.mix uu___7 uu___8 in
                       let uu___7 = hash uu___2 c1 in
                       FStarC_Hash.mix uu___6 uu___7 in
                     let uu___6 = hash uu___3 d1 in
                     FStarC_Hash.mix uu___5 uu___6)
          }
let hashable_tuple5 :
  'a 'b 'c 'd 'e .
    'a hashable ->
      'b hashable ->
        'c hashable ->
          'd hashable -> 'e hashable -> ('a * 'b * 'c * 'd * 'e) hashable
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          fun uu___4 ->
            {
              hash =
                (fun uu___5 ->
                   match uu___5 with
                   | (a1, b1, c1, d1, e1) ->
                       let uu___6 =
                         let uu___7 =
                           let uu___8 =
                             let uu___9 = hash uu___ a1 in
                             let uu___10 = hash uu___1 b1 in
                             FStarC_Hash.mix uu___9 uu___10 in
                           let uu___9 = hash uu___2 c1 in
                           FStarC_Hash.mix uu___8 uu___9 in
                         let uu___8 = hash uu___3 d1 in
                         FStarC_Hash.mix uu___7 uu___8 in
                       let uu___7 = hash uu___4 e1 in
                       FStarC_Hash.mix uu___6 uu___7)
            }
let hashable_tuple6 :
  'a 'b 'c 'd 'e 'f .
    'a hashable ->
      'b hashable ->
        'c hashable ->
          'd hashable ->
            'e hashable ->
              'f hashable -> ('a * 'b * 'c * 'd * 'e * 'f) hashable
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          fun uu___4 ->
            fun uu___5 ->
              {
                hash =
                  (fun uu___6 ->
                     match uu___6 with
                     | (a1, b1, c1, d1, e1, f1) ->
                         let uu___7 =
                           let uu___8 =
                             let uu___9 =
                               let uu___10 =
                                 let uu___11 = hash uu___ a1 in
                                 let uu___12 = hash uu___1 b1 in
                                 FStarC_Hash.mix uu___11 uu___12 in
                               let uu___11 = hash uu___2 c1 in
                               FStarC_Hash.mix uu___10 uu___11 in
                             let uu___10 = hash uu___3 d1 in
                             FStarC_Hash.mix uu___9 uu___10 in
                           let uu___9 = hash uu___4 e1 in
                           FStarC_Hash.mix uu___8 uu___9 in
                         let uu___8 = hash uu___5 f1 in
                         FStarC_Hash.mix uu___7 uu___8)
              }