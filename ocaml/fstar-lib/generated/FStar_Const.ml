open Prims
type signedness =
  | Unsigned 
  | Signed [@@deriving yojson,show]
let (uu___is_Unsigned : signedness -> Prims.bool) =
  fun projectee -> match projectee with | Unsigned -> true | uu___ -> false
let (uu___is_Signed : signedness -> Prims.bool) =
  fun projectee -> match projectee with | Signed -> true | uu___ -> false
type width =
  | Int8 
  | Int16 
  | Int32 
  | Int64 
  | Sizet [@@deriving yojson,show]
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int8 -> true | uu___ -> false
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int16 -> true | uu___ -> false
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int32 -> true | uu___ -> false
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int64 -> true | uu___ -> false
let (uu___is_Sizet : width -> Prims.bool) =
  fun projectee -> match projectee with | Sizet -> true | uu___ -> false
type sconst =
  | Const_effect 
  | Const_unit 
  | Const_bool of Prims.bool 
  | Const_int of (Prims.string * (signedness * width)
  FStar_Pervasives_Native.option) 
  | Const_char of FStar_BaseTypes.char 
  | Const_real of Prims.string 
  | Const_string of (Prims.string * FStar_Compiler_Range.range) 
  | Const_range_of 
  | Const_set_range_of 
  | Const_range of FStar_Compiler_Range.range 
  | Const_reify of FStar_Ident.lid FStar_Pervasives_Native.option 
  | Const_reflect of FStar_Ident.lid [@@deriving yojson,show]
let (uu___is_Const_effect : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_effect -> true | uu___ -> false
let (uu___is_Const_unit : sconst -> Prims.bool) =
  fun projectee -> match projectee with | Const_unit -> true | uu___ -> false
let (uu___is_Const_bool : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_bool _0 -> true | uu___ -> false
let (__proj__Const_bool__item___0 : sconst -> Prims.bool) =
  fun projectee -> match projectee with | Const_bool _0 -> _0
let (uu___is_Const_int : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_int _0 -> true | uu___ -> false
let (__proj__Const_int__item___0 :
  sconst ->
    (Prims.string * (signedness * width) FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Const_int _0 -> _0
let (uu___is_Const_char : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_char _0 -> true | uu___ -> false
let (__proj__Const_char__item___0 : sconst -> FStar_BaseTypes.char) =
  fun projectee -> match projectee with | Const_char _0 -> _0
let (uu___is_Const_real : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_real _0 -> true | uu___ -> false
let (__proj__Const_real__item___0 : sconst -> Prims.string) =
  fun projectee -> match projectee with | Const_real _0 -> _0
let (uu___is_Const_string : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_string _0 -> true | uu___ -> false
let (__proj__Const_string__item___0 :
  sconst -> (Prims.string * FStar_Compiler_Range.range)) =
  fun projectee -> match projectee with | Const_string _0 -> _0
let (uu___is_Const_range_of : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_range_of -> true | uu___ -> false
let (uu___is_Const_set_range_of : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_set_range_of -> true | uu___ -> false
let (uu___is_Const_range : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_range _0 -> true | uu___ -> false
let (__proj__Const_range__item___0 : sconst -> FStar_Compiler_Range.range) =
  fun projectee -> match projectee with | Const_range _0 -> _0
let (uu___is_Const_reify : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_reify _0 -> true | uu___ -> false
let (__proj__Const_reify__item___0 :
  sconst -> FStar_Ident.lid FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | Const_reify _0 -> _0
let (uu___is_Const_reflect : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_reflect _0 -> true | uu___ -> false
let (__proj__Const_reflect__item___0 : sconst -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Const_reflect _0 -> _0
let (eq_const : sconst -> sconst -> Prims.bool) =
  fun c1 ->
    fun c2 ->
      match (c1, c2) with
      | (Const_int (s1, o1), Const_int (s2, o2)) ->
          (let uu___ = FStar_Compiler_Util.ensure_decimal s1 in
           let uu___1 = FStar_Compiler_Util.ensure_decimal s2 in
           uu___ = uu___1) && (o1 = o2)
      | (Const_string (a, uu___), Const_string (b, uu___1)) -> a = b
      | (Const_reflect l1, Const_reflect l2) -> FStar_Ident.lid_equals l1 l2
      | (Const_reify uu___, Const_reify uu___1) -> true
      | uu___ -> c1 = c2
let rec (pow2 : FStar_BigInt.bigint -> FStar_BigInt.bigint) =
  fun x ->
    let uu___ = FStar_BigInt.eq_big_int x FStar_BigInt.zero in
    if uu___
    then FStar_BigInt.one
    else
      (let uu___2 = let uu___3 = FStar_BigInt.pred_big_int x in pow2 uu___3 in
       FStar_BigInt.mult_big_int FStar_BigInt.two uu___2)
let (bounds :
  signedness -> width -> (FStar_BigInt.bigint * FStar_BigInt.bigint)) =
  fun signedness1 ->
    fun width1 ->
      let n =
        match width1 with
        | Int8 -> FStar_BigInt.big_int_of_string "8"
        | Int16 -> FStar_BigInt.big_int_of_string "16"
        | Int32 -> FStar_BigInt.big_int_of_string "32"
        | Int64 -> FStar_BigInt.big_int_of_string "64"
        | Sizet -> FStar_BigInt.big_int_of_string "16" in
      let uu___ =
        match signedness1 with
        | Unsigned ->
            let uu___1 =
              let uu___2 = pow2 n in FStar_BigInt.pred_big_int uu___2 in
            (FStar_BigInt.zero, uu___1)
        | Signed ->
            let upper =
              let uu___1 = FStar_BigInt.pred_big_int n in pow2 uu___1 in
            let uu___1 = FStar_BigInt.minus_big_int upper in
            let uu___2 = FStar_BigInt.pred_big_int upper in (uu___1, uu___2) in
      match uu___ with | (lower, upper) -> (lower, upper)
let (within_bounds : Prims.string -> signedness -> width -> Prims.bool) =
  fun repr ->
    fun signedness1 ->
      fun width1 ->
        let uu___ = bounds signedness1 width1 in
        match uu___ with
        | (lower, upper) ->
            let value =
              let uu___1 = FStar_Compiler_Util.ensure_decimal repr in
              FStar_BigInt.big_int_of_string uu___1 in
            (FStar_BigInt.le_big_int lower value) &&
              (FStar_BigInt.le_big_int value upper)