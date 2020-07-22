open Prims
type signedness =
  | Unsigned 
  | Signed [@@deriving yojson,show]
let (uu___is_Unsigned : signedness -> Prims.bool) =
  fun projectee -> match projectee with | Unsigned -> true | uu____5 -> false
let (uu___is_Signed : signedness -> Prims.bool) =
  fun projectee -> match projectee with | Signed -> true | uu____11 -> false
type width =
  | Int8 
  | Int16 
  | Int32 
  | Int64 [@@deriving yojson,show]
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int8 -> true | uu____17 -> false
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int16 -> true | uu____23 -> false
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int32 -> true | uu____29 -> false
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int64 -> true | uu____35 -> false
type sconst =
  | Const_effect 
  | Const_unit 
  | Const_bool of Prims.bool 
  | Const_int of (Prims.string * (signedness * width)
  FStar_Pervasives_Native.option) 
  | Const_char of FStar_BaseTypes.char 
  | Const_float of FStar_BaseTypes.double 
  | Const_real of Prims.string 
  | Const_bytearray of (FStar_BaseTypes.byte Prims.array * FStar_Range.range)
  
  | Const_string of (Prims.string * FStar_Range.range) 
  | Const_range_of 
  | Const_set_range_of 
  | Const_range of FStar_Range.range 
  | Const_reify 
  | Const_reflect of FStar_Ident.lid [@@deriving yojson,show]
let (uu___is_Const_effect : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_effect -> true | uu____106 -> false
let (uu___is_Const_unit : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_unit -> true | uu____112 -> false
let (uu___is_Const_bool : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_bool _0 -> true | uu____119 -> false
let (__proj__Const_bool__item___0 : sconst -> Prims.bool) =
  fun projectee -> match projectee with | Const_bool _0 -> _0
let (uu___is_Const_int : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_int _0 -> true | uu____142 -> false
let (__proj__Const_int__item___0 :
  sconst ->
    (Prims.string * (signedness * width) FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Const_int _0 -> _0
let (uu___is_Const_char : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_char _0 -> true | uu____185 -> false
let (__proj__Const_char__item___0 : sconst -> FStar_BaseTypes.char) =
  fun projectee -> match projectee with | Const_char _0 -> _0
let (uu___is_Const_float : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_float _0 -> true | uu____198 -> false
let (__proj__Const_float__item___0 : sconst -> FStar_BaseTypes.double) =
  fun projectee -> match projectee with | Const_float _0 -> _0
let (uu___is_Const_real : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_real _0 -> true | uu____211 -> false
let (__proj__Const_real__item___0 : sconst -> Prims.string) =
  fun projectee -> match projectee with | Const_real _0 -> _0
let (uu___is_Const_bytearray : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_bytearray _0 -> true | uu____230 -> false
let (__proj__Const_bytearray__item___0 :
  sconst -> (FStar_BaseTypes.byte Prims.array * FStar_Range.range)) =
  fun projectee -> match projectee with | Const_bytearray _0 -> _0
let (uu___is_Const_string : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_string _0 -> true | uu____265 -> false
let (__proj__Const_string__item___0 :
  sconst -> (Prims.string * FStar_Range.range)) =
  fun projectee -> match projectee with | Const_string _0 -> _0
let (uu___is_Const_range_of : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_range_of -> true | uu____289 -> false
let (uu___is_Const_set_range_of : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_set_range_of -> true | uu____295 -> false
let (uu___is_Const_range : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_range _0 -> true | uu____302 -> false
let (__proj__Const_range__item___0 : sconst -> FStar_Range.range) =
  fun projectee -> match projectee with | Const_range _0 -> _0
let (uu___is_Const_reify : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_reify -> true | uu____314 -> false
let (uu___is_Const_reflect : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_reflect _0 -> true | uu____321 -> false
let (__proj__Const_reflect__item___0 : sconst -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Const_reflect _0 -> _0
let (eq_const : sconst -> sconst -> Prims.bool) =
  fun c1 ->
    fun c2 ->
      match (c1, c2) with
      | (Const_int (s1, o1), Const_int (s2, o2)) ->
          (let uu____370 = FStar_Util.ensure_decimal s1 in
           let uu____371 = FStar_Util.ensure_decimal s2 in
           uu____370 = uu____371) && (o1 = o2)
      | (Const_bytearray (a, uu____379), Const_bytearray (b, uu____381)) ->
          a = b
      | (Const_string (a, uu____393), Const_string (b, uu____395)) -> a = b
      | (Const_reflect l1, Const_reflect l2) -> FStar_Ident.lid_equals l1 l2
      | uu____398 -> c1 = c2
let rec (pow2 : FStar_BigInt.bigint -> FStar_BigInt.bigint) =
  fun x ->
    let uu____408 = FStar_BigInt.eq_big_int x FStar_BigInt.zero in
    if uu____408
    then FStar_BigInt.one
    else
      (let uu____410 =
         let uu____411 = FStar_BigInt.pred_big_int x in pow2 uu____411 in
       FStar_BigInt.mult_big_int FStar_BigInt.two uu____410)
let (bounds :
  signedness -> width -> (FStar_BigInt.bigint * FStar_BigInt.bigint)) =
  fun signedness1 ->
    fun width1 ->
      let n =
        match width1 with
        | Int8 -> FStar_BigInt.big_int_of_string "8"
        | Int16 -> FStar_BigInt.big_int_of_string "16"
        | Int32 -> FStar_BigInt.big_int_of_string "32"
        | Int64 -> FStar_BigInt.big_int_of_string "64" in
      let uu____427 =
        match signedness1 with
        | Unsigned ->
            let uu____436 =
              let uu____437 = pow2 n in FStar_BigInt.pred_big_int uu____437 in
            (FStar_BigInt.zero, uu____436)
        | Signed ->
            let upper =
              let uu____439 = FStar_BigInt.pred_big_int n in pow2 uu____439 in
            let uu____440 = FStar_BigInt.minus_big_int upper in
            let uu____441 = FStar_BigInt.pred_big_int upper in
            (uu____440, uu____441) in
      match uu____427 with | (lower, upper) -> (lower, upper)
let (within_bounds : Prims.string -> signedness -> width -> Prims.bool) =
  fun repr ->
    fun signedness1 ->
      fun width1 ->
        let uu____463 = bounds signedness1 width1 in
        match uu____463 with
        | (lower, upper) ->
            let value =
              let uu____471 = FStar_Util.ensure_decimal repr in
              FStar_BigInt.big_int_of_string uu____471 in
            (FStar_BigInt.le_big_int lower value) &&
              (FStar_BigInt.le_big_int value upper)