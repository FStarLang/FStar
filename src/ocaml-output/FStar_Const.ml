open Prims
type signedness =
  | Unsigned
  | Signed[@@deriving show]
let uu___is_Unsigned: signedness -> Prims.bool =
  fun projectee  ->
    match projectee with | Unsigned  -> true | uu____5 -> false
let uu___is_Signed: signedness -> Prims.bool =
  fun projectee  ->
    match projectee with | Signed  -> true | uu____10 -> false
type width =
  | Int8
  | Int16
  | Int32
  | Int64[@@deriving show]
let uu___is_Int8: width -> Prims.bool =
  fun projectee  -> match projectee with | Int8  -> true | uu____15 -> false
let uu___is_Int16: width -> Prims.bool =
  fun projectee  -> match projectee with | Int16  -> true | uu____20 -> false
let uu___is_Int32: width -> Prims.bool =
  fun projectee  -> match projectee with | Int32  -> true | uu____25 -> false
let uu___is_Int64: width -> Prims.bool =
  fun projectee  -> match projectee with | Int64  -> true | uu____30 -> false
type sconst =
  | Const_effect
  | Const_unit
  | Const_bool of Prims.bool
  | Const_int of
  (Prims.string,(signedness,width) FStar_Pervasives_Native.tuple2
                  FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | Const_char of FStar_BaseTypes.char
  | Const_float of FStar_BaseTypes.double
  | Const_bytearray of (FStar_BaseTypes.byte Prims.array,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
  | Const_string of (Prims.string,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
  | Const_range of FStar_Range.range
  | Const_reify
  | Const_reflect of FStar_Ident.lid[@@deriving show]
let uu___is_Const_effect: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_effect  -> true | uu____87 -> false
let uu___is_Const_unit: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_unit  -> true | uu____92 -> false
let uu___is_Const_bool: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_bool _0 -> true | uu____98 -> false
let __proj__Const_bool__item___0: sconst -> Prims.bool =
  fun projectee  -> match projectee with | Const_bool _0 -> _0
let uu___is_Const_int: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_int _0 -> true | uu____122 -> false
let __proj__Const_int__item___0:
  sconst ->
    (Prims.string,(signedness,width) FStar_Pervasives_Native.tuple2
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Const_int _0 -> _0
let uu___is_Const_char: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_char _0 -> true | uu____166 -> false
let __proj__Const_char__item___0: sconst -> FStar_BaseTypes.char =
  fun projectee  -> match projectee with | Const_char _0 -> _0
let uu___is_Const_float: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_float _0 -> true | uu____180 -> false
let __proj__Const_float__item___0: sconst -> FStar_BaseTypes.double =
  fun projectee  -> match projectee with | Const_float _0 -> _0
let uu___is_Const_bytearray: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_bytearray _0 -> true | uu____200 -> false
let __proj__Const_bytearray__item___0:
  sconst ->
    (FStar_BaseTypes.byte Prims.array,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Const_bytearray _0 -> _0
let uu___is_Const_string: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_string _0 -> true | uu____236 -> false
let __proj__Const_string__item___0:
  sconst -> (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Const_string _0 -> _0
let uu___is_Const_range: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_range _0 -> true | uu____262 -> false
let __proj__Const_range__item___0: sconst -> FStar_Range.range =
  fun projectee  -> match projectee with | Const_range _0 -> _0
let uu___is_Const_reify: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_reify  -> true | uu____275 -> false
let uu___is_Const_reflect: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_reflect _0 -> true | uu____281 -> false
let __proj__Const_reflect__item___0: sconst -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Const_reflect _0 -> _0
let eq_const: sconst -> sconst -> Prims.bool =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Const_int (s1,o1),Const_int (s2,o2)) ->
          (let uu____330 = FStar_Util.ensure_decimal s1 in
           let uu____331 = FStar_Util.ensure_decimal s2 in
           uu____330 = uu____331) && (o1 = o2)
      | (Const_bytearray (a,uu____339),Const_bytearray (b,uu____341)) ->
          a = b
      | (Const_string (a,uu____353),Const_string (b,uu____355)) -> a = b
      | (Const_reflect l1,Const_reflect l2) -> FStar_Ident.lid_equals l1 l2
      | uu____358 -> c1 = c2
let rec pow2: FStar_BigInt.bigint -> FStar_BigInt.bigint =
  fun x  ->
    let uu____367 = FStar_BigInt.eq_big_int x FStar_BigInt.zero in
    if uu____367
    then FStar_BigInt.one
    else
      (let uu____369 =
         let uu____370 = FStar_BigInt.pred_big_int x in pow2 uu____370 in
       FStar_BigInt.mult_big_int FStar_BigInt.two uu____369)
let bounds:
  signedness ->
    width ->
      (FStar_BigInt.bigint,FStar_BigInt.bigint)
        FStar_Pervasives_Native.tuple2
  =
  fun signedness  ->
    fun width  ->
      let n1 =
        match width with
        | Int8  -> FStar_BigInt.big_int_of_string "8"
        | Int16  -> FStar_BigInt.big_int_of_string "16"
        | Int32  -> FStar_BigInt.big_int_of_string "32"
        | Int64  -> FStar_BigInt.big_int_of_string "64" in
      let uu____384 =
        match signedness with
        | Unsigned  ->
            let uu____393 =
              let uu____394 = pow2 n1 in FStar_BigInt.pred_big_int uu____394 in
            (FStar_BigInt.zero, uu____393)
        | Signed  ->
            let upper =
              let uu____396 = FStar_BigInt.pred_big_int n1 in pow2 uu____396 in
            let uu____397 = FStar_BigInt.minus_big_int upper in
            let uu____398 = FStar_BigInt.pred_big_int upper in
            (uu____397, uu____398) in
      match uu____384 with | (lower,upper) -> (lower, upper)
let within_bounds: Prims.string -> signedness -> width -> Prims.bool =
  fun repr  ->
    fun signedness  ->
      fun width  ->
        let uu____417 = bounds signedness width in
        match uu____417 with
        | (lower,upper) ->
            let value =
              let uu____425 = FStar_Util.ensure_decimal repr in
              FStar_BigInt.big_int_of_string uu____425 in
            (FStar_BigInt.le_big_int lower value) &&
              (FStar_BigInt.le_big_int value upper)