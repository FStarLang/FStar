open Prims
type signedness =
  | Unsigned
  | Signed[@@deriving show]
let uu___is_Unsigned: signedness -> Prims.bool =
  fun projectee  ->
    match projectee with | Unsigned  -> true | uu____4 -> false
let uu___is_Signed: signedness -> Prims.bool =
  fun projectee  -> match projectee with | Signed  -> true | uu____8 -> false
type width =
  | Int8
  | Int16
  | Int32
  | Int64[@@deriving show]
let uu___is_Int8: width -> Prims.bool =
  fun projectee  -> match projectee with | Int8  -> true | uu____12 -> false
let uu___is_Int16: width -> Prims.bool =
  fun projectee  -> match projectee with | Int16  -> true | uu____16 -> false
let uu___is_Int32: width -> Prims.bool =
  fun projectee  -> match projectee with | Int32  -> true | uu____20 -> false
let uu___is_Int64: width -> Prims.bool =
  fun projectee  -> match projectee with | Int64  -> true | uu____24 -> false
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
  | Const_range_of
  | Const_set_range_of
  | Const_range of FStar_Range.range
  | Const_reify
  | Const_reflect of FStar_Ident.lid[@@deriving show]
let uu___is_Const_effect: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_effect  -> true | uu____80 -> false
let uu___is_Const_unit: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_unit  -> true | uu____84 -> false
let uu___is_Const_bool: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_bool _0 -> true | uu____89 -> false
let __proj__Const_bool__item___0: sconst -> Prims.bool =
  fun projectee  -> match projectee with | Const_bool _0 -> _0
let uu___is_Const_int: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_int _0 -> true | uu____111 -> false
let __proj__Const_int__item___0:
  sconst ->
    (Prims.string,(signedness,width) FStar_Pervasives_Native.tuple2
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Const_int _0 -> _0
let uu___is_Const_char: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_char _0 -> true | uu____153 -> false
let __proj__Const_char__item___0: sconst -> FStar_BaseTypes.char =
  fun projectee  -> match projectee with | Const_char _0 -> _0
let uu___is_Const_float: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_float _0 -> true | uu____165 -> false
let __proj__Const_float__item___0: sconst -> FStar_BaseTypes.double =
  fun projectee  -> match projectee with | Const_float _0 -> _0
let uu___is_Const_bytearray: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_bytearray _0 -> true | uu____183 -> false
let __proj__Const_bytearray__item___0:
  sconst ->
    (FStar_BaseTypes.byte Prims.array,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Const_bytearray _0 -> _0
let uu___is_Const_string: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_string _0 -> true | uu____217 -> false
let __proj__Const_string__item___0:
  sconst -> (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Const_string _0 -> _0
let uu___is_Const_range_of: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_range_of  -> true | uu____240 -> false
let uu___is_Const_set_range_of: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_set_range_of  -> true | uu____244 -> false
let uu___is_Const_range: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_range _0 -> true | uu____249 -> false
let __proj__Const_range__item___0: sconst -> FStar_Range.range =
  fun projectee  -> match projectee with | Const_range _0 -> _0
let uu___is_Const_reify: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_reify  -> true | uu____260 -> false
let uu___is_Const_reflect: sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_reflect _0 -> true | uu____265 -> false
let __proj__Const_reflect__item___0: sconst -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Const_reflect _0 -> _0
let eq_const: sconst -> sconst -> Prims.bool =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Const_int (s1,o1),Const_int (s2,o2)) ->
          (let uu____311 = FStar_Util.ensure_decimal s1 in
           let uu____312 = FStar_Util.ensure_decimal s2 in
           uu____311 = uu____312) && (o1 = o2)
      | (Const_bytearray (a,uu____320),Const_bytearray (b,uu____322)) ->
          a = b
      | (Const_string (a,uu____334),Const_string (b,uu____336)) -> a = b
      | (Const_reflect l1,Const_reflect l2) -> FStar_Ident.lid_equals l1 l2
      | uu____339 -> c1 = c2
let rec pow2: FStar_BigInt.bigint -> FStar_BigInt.bigint =
  fun x  ->
    let uu____347 = FStar_BigInt.eq_big_int x FStar_BigInt.zero in
    if uu____347
    then FStar_BigInt.one
    else
      (let uu____349 =
         let uu____350 = FStar_BigInt.pred_big_int x in pow2 uu____350 in
       FStar_BigInt.mult_big_int FStar_BigInt.two uu____349)
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
      let uu____362 =
        match signedness with
        | Unsigned  ->
            let uu____371 =
              let uu____372 = pow2 n1 in FStar_BigInt.pred_big_int uu____372 in
            (FStar_BigInt.zero, uu____371)
        | Signed  ->
            let upper =
              let uu____374 = FStar_BigInt.pred_big_int n1 in pow2 uu____374 in
            let uu____375 = FStar_BigInt.minus_big_int upper in
            let uu____376 = FStar_BigInt.pred_big_int upper in
            (uu____375, uu____376) in
      match uu____362 with | (lower,upper) -> (lower, upper)
let within_bounds: Prims.string -> signedness -> width -> Prims.bool =
  fun repr  ->
    fun signedness  ->
      fun width  ->
        let uu____392 = bounds signedness width in
        match uu____392 with
        | (lower,upper) ->
            let value =
              let uu____400 = FStar_Util.ensure_decimal repr in
              FStar_BigInt.big_int_of_string uu____400 in
            (FStar_BigInt.le_big_int lower value) &&
              (FStar_BigInt.le_big_int value upper)