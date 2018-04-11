open Prims
type signedness =
  | Unsigned 
  | Signed [@@deriving show]
let (uu___is_Unsigned : signedness -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unsigned  -> true | uu____6 -> false
  
let (uu___is_Signed : signedness -> Prims.bool) =
  fun projectee  ->
    match projectee with | Signed  -> true | uu____12 -> false
  
type width =
  | Int8 
  | Int16 
  | Int32 
  | Int64 [@@deriving show]
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  -> match projectee with | Int8  -> true | uu____18 -> false 
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  -> match projectee with | Int16  -> true | uu____24 -> false 
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  -> match projectee with | Int32  -> true | uu____30 -> false 
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  -> match projectee with | Int64  -> true | uu____36 -> false 
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
  | Const_reflect of FStar_Ident.lid [@@deriving show]
let (uu___is_Const_effect : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_effect  -> true | uu____94 -> false
  
let (uu___is_Const_unit : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_unit  -> true | uu____100 -> false
  
let (uu___is_Const_bool : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_bool _0 -> true | uu____107 -> false
  
let (__proj__Const_bool__item___0 : sconst -> Prims.bool) =
  fun projectee  -> match projectee with | Const_bool _0 -> _0 
let (uu___is_Const_int : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_int _0 -> true | uu____131 -> false
  
let (__proj__Const_int__item___0 :
  sconst ->
    (Prims.string,(signedness,width) FStar_Pervasives_Native.tuple2
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Const_int _0 -> _0 
let (uu___is_Const_char : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_char _0 -> true | uu____175 -> false
  
let (__proj__Const_char__item___0 : sconst -> FStar_BaseTypes.char) =
  fun projectee  -> match projectee with | Const_char _0 -> _0 
let (uu___is_Const_float : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_float _0 -> true | uu____189 -> false
  
let (__proj__Const_float__item___0 : sconst -> FStar_BaseTypes.double) =
  fun projectee  -> match projectee with | Const_float _0 -> _0 
let (uu___is_Const_bytearray : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_bytearray _0 -> true | uu____209 -> false
  
let (__proj__Const_bytearray__item___0 :
  sconst ->
    (FStar_BaseTypes.byte Prims.array,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Const_bytearray _0 -> _0 
let (uu___is_Const_string : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_string _0 -> true | uu____245 -> false
  
let (__proj__Const_string__item___0 :
  sconst -> (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Const_string _0 -> _0 
let (uu___is_Const_range_of : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_range_of  -> true | uu____270 -> false
  
let (uu___is_Const_set_range_of : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_set_range_of  -> true | uu____276 -> false
  
let (uu___is_Const_range : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_range _0 -> true | uu____283 -> false
  
let (__proj__Const_range__item___0 : sconst -> FStar_Range.range) =
  fun projectee  -> match projectee with | Const_range _0 -> _0 
let (uu___is_Const_reify : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_reify  -> true | uu____296 -> false
  
let (uu___is_Const_reflect : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_reflect _0 -> true | uu____303 -> false
  
let (__proj__Const_reflect__item___0 : sconst -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Const_reflect _0 -> _0 
let (eq_const : sconst -> sconst -> Prims.bool) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Const_int (s1,o1),Const_int (s2,o2)) ->
          (let uu____353 = FStar_Util.ensure_decimal s1  in
           let uu____354 = FStar_Util.ensure_decimal s2  in
           uu____353 = uu____354) && (o1 = o2)
      | (Const_bytearray (a,uu____362),Const_bytearray (b,uu____364)) ->
          a = b
      | (Const_string (a,uu____376),Const_string (b,uu____378)) -> a = b
      | (Const_reflect l1,Const_reflect l2) -> FStar_Ident.lid_equals l1 l2
      | uu____381 -> c1 = c2
  
let rec (pow2 : FStar_BigInt.bigint -> FStar_BigInt.bigint) =
  fun x  ->
    let uu____391 = FStar_BigInt.eq_big_int x FStar_BigInt.zero  in
    if uu____391
    then FStar_BigInt.one
    else
      (let uu____393 =
         let uu____394 = FStar_BigInt.pred_big_int x  in pow2 uu____394  in
       FStar_BigInt.mult_big_int FStar_BigInt.two uu____393)
  
let (bounds :
  signedness ->
    width ->
      (FStar_BigInt.bigint,FStar_BigInt.bigint)
        FStar_Pervasives_Native.tuple2)
  =
  fun signedness  ->
    fun width  ->
      let n1 =
        match width with
        | Int8  -> FStar_BigInt.big_int_of_string "8"
        | Int16  -> FStar_BigInt.big_int_of_string "16"
        | Int32  -> FStar_BigInt.big_int_of_string "32"
        | Int64  -> FStar_BigInt.big_int_of_string "64"  in
      let uu____410 =
        match signedness with
        | Unsigned  ->
            let uu____419 =
              let uu____420 = pow2 n1  in FStar_BigInt.pred_big_int uu____420
               in
            (FStar_BigInt.zero, uu____419)
        | Signed  ->
            let upper =
              let uu____422 = FStar_BigInt.pred_big_int n1  in pow2 uu____422
               in
            let uu____423 = FStar_BigInt.minus_big_int upper  in
            let uu____424 = FStar_BigInt.pred_big_int upper  in
            (uu____423, uu____424)
         in
      match uu____410 with | (lower,upper) -> (lower, upper)
  
let (within_bounds : Prims.string -> signedness -> width -> Prims.bool) =
  fun repr  ->
    fun signedness  ->
      fun width  ->
        let uu____446 = bounds signedness width  in
        match uu____446 with
        | (lower,upper) ->
            let value =
              let uu____454 = FStar_Util.ensure_decimal repr  in
              FStar_BigInt.big_int_of_string uu____454  in
            (FStar_BigInt.le_big_int lower value) &&
              (FStar_BigInt.le_big_int value upper)
  