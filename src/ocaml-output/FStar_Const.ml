open Prims
type signedness =
  | Unsigned 
  | Signed [@@deriving yojson,show]
let (uu___is_Unsigned : signedness -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unsigned  -> true | uu____29070 -> false
  
let (uu___is_Signed : signedness -> Prims.bool) =
  fun projectee  ->
    match projectee with | Signed  -> true | uu____29081 -> false
  
type width =
  | Int8 
  | Int16 
  | Int32 
  | Int64 [@@deriving yojson,show]
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____29092 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____29103 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____29114 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____29125 -> false
  
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
  fun projectee  ->
    match projectee with | Const_effect  -> true | uu____29206 -> false
  
let (uu___is_Const_unit : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_unit  -> true | uu____29217 -> false
  
let (uu___is_Const_bool : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_bool _0 -> true | uu____29230 -> false
  
let (__proj__Const_bool__item___0 : sconst -> Prims.bool) =
  fun projectee  -> match projectee with | Const_bool _0 -> _0 
let (uu___is_Const_int : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_int _0 -> true | uu____29264 -> false
  
let (__proj__Const_int__item___0 :
  sconst ->
    (Prims.string * (signedness * width) FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Const_int _0 -> _0 
let (uu___is_Const_char : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_char _0 -> true | uu____29318 -> false
  
let (__proj__Const_char__item___0 : sconst -> FStar_BaseTypes.char) =
  fun projectee  -> match projectee with | Const_char _0 -> _0 
let (uu___is_Const_float : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_float _0 -> true | uu____29341 -> false
  
let (__proj__Const_float__item___0 : sconst -> FStar_BaseTypes.double) =
  fun projectee  -> match projectee with | Const_float _0 -> _0 
let (uu___is_Const_real : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_real _0 -> true | uu____29362 -> false
  
let (__proj__Const_real__item___0 : sconst -> Prims.string) =
  fun projectee  -> match projectee with | Const_real _0 -> _0 
let (uu___is_Const_bytearray : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_bytearray _0 -> true | uu____29391 -> false
  
let (__proj__Const_bytearray__item___0 :
  sconst -> (FStar_BaseTypes.byte Prims.array * FStar_Range.range)) =
  fun projectee  -> match projectee with | Const_bytearray _0 -> _0 
let (uu___is_Const_string : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_string _0 -> true | uu____29434 -> false
  
let (__proj__Const_string__item___0 :
  sconst -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Const_string _0 -> _0 
let (uu___is_Const_range_of : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_range_of  -> true | uu____29468 -> false
  
let (uu___is_Const_set_range_of : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_set_range_of  -> true | uu____29479 -> false
  
let (uu___is_Const_range : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_range _0 -> true | uu____29491 -> false
  
let (__proj__Const_range__item___0 : sconst -> FStar_Range.range) =
  fun projectee  -> match projectee with | Const_range _0 -> _0 
let (uu___is_Const_reify : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_reify  -> true | uu____29510 -> false
  
let (uu___is_Const_reflect : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_reflect _0 -> true | uu____29522 -> false
  
let (__proj__Const_reflect__item___0 : sconst -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Const_reflect _0 -> _0 
let (eq_const : sconst -> sconst -> Prims.bool) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Const_int (s1,o1),Const_int (s2,o2)) ->
          (let uu____29581 = FStar_Util.ensure_decimal s1  in
           let uu____29583 = FStar_Util.ensure_decimal s2  in
           uu____29581 = uu____29583) && (o1 = o2)
      | (Const_bytearray (a,uu____29593),Const_bytearray (b,uu____29595)) ->
          a = b
      | (Const_string (a,uu____29607),Const_string (b,uu____29609)) -> a = b
      | (Const_reflect l1,Const_reflect l2) -> FStar_Ident.lid_equals l1 l2
      | uu____29617 -> c1 = c2
  
let rec (pow2 : FStar_BigInt.bigint -> FStar_BigInt.bigint) =
  fun x  ->
    let uu____29628 = FStar_BigInt.eq_big_int x FStar_BigInt.zero  in
    if uu____29628
    then FStar_BigInt.one
    else
      (let uu____29633 =
         let uu____29634 = FStar_BigInt.pred_big_int x  in pow2 uu____29634
          in
       FStar_BigInt.mult_big_int FStar_BigInt.two uu____29633)
  
let (bounds :
  signedness -> width -> (FStar_BigInt.bigint * FStar_BigInt.bigint)) =
  fun signedness  ->
    fun width  ->
      let n1 =
        match width with
        | Int8  -> FStar_BigInt.big_int_of_string "8"
        | Int16  -> FStar_BigInt.big_int_of_string "16"
        | Int32  -> FStar_BigInt.big_int_of_string "32"
        | Int64  -> FStar_BigInt.big_int_of_string "64"  in
      let uu____29655 =
        match signedness with
        | Unsigned  ->
            let uu____29664 =
              let uu____29665 = pow2 n1  in
              FStar_BigInt.pred_big_int uu____29665  in
            (FStar_BigInt.zero, uu____29664)
        | Signed  ->
            let upper =
              let uu____29667 = FStar_BigInt.pred_big_int n1  in
              pow2 uu____29667  in
            let uu____29668 = FStar_BigInt.minus_big_int upper  in
            let uu____29669 = FStar_BigInt.pred_big_int upper  in
            (uu____29668, uu____29669)
         in
      match uu____29655 with | (lower,upper) -> (lower, upper)
  
let (within_bounds : Prims.string -> signedness -> width -> Prims.bool) =
  fun repr  ->
    fun signedness  ->
      fun width  ->
        let uu____29695 = bounds signedness width  in
        match uu____29695 with
        | (lower,upper) ->
            let value =
              let uu____29704 = FStar_Util.ensure_decimal repr  in
              FStar_BigInt.big_int_of_string uu____29704  in
            (FStar_BigInt.le_big_int lower value) &&
              (FStar_BigInt.le_big_int value upper)
  