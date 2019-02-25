open Prims
type signedness =
  | Unsigned 
  | Signed [@@deriving yojson,show]
let (uu___is_Unsigned : signedness -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unsigned  -> true | uu____32579 -> false
  
let (uu___is_Signed : signedness -> Prims.bool) =
  fun projectee  ->
    match projectee with | Signed  -> true | uu____32590 -> false
  
type width =
  | Int8 
  | Int16 
  | Int32 
  | Int64 [@@deriving yojson,show]
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int8  -> true | uu____32601 -> false
  
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int16  -> true | uu____32612 -> false
  
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int32  -> true | uu____32623 -> false
  
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int64  -> true | uu____32634 -> false
  
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
    match projectee with | Const_effect  -> true | uu____32715 -> false
  
let (uu___is_Const_unit : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_unit  -> true | uu____32726 -> false
  
let (uu___is_Const_bool : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_bool _0 -> true | uu____32739 -> false
  
let (__proj__Const_bool__item___0 : sconst -> Prims.bool) =
  fun projectee  -> match projectee with | Const_bool _0 -> _0 
let (uu___is_Const_int : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_int _0 -> true | uu____32773 -> false
  
let (__proj__Const_int__item___0 :
  sconst ->
    (Prims.string * (signedness * width) FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Const_int _0 -> _0 
let (uu___is_Const_char : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_char _0 -> true | uu____32827 -> false
  
let (__proj__Const_char__item___0 : sconst -> FStar_BaseTypes.char) =
  fun projectee  -> match projectee with | Const_char _0 -> _0 
let (uu___is_Const_float : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_float _0 -> true | uu____32850 -> false
  
let (__proj__Const_float__item___0 : sconst -> FStar_BaseTypes.double) =
  fun projectee  -> match projectee with | Const_float _0 -> _0 
let (uu___is_Const_real : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_real _0 -> true | uu____32871 -> false
  
let (__proj__Const_real__item___0 : sconst -> Prims.string) =
  fun projectee  -> match projectee with | Const_real _0 -> _0 
let (uu___is_Const_bytearray : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_bytearray _0 -> true | uu____32900 -> false
  
let (__proj__Const_bytearray__item___0 :
  sconst -> (FStar_BaseTypes.byte Prims.array * FStar_Range.range)) =
  fun projectee  -> match projectee with | Const_bytearray _0 -> _0 
let (uu___is_Const_string : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_string _0 -> true | uu____32943 -> false
  
let (__proj__Const_string__item___0 :
  sconst -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Const_string _0 -> _0 
let (uu___is_Const_range_of : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_range_of  -> true | uu____32977 -> false
  
let (uu___is_Const_set_range_of : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_set_range_of  -> true | uu____32988 -> false
  
let (uu___is_Const_range : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_range _0 -> true | uu____33000 -> false
  
let (__proj__Const_range__item___0 : sconst -> FStar_Range.range) =
  fun projectee  -> match projectee with | Const_range _0 -> _0 
let (uu___is_Const_reify : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_reify  -> true | uu____33019 -> false
  
let (uu___is_Const_reflect : sconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const_reflect _0 -> true | uu____33031 -> false
  
let (__proj__Const_reflect__item___0 : sconst -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | Const_reflect _0 -> _0 
let (eq_const : sconst -> sconst -> Prims.bool) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Const_int (s1,o1),Const_int (s2,o2)) ->
          (let uu____33090 = FStar_Util.ensure_decimal s1  in
           let uu____33092 = FStar_Util.ensure_decimal s2  in
           uu____33090 = uu____33092) && (o1 = o2)
      | (Const_bytearray (a,uu____33102),Const_bytearray (b,uu____33104)) ->
          a = b
      | (Const_string (a,uu____33116),Const_string (b,uu____33118)) -> a = b
      | (Const_reflect l1,Const_reflect l2) -> FStar_Ident.lid_equals l1 l2
      | uu____33126 -> c1 = c2
  
let rec (pow2 : FStar_BigInt.bigint -> FStar_BigInt.bigint) =
  fun x  ->
    let uu____33137 = FStar_BigInt.eq_big_int x FStar_BigInt.zero  in
    if uu____33137
    then FStar_BigInt.one
    else
      (let uu____33142 =
         let uu____33143 = FStar_BigInt.pred_big_int x  in pow2 uu____33143
          in
       FStar_BigInt.mult_big_int FStar_BigInt.two uu____33142)
  
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
      let uu____33164 =
        match signedness with
        | Unsigned  ->
            let uu____33173 =
              let uu____33174 = pow2 n1  in
              FStar_BigInt.pred_big_int uu____33174  in
            (FStar_BigInt.zero, uu____33173)
        | Signed  ->
            let upper =
              let uu____33176 = FStar_BigInt.pred_big_int n1  in
              pow2 uu____33176  in
            let uu____33177 = FStar_BigInt.minus_big_int upper  in
            let uu____33178 = FStar_BigInt.pred_big_int upper  in
            (uu____33177, uu____33178)
         in
      match uu____33164 with | (lower,upper) -> (lower, upper)
  
let (within_bounds : Prims.string -> signedness -> width -> Prims.bool) =
  fun repr  ->
    fun signedness  ->
      fun width  ->
        let uu____33204 = bounds signedness width  in
        match uu____33204 with
        | (lower,upper) ->
            let value =
              let uu____33213 = FStar_Util.ensure_decimal repr  in
              FStar_BigInt.big_int_of_string uu____33213  in
            (FStar_BigInt.le_big_int lower value) &&
              (FStar_BigInt.le_big_int value upper)
  