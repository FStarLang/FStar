open Prims
type signedness =
  | Unsigned 
  | Signed 
let uu___is_Unsigned : signedness -> Prims.bool =
  fun projectee  ->
    match projectee with | Unsigned  -> true | uu____4 -> false
  
let uu___is_Signed : signedness -> Prims.bool =
  fun projectee  -> match projectee with | Signed  -> true | uu____8 -> false 
type width =
  | Int8 
  | Int16 
  | Int32 
  | Int64 
let uu___is_Int8 : width -> Prims.bool =
  fun projectee  -> match projectee with | Int8  -> true | uu____12 -> false 
let uu___is_Int16 : width -> Prims.bool =
  fun projectee  -> match projectee with | Int16  -> true | uu____16 -> false 
let uu___is_Int32 : width -> Prims.bool =
  fun projectee  -> match projectee with | Int32  -> true | uu____20 -> false 
let uu___is_Int64 : width -> Prims.bool =
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
  | Const_string of (FStar_BaseTypes.byte Prims.array,FStar_Range.range)
  FStar_Pervasives_Native.tuple2 
  | Const_range of FStar_Range.range 
  | Const_reify 
  | Const_reflect of FStar_Ident.lid 
let uu___is_Const_effect : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_effect  -> true | uu____71 -> false
  
let uu___is_Const_unit : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_unit  -> true | uu____75 -> false
  
let uu___is_Const_bool : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_bool _0 -> true | uu____80 -> false
  
let __proj__Const_bool__item___0 : sconst -> Prims.bool =
  fun projectee  -> match projectee with | Const_bool _0 -> _0 
let uu___is_Const_int : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_int _0 -> true | uu____97 -> false
  
let __proj__Const_int__item___0 :
  sconst ->
    (Prims.string,(signedness,width) FStar_Pervasives_Native.tuple2
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Const_int _0 -> _0 
let uu___is_Const_char : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_char _0 -> true | uu____124 -> false
  
let __proj__Const_char__item___0 : sconst -> FStar_BaseTypes.char =
  fun projectee  -> match projectee with | Const_char _0 -> _0 
let uu___is_Const_float : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_float _0 -> true | uu____136 -> false
  
let __proj__Const_float__item___0 : sconst -> FStar_BaseTypes.double =
  fun projectee  -> match projectee with | Const_float _0 -> _0 
let uu___is_Const_bytearray : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_bytearray _0 -> true | uu____151 -> false
  
let __proj__Const_bytearray__item___0 :
  sconst ->
    (FStar_BaseTypes.byte Prims.array,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Const_bytearray _0 -> _0 
let uu___is_Const_string : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_string _0 -> true | uu____175 -> false
  
let __proj__Const_string__item___0 :
  sconst ->
    (FStar_BaseTypes.byte Prims.array,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Const_string _0 -> _0 
let uu___is_Const_range : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_range _0 -> true | uu____196 -> false
  
let __proj__Const_range__item___0 : sconst -> FStar_Range.range =
  fun projectee  -> match projectee with | Const_range _0 -> _0 
let uu___is_Const_reify : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_reify  -> true | uu____207 -> false
  
let uu___is_Const_reflect : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_reflect _0 -> true | uu____212 -> false
  
let __proj__Const_reflect__item___0 : sconst -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Const_reflect _0 -> _0 
let eq_const : sconst -> sconst -> Prims.bool =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Const_int (s1,o1),Const_int (s2,o2)) ->
          (let uu____242 = FStar_Util.ensure_decimal s1  in
           let uu____243 = FStar_Util.ensure_decimal s2  in
           uu____242 = uu____243) && (o1 = o2)
      | (Const_bytearray (a,uu____248),Const_bytearray (b,uu____250)) ->
          a = b
      | (Const_string (a,uu____257),Const_string (b,uu____259)) -> a = b
      | (Const_reflect l1,Const_reflect l2) -> FStar_Ident.lid_equals l1 l2
      | uu____267 -> c1 = c2
  
let rec pow2 : Prims.int -> Prims.int =
  fun x  ->
    match x with
    | _0_25 when _0_25 = (Prims.parse_int "0") -> (Prims.parse_int "1")
    | uu____273 ->
        let uu____274 = pow2 (x - (Prims.parse_int "1"))  in
        (Prims.parse_int "2") * uu____274
  
let bounds :
  signedness -> width -> (Prims.int,Prims.int) FStar_Pervasives_Native.tuple2
  =
  fun signedness  ->
    fun width  ->
      let n1 =
        match width with
        | Int8  -> (Prims.parse_int "8")
        | Int16  -> (Prims.parse_int "16")
        | Int32  -> (Prims.parse_int "32")
        | Int64  -> (Prims.parse_int "64")  in
      let uu____284 =
        match signedness with
        | Unsigned  ->
            let uu____289 =
              let uu____290 = pow2 n1  in uu____290 - (Prims.parse_int "1")
               in
            ((Prims.parse_int "0"), uu____289)
        | Signed  ->
            let upper = pow2 (n1 - (Prims.parse_int "1"))  in
            ((- upper), (upper - (Prims.parse_int "1")))
         in
      match uu____284 with | (lower,upper) -> (lower, upper)
  