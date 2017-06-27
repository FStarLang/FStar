open Prims
type signedness =
  | Unsigned 
  | Signed 
let uu___is_Unsigned : signedness -> Prims.bool =
  fun projectee  ->
    match projectee with | Unsigned  -> true | uu____5 -> false
  
let uu___is_Signed : signedness -> Prims.bool =
  fun projectee  ->
    match projectee with | Signed  -> true | uu____10 -> false
  
type width =
  | Int8 
  | Int16 
  | Int32 
  | Int64 
let uu___is_Int8 : width -> Prims.bool =
  fun projectee  -> match projectee with | Int8  -> true | uu____15 -> false 
let uu___is_Int16 : width -> Prims.bool =
  fun projectee  -> match projectee with | Int16  -> true | uu____20 -> false 
let uu___is_Int32 : width -> Prims.bool =
  fun projectee  -> match projectee with | Int32  -> true | uu____25 -> false 
let uu___is_Int64 : width -> Prims.bool =
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
  | Const_string of (FStar_BaseTypes.byte Prims.array,FStar_Range.range)
  FStar_Pervasives_Native.tuple2 
  | Const_range of FStar_Range.range 
  | Const_reify 
  | Const_reflect of FStar_Ident.lid 
let uu___is_Const_effect : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_effect  -> true | uu____78 -> false
  
let uu___is_Const_unit : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_unit  -> true | uu____83 -> false
  
let uu___is_Const_bool : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_bool _0 -> true | uu____89 -> false
  
let __proj__Const_bool__item___0 : sconst -> Prims.bool =
  fun projectee  -> match projectee with | Const_bool _0 -> _0 
let uu___is_Const_int : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_int _0 -> true | uu____108 -> false
  
let __proj__Const_int__item___0 :
  sconst ->
    (Prims.string,(signedness,width) FStar_Pervasives_Native.tuple2
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Const_int _0 -> _0 
let uu___is_Const_char : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_char _0 -> true | uu____137 -> false
  
let __proj__Const_char__item___0 : sconst -> FStar_BaseTypes.char =
  fun projectee  -> match projectee with | Const_char _0 -> _0 
let uu___is_Const_float : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_float _0 -> true | uu____151 -> false
  
let __proj__Const_float__item___0 : sconst -> FStar_BaseTypes.double =
  fun projectee  -> match projectee with | Const_float _0 -> _0 
let uu___is_Const_bytearray : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_bytearray _0 -> true | uu____168 -> false
  
let __proj__Const_bytearray__item___0 :
  sconst ->
    (FStar_BaseTypes.byte Prims.array,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Const_bytearray _0 -> _0 
let uu___is_Const_string : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_string _0 -> true | uu____194 -> false
  
let __proj__Const_string__item___0 :
  sconst ->
    (FStar_BaseTypes.byte Prims.array,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Const_string _0 -> _0 
let uu___is_Const_range : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_range _0 -> true | uu____217 -> false
  
let __proj__Const_range__item___0 : sconst -> FStar_Range.range =
  fun projectee  -> match projectee with | Const_range _0 -> _0 
let uu___is_Const_reify : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_reify  -> true | uu____230 -> false
  
let uu___is_Const_reflect : sconst -> Prims.bool =
  fun projectee  ->
    match projectee with | Const_reflect _0 -> true | uu____236 -> false
  
let __proj__Const_reflect__item___0 : sconst -> FStar_Ident.lid =
  fun projectee  -> match projectee with | Const_reflect _0 -> _0 
let eq_const : sconst -> sconst -> Prims.bool =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Const_int (s1,o1),Const_int (s2,o2)) ->
          (let uu____273 = FStar_Util.ensure_decimal s1  in
           let uu____274 = FStar_Util.ensure_decimal s2  in
           uu____273 = uu____274) && (o1 = o2)
      | (Const_bytearray (a,uu____279),Const_bytearray (b,uu____281)) ->
          a = b
      | (Const_string (a,uu____288),Const_string (b,uu____290)) -> a = b
      | (Const_reflect l1,Const_reflect l2) -> FStar_Ident.lid_equals l1 l2
      | uu____298 -> c1 = c2
  
let rec pow2 : Prims.int -> Prims.int =
  fun x  ->
    match x with
    | _0_25 when _0_25 = (Prims.parse_int "0") -> (Prims.parse_int "1")
    | uu____305 ->
        let uu____306 = pow2 (x - (Prims.parse_int "1"))  in
        (Prims.parse_int "2") * uu____306
  
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
      let uu____318 =
        match signedness with
        | Unsigned  ->
            let uu____323 =
              let uu____324 = pow2 n1  in uu____324 - (Prims.parse_int "1")
               in
            ((Prims.parse_int "0"), uu____323)
        | Signed  ->
            let upper = pow2 (n1 - (Prims.parse_int "1"))  in
            ((- upper), (upper - (Prims.parse_int "1")))
         in
      match uu____318 with | (lower,upper) -> (lower, upper)
  