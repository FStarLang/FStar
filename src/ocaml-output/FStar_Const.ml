open Prims
type signedness =
  | Unsigned 
  | Signed [@@deriving yojson,show]
let (uu___is_Unsigned : signedness -> Prims.bool) =
  fun projectee -> match projectee with | Unsigned -> true | uu____8 -> false
let (uu___is_Signed : signedness -> Prims.bool) =
  fun projectee -> match projectee with | Signed -> true | uu____19 -> false
type width =
  | Int8 
  | Int16 
  | Int32 
  | Int64 [@@deriving yojson,show]
let (uu___is_Int8 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int8 -> true | uu____30 -> false
let (uu___is_Int16 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int16 -> true | uu____41 -> false
let (uu___is_Int32 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int32 -> true | uu____52 -> false
let (uu___is_Int64 : width -> Prims.bool) =
  fun projectee -> match projectee with | Int64 -> true | uu____63 -> false
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
    match projectee with | Const_effect -> true | uu____144 -> false
let (uu___is_Const_unit : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_unit -> true | uu____155 -> false
let (uu___is_Const_bool : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_bool _0 -> true | uu____168 -> false
let (__proj__Const_bool__item___0 : sconst -> Prims.bool) =
  fun projectee -> match projectee with | Const_bool _0 -> _0
let (uu___is_Const_int : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_int _0 -> true | uu____201 -> false
let (__proj__Const_int__item___0 :
  sconst ->
    (Prims.string * (signedness * width) FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Const_int _0 -> _0
let (uu___is_Const_char : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_char _0 -> true | uu____254 -> false
let (__proj__Const_char__item___0 : sconst -> FStar_BaseTypes.char) =
  fun projectee -> match projectee with | Const_char _0 -> _0
let (uu___is_Const_float : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_float _0 -> true | uu____276 -> false
let (__proj__Const_float__item___0 : sconst -> FStar_BaseTypes.double) =
  fun projectee -> match projectee with | Const_float _0 -> _0
let (uu___is_Const_real : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_real _0 -> true | uu____296 -> false
let (__proj__Const_real__item___0 : sconst -> Prims.string) =
  fun projectee -> match projectee with | Const_real _0 -> _0
let (uu___is_Const_bytearray : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_bytearray _0 -> true | uu____324 -> false
let (__proj__Const_bytearray__item___0 :
  sconst -> (FStar_BaseTypes.byte Prims.array * FStar_Range.range)) =
  fun projectee -> match projectee with | Const_bytearray _0 -> _0
let (uu___is_Const_string : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_string _0 -> true | uu____366 -> false
let (__proj__Const_string__item___0 :
  sconst -> (Prims.string * FStar_Range.range)) =
  fun projectee -> match projectee with | Const_string _0 -> _0
let (uu___is_Const_range_of : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_range_of -> true | uu____399 -> false
let (uu___is_Const_set_range_of : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_set_range_of -> true | uu____410 -> false
let (uu___is_Const_range : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_range _0 -> true | uu____422 -> false
let (__proj__Const_range__item___0 : sconst -> FStar_Range.range) =
  fun projectee -> match projectee with | Const_range _0 -> _0
let (uu___is_Const_reify : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_reify -> true | uu____440 -> false
let (uu___is_Const_reflect : sconst -> Prims.bool) =
  fun projectee ->
    match projectee with | Const_reflect _0 -> true | uu____452 -> false
let (__proj__Const_reflect__item___0 : sconst -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Const_reflect _0 -> _0
let (eq_const : sconst -> sconst -> Prims.bool) =
  fun c1 ->
    fun c2 ->
      match (c1, c2) with
      | (Const_int (s1, o1), Const_int (s2, o2)) ->
          (let uu____510 = FStar_Util.ensure_decimal s1 in
           let uu____512 = FStar_Util.ensure_decimal s2 in
           uu____510 = uu____512) && (o1 = o2)
      | (Const_bytearray (a, uu____522), Const_bytearray (b, uu____524)) ->
          a = b
      | (Const_string (a, uu____536), Const_string (b, uu____538)) -> a = b
      | (Const_reflect l1, Const_reflect l2) -> FStar_Ident.lid_equals l1 l2
      | uu____546 -> c1 = c2
let rec (pow2 : FStar_BigInt.bigint -> FStar_BigInt.bigint) =
  fun x ->
    let uu____557 = FStar_BigInt.eq_big_int x FStar_BigInt.zero in
    if uu____557
    then FStar_BigInt.one
    else
      (let uu____562 =
         let uu____563 = FStar_BigInt.pred_big_int x in pow2 uu____563 in
       FStar_BigInt.mult_big_int FStar_BigInt.two uu____562)
let (bounds :
  signedness -> width -> (FStar_BigInt.bigint * FStar_BigInt.bigint)) =
  fun signedness ->
    fun width ->
      let n1 =
        match width with
        | Int8 -> FStar_BigInt.big_int_of_string "8"
        | Int16 -> FStar_BigInt.big_int_of_string "16"
        | Int32 -> FStar_BigInt.big_int_of_string "32"
        | Int64 -> FStar_BigInt.big_int_of_string "64" in
      let uu____584 =
        match signedness with
        | Unsigned ->
            let uu____593 =
              let uu____594 = pow2 n1 in FStar_BigInt.pred_big_int uu____594 in
            (FStar_BigInt.zero, uu____593)
        | Signed ->
            let upper =
              let uu____596 = FStar_BigInt.pred_big_int n1 in pow2 uu____596 in
            let uu____597 = FStar_BigInt.minus_big_int upper in
            let uu____598 = FStar_BigInt.pred_big_int upper in
            (uu____597, uu____598) in
      match uu____584 with | (lower, upper) -> (lower, upper)
let (within_bounds : Prims.string -> signedness -> width -> Prims.bool) =
  fun repr ->
    fun signedness ->
      fun width ->
        let uu____624 = bounds signedness width in
        match uu____624 with
        | (lower, upper) ->
            let value =
              let uu____633 = FStar_Util.ensure_decimal repr in
              FStar_BigInt.big_int_of_string uu____633 in
            (FStar_BigInt.le_big_int lower value) &&
              (FStar_BigInt.le_big_int value upper)