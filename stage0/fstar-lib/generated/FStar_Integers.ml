open Prims
let norm : 'a . 'a -> 'a = fun x -> x
type width =
  | W8 
  | W16 
  | W32 
  | W64 
  | W128 
  | Winfinite 
let (uu___is_W8 : width -> Prims.bool) =
  fun projectee -> match projectee with | W8 -> true | uu___ -> false
let (uu___is_W16 : width -> Prims.bool) =
  fun projectee -> match projectee with | W16 -> true | uu___ -> false
let (uu___is_W32 : width -> Prims.bool) =
  fun projectee -> match projectee with | W32 -> true | uu___ -> false
let (uu___is_W64 : width -> Prims.bool) =
  fun projectee -> match projectee with | W64 -> true | uu___ -> false
let (uu___is_W128 : width -> Prims.bool) =
  fun projectee -> match projectee with | W128 -> true | uu___ -> false
let (uu___is_Winfinite : width -> Prims.bool) =
  fun projectee -> match projectee with | Winfinite -> true | uu___ -> false
let (nat_of_width : width -> Prims.int FStar_Pervasives_Native.option) =
  fun uu___ ->
    match uu___ with
    | W8 -> FStar_Pervasives_Native.Some (Prims.of_int (8))
    | W16 -> FStar_Pervasives_Native.Some (Prims.of_int (16))
    | W32 -> FStar_Pervasives_Native.Some (Prims.of_int (32))
    | W64 -> FStar_Pervasives_Native.Some (Prims.of_int (64))
    | W128 -> FStar_Pervasives_Native.Some (Prims.of_int (128))
    | Winfinite -> FStar_Pervasives_Native.None
type fixed_width = width
let (nat_of_fixed_width : fixed_width -> Prims.int) =
  fun w -> match nat_of_width w with | FStar_Pervasives_Native.Some v -> v
type signed_width =
  | Signed of width 
  | Unsigned of fixed_width 
let (uu___is_Signed : signed_width -> Prims.bool) =
  fun projectee -> match projectee with | Signed _0 -> true | uu___ -> false
let (__proj__Signed__item___0 : signed_width -> width) =
  fun projectee -> match projectee with | Signed _0 -> _0
let (uu___is_Unsigned : signed_width -> Prims.bool) =
  fun projectee ->
    match projectee with | Unsigned _0 -> true | uu___ -> false
let (__proj__Unsigned__item___0 : signed_width -> fixed_width) =
  fun projectee -> match projectee with | Unsigned _0 -> _0
let (width_of_sw : signed_width -> width) =
  fun uu___ -> match uu___ with | Signed w -> w | Unsigned w -> w
type ('sw, 'x) within_bounds = Obj.t
type uint_8 = FStar_UInt8.t
type uint_16 = FStar_UInt16.t
type uint_32 = FStar_UInt32.t
type uint_64 = FStar_UInt64.t
type int = Prims.int
type int_8 = FStar_Int8.t
type int_16 = FStar_Int16.t
type int_32 = FStar_Int32.t
type int_64 = FStar_Int64.t
type int_128 = FStar_Int128.t
type ('sw, 'op, 'x, 'y) ok = Obj.t
type nat = Prims.int
type pos = Prims.int
let (f_int : Prims.int -> Prims.int -> Prims.int) = fun x -> fun y -> x + y
let (f_nat : Prims.int -> Prims.int -> Prims.int) = fun x -> fun y -> x + y
let (f_nat_int_pos : Prims.int -> Prims.int -> Prims.int -> Prims.int) =
  fun x -> fun y -> fun z -> (x + y) + z
let (f_uint_8 : FStar_UInt8.t -> FStar_UInt8.t -> FStar_UInt8.t) =
  fun x -> fun y -> FStar_UInt8.add x y
let (f_int_16 : FStar_Int16.t -> FStar_Int16.t -> FStar_Int16.t) =
  fun x -> fun y -> FStar_Int16.add x y
let (g : FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t) =
  fun x -> fun y -> FStar_UInt32.add x (FStar_UInt32.mul y y)
let (h : Prims.nat -> Prims.nat -> Prims.int) = fun x -> fun y -> x + y
let (i : Prims.nat -> Prims.nat -> Prims.int) = fun x -> fun y -> x + y
let (j : Prims.int -> Prims.nat -> Prims.int) = fun x -> fun y -> x - y
let (k : Prims.int -> Prims.int -> Prims.int) = fun x -> fun y -> x * y