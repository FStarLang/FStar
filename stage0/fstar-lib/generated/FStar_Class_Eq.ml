open Prims
type ('a, 'f) decides_eq = unit
type 'a deq = {
  raw: 'a FStar_Class_Eq_Raw.deq ;
  eq_dec: unit }
let __proj__Mkdeq__item__raw : 'a . 'a deq -> 'a FStar_Class_Eq_Raw.deq =
  fun projectee -> match projectee with | { raw; eq_dec;_} -> raw
let raw : 'a . 'a deq -> 'a FStar_Class_Eq_Raw.deq =
  fun projectee -> match projectee with | { raw = raw1; eq_dec;_} -> raw1
let deq_raw_deq : 'a . 'a deq -> 'a FStar_Class_Eq_Raw.deq = fun d -> d.raw
let eq : 'a . 'a deq -> 'a -> 'a -> Prims.bool =
  fun d -> fun x -> fun y -> (d.raw).FStar_Class_Eq_Raw.eq x y
let eq_instance_of_eqtype : 'a . 'a FStar_Class_Eq_Raw.deq -> 'a deq =
  fun uu___ ->
    { raw = (FStar_Class_Eq_Raw.eq_instance_of_eqtype ()); eq_dec = () }
let (int_has_eq : Prims.int deq) =
  eq_instance_of_eqtype FStar_Class_Eq_Raw.int_has_eq
let (unit_has_eq : unit deq) =
  eq_instance_of_eqtype FStar_Class_Eq_Raw.unit_has_eq
let (bool_has_eq : Prims.bool deq) =
  eq_instance_of_eqtype FStar_Class_Eq_Raw.bool_has_eq
let (string_has_eq : Prims.string deq) =
  eq_instance_of_eqtype FStar_Class_Eq_Raw.string_has_eq
let eq_list : 'a . 'a deq -> 'a Prims.list deq =
  fun d -> { raw = (FStar_Class_Eq_Raw.eq_list d.raw); eq_dec = () }
let eq_pair : 'a 'b . 'a deq -> 'b deq -> ('a * 'b) deq =
  fun uu___ ->
    fun uu___1 ->
      {
        raw =
          (FStar_Class_Eq_Raw.eq_pair (deq_raw_deq uu___)
             (deq_raw_deq uu___1));
        eq_dec = ()
      }
let eq_option : 'a . 'a deq -> 'a FStar_Pervasives_Native.option deq =
  fun uu___ ->
    { raw = (FStar_Class_Eq_Raw.eq_option (deq_raw_deq uu___)); eq_dec = () }
let op_Equals : 'a . 'a deq -> 'a -> 'a -> Prims.bool = eq