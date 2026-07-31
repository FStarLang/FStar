open Prims
type 'a deq = {
  raw: 'a FStar_Class_Eq_Raw.deq ;
  eq_dec: unit }
let __proj__Mkdeq__item__raw (projectee : 'a deq) :
  'a FStar_Class_Eq_Raw.deq= match projectee with | { raw; eq_dec;_} -> raw
let raw (projectee : 'a deq) : 'a FStar_Class_Eq_Raw.deq=
  __proj__Mkdeq__item__raw projectee
let deq_raw_deq (d : 'a deq) : 'a FStar_Class_Eq_Raw.deq= d.raw
let eq (d : 'a deq) (x : 'a) (y : 'a) : Prims.bool=
  (d.raw).FStar_Class_Eq_Raw.eq x y
let eq_instance_of_eqtype (uu___ : 'a FStar_Class_Eq_Raw.deq) : 'a deq=
  { raw = (FStar_Class_Eq_Raw.eq_instance_of_eqtype ()); eq_dec = () }
let int_has_eq : Prims.int deq=
  eq_instance_of_eqtype FStar_Class_Eq_Raw.int_has_eq
let unit_has_eq : unit deq=
  eq_instance_of_eqtype FStar_Class_Eq_Raw.unit_has_eq
let bool_has_eq : Prims.bool deq=
  eq_instance_of_eqtype FStar_Class_Eq_Raw.bool_has_eq
let string_has_eq : Prims.string deq=
  eq_instance_of_eqtype FStar_Class_Eq_Raw.string_has_eq
let eq_list (d : 'a deq) : 'a Prims.list deq=
  { raw = (FStar_Class_Eq_Raw.eq_list d.raw); eq_dec = () }
let eq_pair (uu___ : 'a deq) (uu___1 : 'b deq) : ('a * 'b) deq=
  {
    raw =
      (FStar_Class_Eq_Raw.eq_pair (deq_raw_deq uu___) (deq_raw_deq uu___1));
    eq_dec = ()
  }
let eq_option (uu___ : 'a deq) : 'a FStar_Pervasives_Native.option deq=
  { raw = (FStar_Class_Eq_Raw.eq_option (deq_raw_deq uu___)); eq_dec = () }
let op_Equals : 'a deq -> 'a -> 'a -> Prims.bool= eq
