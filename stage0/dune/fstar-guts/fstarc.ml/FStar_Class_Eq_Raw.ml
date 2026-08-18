open Prims
type 'a deq = {
  eq: 'a -> 'a -> Prims.bool }
let __proj__Mkdeq__item__eq (projectee : 'a deq) : 'a -> 'a -> Prims.bool=
  match projectee with | { eq;_} -> eq
let eq (projectee : 'a deq) : 'a -> 'a -> Prims.bool=
  match projectee with | { eq = eq1;_} -> eq1
let eq_instance_of_eqtype (uu___ : unit) : 'a deq=
  { eq = (fun x y -> x = y) }
let int_has_eq : Prims.int deq= eq_instance_of_eqtype ()
let unit_has_eq : unit deq= eq_instance_of_eqtype ()
let bool_has_eq : Prims.bool deq= eq_instance_of_eqtype ()
let string_has_eq : Prims.string deq= eq_instance_of_eqtype ()
let rec eqList :
  'a .
    ('a -> 'a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list -> Prims.bool
  =
  fun eq1 xs ys ->
    match (xs, ys) with
    | ([], []) -> true
    | (x::xs1, y::ys1) -> (eq1 x y) && (eqList eq1 xs1 ys1)
    | (uu___, uu___1) -> false
let eq_list (uu___ : 'a deq) : 'a Prims.list deq=
  { eq = (eqList (eq uu___)) }
let eq_pair (uu___ : 'a deq) (uu___1 : 'b deq) : ('a * 'b) deq=
  {
    eq =
      (fun uu___2 uu___3 ->
         match (uu___2, uu___3) with
         | ((a1, b1), (c, d)) -> (eq uu___ a1 c) && (eq uu___1 b1 d))
  }
let eq_option (uu___ : 'a deq) : 'a FStar_Pervasives_Native.option deq=
  {
    eq =
      (fun o1 o2 ->
         match (o1, o2) with
         | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
             true
         | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y)
             -> eq uu___ x y
         | (uu___1, uu___2) -> false)
  }
let eq_either (uu___ : 'a deq) (uu___1 : 'b deq) :
  ('a, 'b) FStar_Pervasives.either deq=
  {
    eq =
      (fun x y ->
         match (x, y) with
         | (FStar_Pervasives.Inl a1, FStar_Pervasives.Inl a2) ->
             eq uu___ a1 a2
         | (FStar_Pervasives.Inr b1, FStar_Pervasives.Inr b2) ->
             eq uu___1 b1 b2
         | (uu___2, uu___3) -> false)
  }
let op_Equals : 'a deq -> 'a -> 'a -> Prims.bool= eq
