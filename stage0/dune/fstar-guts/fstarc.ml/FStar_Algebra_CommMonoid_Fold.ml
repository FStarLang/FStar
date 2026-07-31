open Prims
let init_func_from_expr (n0 : Prims.int)
  (nk : Obj.t FStar_IntegerIntervals.not_less_than)
  (expr : (Obj.t, Obj.t) FStar_IntegerIntervals.ifrom_ito -> 'c)
  (a : (Obj.t, Obj.t) FStar_IntegerIntervals.ifrom_ito)
  (b : (Obj.t, Obj.t) FStar_IntegerIntervals.ifrom_ito)
  (i :
    (Obj.t, Obj.t, (Obj.t, Obj.t) FStar_IntegerIntervals.ifrom_ito)
      FStar_IntegerIntervals.counter_for)
  : 'c= expr (n0 + i)
let rec fold :
  'c .
    'c FStar_Algebra_CommMonoid_Equiv.equiv ->
      ('c, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm ->
        Prims.int ->
          Obj.t FStar_IntegerIntervals.not_less_than ->
            ((Obj.t, Obj.t) FStar_IntegerIntervals.ifrom_ito -> 'c) -> 'c
  =
  fun eq cm a b expr ->
    if b = a
    then expr b
    else
      FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq cm
        (fold eq cm a (b - Prims.int_one) expr) (expr b)
