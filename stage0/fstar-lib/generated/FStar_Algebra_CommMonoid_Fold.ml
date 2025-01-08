open Prims
let init_func_from_expr :
  'c .
    Prims.int ->
      unit FStar_IntegerIntervals.not_less_than ->
        ((unit, unit) FStar_IntegerIntervals.ifrom_ito -> 'c) ->
          (unit, unit) FStar_IntegerIntervals.ifrom_ito ->
            (unit, unit) FStar_IntegerIntervals.ifrom_ito ->
              (unit, unit, (unit, unit) FStar_IntegerIntervals.ifrom_ito)
                FStar_IntegerIntervals.counter_for -> 'c
  = fun n0 -> fun nk -> fun expr -> fun a -> fun b -> fun i -> expr (n0 + i)
let rec fold :
  'c .
    'c FStar_Algebra_CommMonoid_Equiv.equiv ->
      ('c, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
        Prims.int ->
          unit FStar_IntegerIntervals.not_less_than ->
            ((unit, unit) FStar_IntegerIntervals.ifrom_ito -> 'c) -> 'c
  =
  fun eq ->
    fun cm ->
      fun a ->
        fun b ->
          fun expr ->
            if b = a
            then expr b
            else
              FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq cm
                (fold eq cm a (b - Prims.int_one) expr) (expr b)