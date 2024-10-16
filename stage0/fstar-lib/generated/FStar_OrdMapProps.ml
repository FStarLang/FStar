open Prims
let rec fold :
  'k 'v 't .
    'k FStar_OrdMap.cmp ->
      ('k -> 'v -> 't -> 't) ->
        ('k, 'v, unit) FStar_OrdMap.ordmap -> 't -> 't
  =
  fun f ->
    fun g ->
      fun m ->
        fun a ->
          if (FStar_OrdMap.size f m) = Prims.int_zero
          then a
          else
            (let uu___1 = FStar_OrdMap.choose f m in
             match uu___1 with
             | FStar_Pervasives_Native.Some (k1, v1) ->
                 fold f g (FStar_OrdMap.remove f k1 m) (g k1 v1 a))