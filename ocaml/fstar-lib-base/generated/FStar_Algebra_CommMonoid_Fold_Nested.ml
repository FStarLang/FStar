open Prims
let transpose_generator :
  'c .
    Prims.int ->
      Prims.int ->
        Prims.int ->
          Prims.int ->
            ((unit, unit) FStar_IntegerIntervals.ifrom_ito ->
               (unit, unit) FStar_IntegerIntervals.ifrom_ito -> 'c)
              ->
              (unit, unit) FStar_IntegerIntervals.ifrom_ito ->
                (unit, unit) FStar_IntegerIntervals.ifrom_ito -> 'c
  =
  fun m0 ->
    fun mk -> fun n0 -> fun nk -> fun gen -> fun j -> fun i -> gen i j
let double_fold :
  'c .
    'c FStar_Algebra_CommMonoid_Equiv.equiv ->
      Prims.int ->
        unit FStar_IntegerIntervals.not_less_than ->
          Prims.int ->
            unit FStar_IntegerIntervals.not_less_than ->
              ('c, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
                ((unit, unit) FStar_IntegerIntervals.ifrom_ito ->
                   (unit, unit) FStar_IntegerIntervals.ifrom_ito -> 'c)
                  -> 'c
  =
  fun eq ->
    fun a0 ->
      fun ak ->
        fun b0 ->
          fun bk ->
            fun cm ->
              fun g ->
                FStar_Algebra_CommMonoid_Fold.fold eq cm a0 ak
                  (fun i ->
                     FStar_Algebra_CommMonoid_Fold.fold eq cm b0 bk (g i))
let matrix_seq :
  'c .
    Prims.pos ->
      Prims.pos ->
        ('c, unit, unit) FStar_Matrix.matrix_generator ->
          'c FStar_Seq_Base.seq
  =
  fun m ->
    fun r ->
      fun generator ->
        FStar_Matrix.seq_of_matrix m r (FStar_Matrix.init m r generator)