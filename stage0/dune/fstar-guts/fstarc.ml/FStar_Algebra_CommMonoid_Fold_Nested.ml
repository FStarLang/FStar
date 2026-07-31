open Prims
let transpose_generator (m0 : Prims.int) (mk : Prims.int) (n0 : Prims.int)
  (nk : Prims.int)
  (gen :
    (Obj.t, Obj.t) FStar_IntegerIntervals.ifrom_ito ->
      (Obj.t, Obj.t) FStar_IntegerIntervals.ifrom_ito -> 'c)
  (j : (Obj.t, Obj.t) FStar_IntegerIntervals.ifrom_ito)
  (i : (Obj.t, Obj.t) FStar_IntegerIntervals.ifrom_ito) : 'c= gen i j
let double_fold (eq : 'c FStar_Algebra_CommMonoid_Equiv.equiv)
  (a0 : Prims.int) (ak : Obj.t FStar_IntegerIntervals.not_less_than)
  (b0 : Prims.int) (bk : Obj.t FStar_IntegerIntervals.not_less_than)
  (cm : ('c, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm)
  (g :
    (Obj.t, Obj.t) FStar_IntegerIntervals.ifrom_ito ->
      (Obj.t, Obj.t) FStar_IntegerIntervals.ifrom_ito -> 'c)
  : 'c=
  FStar_Algebra_CommMonoid_Fold.fold eq cm a0 ak
    (fun i -> FStar_Algebra_CommMonoid_Fold.fold eq cm b0 bk (g i))
let matrix_seq (m : Prims.pos) (r : Prims.pos)
  (generator : ('c, Obj.t, Obj.t) FStar_Matrix.matrix_generator) :
  'c FStar_Seq_Base.seq=
  FStar_Matrix.seq_of_matrix m r (FStar_Matrix.init m r generator)
