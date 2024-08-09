open Prims
type ('c, 'eq, 's1, 's2) eq_of_seq = Obj.t
let seq_equiv :
  'c .
    'c FStar_Algebra_CommMonoid_Equiv.equiv ->
      'c FStar_Seq_Base.seq FStar_Algebra_CommMonoid_Equiv.equiv
  = fun eq -> FStar_Algebra_CommMonoid_Equiv.EQ ((), (), (), ())