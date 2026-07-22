open Prims
type ('c, 'm, 'n) matrix_generator =
  'm FStar_IntegerIntervals.under -> 'n FStar_IntegerIntervals.under -> 'c
type ('c, 'm, 'n) matrix = 'c FStar_Seq_Base.seq
let get_ij (m : Prims.pos) (n : Prims.pos)
  (i : Obj.t FStar_IntegerIntervals.under)
  (j : Obj.t FStar_IntegerIntervals.under) :
  Obj.t FStar_IntegerIntervals.under= (i * n) + j
let get_i (m : Prims.pos) (n : Prims.pos)
  (ij : Obj.t FStar_IntegerIntervals.under) :
  Obj.t FStar_IntegerIntervals.under= ij / n
let get_j (m : Prims.pos) (n : Prims.pos)
  (ij : Obj.t FStar_IntegerIntervals.under) :
  Obj.t FStar_IntegerIntervals.under= (mod) ij n
let transpose_ji (m : Prims.pos) (n : Prims.pos)
  (ij : Obj.t FStar_IntegerIntervals.under) :
  Obj.t FStar_IntegerIntervals.under= ((get_j m n ij) * m) + (get_i m n ij)
let seq_of_matrix (m : Prims.pos) (n : Prims.pos)
  (mx : ('c, Obj.t, Obj.t) matrix) : 'c FStar_Seq_Base.seq= mx
let ijth (m : Prims.pos) (n : Prims.pos) (mx : ('c, Obj.t, Obj.t) matrix)
  (i : Obj.t FStar_IntegerIntervals.under)
  (j : Obj.t FStar_IntegerIntervals.under) : 'c=
  FStar_Seq_Base.index mx (get_ij m n i j)
let matrix_of_seq (m : Prims.pos) (n : Prims.pos) (s : 'c FStar_Seq_Base.seq)
  : ('c, Obj.t, Obj.t) matrix= s
type ('c, 'm, 'n, 'gen) matrix_of = ('c, 'm, 'n) matrix
let foldm (eq : 'c FStar_Algebra_CommMonoid_Equiv.equiv) (m : Prims.pos)
  (n : Prims.pos) (cm : ('c, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm)
  (mx : ('c, Obj.t, Obj.t) matrix) : 'c=
  FStar_Seq_Permutation.foldm_snoc eq cm mx
let init (m : Prims.pos) (n : Prims.pos)
  (generator : ('c, Obj.t, Obj.t) matrix_generator) :
  ('c, Obj.t, Obj.t, Obj.t) matrix_of=
  let mn = m * n in
  let generator_ij ij = generator (get_i m n ij) (get_j m n ij) in
  let flat_indices = FStar_IntegerIntervals.indices_seq mn in
  let result = FStar_Seq_Properties.map_seq generator_ij flat_indices in
  result
let matrix_seq (m : Prims.pos) (n : Prims.pos)
  (gen : ('c, Obj.t, Obj.t) matrix_generator) : 'c FStar_Seq_Base.seq=
  init m n gen
let transposed_matrix_gen (m : Prims.pos) (n : Prims.pos)
  (generator : ('c, Obj.t, Obj.t) matrix_generator) :
  ('c, Obj.t, Obj.t) matrix_generator= fun j i -> generator i j
let matrix_equiv (eq : 'c FStar_Algebra_CommMonoid_Equiv.equiv)
  (m : Prims.pos) (n : Prims.pos) :
  ('c, Obj.t, Obj.t) matrix FStar_Algebra_CommMonoid_Equiv.equiv=
  FStar_Algebra_CommMonoid_Equiv.EQ ((), (), (), ())
let matrix_add_generator (eq : 'c FStar_Algebra_CommMonoid_Equiv.equiv)
  (m : Prims.pos) (n : Prims.pos)
  (add : ('c, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm)
  (ma : ('c, Obj.t, Obj.t) matrix) (mb : ('c, Obj.t, Obj.t) matrix) :
  ('c, Obj.t, Obj.t) matrix_generator=
  fun i j ->
    FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq add
      (ijth m n ma i j) (ijth m n mb i j)
let matrix_add (eq : 'c FStar_Algebra_CommMonoid_Equiv.equiv) (m : Prims.pos)
  (n : Prims.pos) (add : ('c, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm)
  (ma : ('c, Obj.t, Obj.t) matrix) (mb : ('c, Obj.t, Obj.t) matrix) :
  ('c, Obj.t, Obj.t, Obj.t) matrix_of=
  init m n (matrix_add_generator eq m n add ma mb)
let matrix_add_zero (eq : 'c FStar_Algebra_CommMonoid_Equiv.equiv)
  (add : ('c, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm) (m : Prims.pos)
  (n : Prims.pos) : ('c, Obj.t, Obj.t) matrix=
  matrix_of_seq m n
    (FStar_Seq_Base.create (m * n)
       (FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__unit eq add))
let matrix_add_comm_monoid (eq : 'c FStar_Algebra_CommMonoid_Equiv.equiv)
  (add : ('c, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm) (m : Prims.pos)
  (n : Prims.pos) :
  (('c, Obj.t, Obj.t) matrix, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm=
  FStar_Algebra_CommMonoid_Equiv.CM
    ((matrix_add_zero eq add m n), (matrix_add eq m n add), (), (), (), ())
let col (m : Prims.pos) (n : Prims.pos) (mx : ('c, Obj.t, Obj.t) matrix)
  (j : Obj.t FStar_IntegerIntervals.under) : 'c FStar_Seq_Base.seq=
  if m = Prims.int_zero
  then FStar_Seq_Base.MkSeq []
  else FStar_Seq_Base.init_aux m Prims.int_zero (fun i -> ijth m n mx i j)
let row (m : Prims.pos) (n : Prims.pos) (mx : ('c, Obj.t, Obj.t) matrix)
  (i : Obj.t FStar_IntegerIntervals.under) : 'c FStar_Seq_Base.seq=
  if n = Prims.int_zero
  then FStar_Seq_Base.MkSeq []
  else FStar_Seq_Base.init_aux n Prims.int_zero (fun j -> ijth m n mx i j)
let seq_op_const (eq : 'c FStar_Algebra_CommMonoid_Equiv.equiv)
  (cm : ('c, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm)
  (s : 'c FStar_Seq_Base.seq) (const : 'c) : 'c FStar_Seq_Base.seq=
  if (FStar_Seq_Base.length s) = Prims.int_zero
  then FStar_Seq_Base.MkSeq []
  else
    FStar_Seq_Base.init_aux (FStar_Seq_Base.length s) Prims.int_zero
      (fun i ->
         FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq cm
           (FStar_Seq_Base.index s i) const)
let const_op_seq (eq : 'c FStar_Algebra_CommMonoid_Equiv.equiv)
  (cm : ('c, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm) (const : 'c)
  (s : 'c FStar_Seq_Base.seq) : 'c FStar_Seq_Base.seq=
  if (FStar_Seq_Base.length s) = Prims.int_zero
  then FStar_Seq_Base.MkSeq []
  else
    FStar_Seq_Base.init_aux (FStar_Seq_Base.length s) Prims.int_zero
      (fun i ->
         FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq cm const
           (FStar_Seq_Base.index s i))
let seq_of_products (eq : 'c FStar_Algebra_CommMonoid_Equiv.equiv)
  (mul : ('c, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm)
  (s : 'c FStar_Seq_Base.seq) (t : 'c FStar_Seq_Base.seq) :
  'c FStar_Seq_Base.seq=
  if (FStar_Seq_Base.length s) = Prims.int_zero
  then FStar_Seq_Base.MkSeq []
  else
    FStar_Seq_Base.init_aux (FStar_Seq_Base.length s) Prims.int_zero
      (fun i ->
         FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq mul
           (FStar_Seq_Base.index s i) (FStar_Seq_Base.index t i))
let dot (eq : 'c FStar_Algebra_CommMonoid_Equiv.equiv)
  (add : ('c, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm)
  (mul : ('c, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm)
  (s : 'c FStar_Seq_Base.seq) (t : 'c FStar_Seq_Base.seq) : 'c=
  FStar_Seq_Permutation.foldm_snoc eq add (seq_of_products eq mul s t)
let matrix_mul_gen (eq : 'c FStar_Algebra_CommMonoid_Equiv.equiv)
  (m : Prims.pos) (n : Prims.pos) (p : Prims.pos)
  (add : ('c, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm)
  (mul : ('c, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm)
  (mx : ('c, Obj.t, Obj.t) matrix) (my : ('c, Obj.t, Obj.t) matrix)
  (i : Obj.t FStar_IntegerIntervals.under)
  (k : Obj.t FStar_IntegerIntervals.under) : 'c=
  dot eq add mul (row m n mx i) (col n p my k)
let matrix_mul (eq : 'c FStar_Algebra_CommMonoid_Equiv.equiv) (m : Prims.pos)
  (n : Prims.pos) (p : Prims.pos)
  (add : ('c, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm)
  (mul : ('c, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm)
  (mx : ('c, Obj.t, Obj.t) matrix) (my : ('c, Obj.t, Obj.t) matrix) :
  ('c, Obj.t, Obj.t) matrix= init m p (matrix_mul_gen eq m n p add mul mx my)
let matrix_mul_unit (eq : 'c FStar_Algebra_CommMonoid_Equiv.equiv)
  (add : ('c, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm)
  (mul : ('c, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm) (m : Prims.pos) :
  ('c, Obj.t, Obj.t) matrix=
  init m m
    (fun i j ->
       if i = j
       then FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__unit eq mul
       else FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__unit eq add)
