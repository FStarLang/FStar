open Prims
type ('c, 'm, 'n) matrix_generator =
  unit FStar_IntegerIntervals.under ->
    unit FStar_IntegerIntervals.under -> 'c
type ('c, 'm, 'n) matrix = 'c FStar_Seq_Base.seq
let (get_ij :
  Prims.pos ->
    Prims.pos ->
      unit FStar_IntegerIntervals.under ->
        unit FStar_IntegerIntervals.under ->
          unit FStar_IntegerIntervals.under)
  = fun m -> fun n -> fun i -> fun j -> (i * n) + j
let (get_i :
  Prims.pos ->
    Prims.pos ->
      unit FStar_IntegerIntervals.under -> unit FStar_IntegerIntervals.under)
  = fun m -> fun n -> fun ij -> ij / n
let (get_j :
  Prims.pos ->
    Prims.pos ->
      unit FStar_IntegerIntervals.under -> unit FStar_IntegerIntervals.under)
  = fun m -> fun n -> fun ij -> ij mod n
let (transpose_ji :
  Prims.pos ->
    Prims.pos ->
      unit FStar_IntegerIntervals.under -> unit FStar_IntegerIntervals.under)
  = fun m -> fun n -> fun ij -> ((get_j m n ij) * m) + (get_i m n ij)
let seq_of_matrix :
  'c .
    Prims.pos ->
      Prims.pos -> ('c, unit, unit) matrix -> 'c FStar_Seq_Base.seq
  = fun m -> fun n -> fun mx -> mx
let ijth :
  'c .
    Prims.pos ->
      Prims.pos ->
        ('c, unit, unit) matrix ->
          unit FStar_IntegerIntervals.under ->
            unit FStar_IntegerIntervals.under -> 'c
  =
  fun m ->
    fun n ->
      fun mx -> fun i -> fun j -> FStar_Seq_Base.index mx (get_ij m n i j)
let matrix_of_seq :
  'c .
    Prims.pos ->
      Prims.pos -> 'c FStar_Seq_Base.seq -> ('c, unit, unit) matrix
  = fun m -> fun n -> fun s -> s
type ('c, 'm, 'n, 'gen) matrix_of = ('c, unit, unit) matrix
let foldm :
  'c .
    'c FStar_Algebra_CommMonoid_Equiv.equiv ->
      Prims.pos ->
        Prims.pos ->
          ('c, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
            ('c, unit, unit) matrix -> 'c
  =
  fun eq ->
    fun m ->
      fun n -> fun cm -> fun mx -> FStar_Seq_Permutation.foldm_snoc eq cm mx
let init :
  'c .
    Prims.pos ->
      Prims.pos ->
        ('c, unit, unit) matrix_generator -> ('c, unit, unit, unit) matrix_of
  =
  fun m ->
    fun n ->
      fun generator ->
        let mn = m * n in
        let generator_ij ij = generator (get_i m n ij) (get_j m n ij) in
        let flat_indices = FStar_IntegerIntervals.indices_seq mn in
        let result = FStar_Seq_Properties.map_seq generator_ij flat_indices in
        result
let matrix_seq :
  'c .
    Prims.pos ->
      Prims.pos -> ('c, unit, unit) matrix_generator -> 'c FStar_Seq_Base.seq
  = fun m -> fun n -> fun gen -> init m n gen
let transposed_matrix_gen :
  'c .
    Prims.pos ->
      Prims.pos ->
        ('c, unit, unit) matrix_generator ->
          ('c, unit, unit) matrix_generator
  = fun m -> fun n -> fun generator -> fun j -> fun i -> generator i j
type ('c, 'm, 'n, 'eq, 'ma, 'mb) matrix_eq_fun =
  ('c, unit, unit, unit) FStar_Seq_Equiv.eq_of_seq
let matrix_equiv :
  'c .
    'c FStar_Algebra_CommMonoid_Equiv.equiv ->
      Prims.pos ->
        Prims.pos ->
          ('c, unit, unit) matrix FStar_Algebra_CommMonoid_Equiv.equiv
  =
  fun eq ->
    fun m -> fun n -> FStar_Algebra_CommMonoid_Equiv.EQ ((), (), (), ())
let matrix_add_generator :
  'c .
    'c FStar_Algebra_CommMonoid_Equiv.equiv ->
      Prims.pos ->
        Prims.pos ->
          ('c, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
            ('c, unit, unit) matrix ->
              ('c, unit, unit) matrix -> ('c, unit, unit) matrix_generator
  =
  fun eq ->
    fun m ->
      fun n ->
        fun add ->
          fun ma ->
            fun mb ->
              fun i ->
                fun j ->
                  FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq
                    add (ijth m n ma i j) (ijth m n mb i j)
let matrix_add :
  'c .
    'c FStar_Algebra_CommMonoid_Equiv.equiv ->
      Prims.pos ->
        Prims.pos ->
          ('c, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
            ('c, unit, unit) matrix ->
              ('c, unit, unit) matrix -> ('c, unit, unit, unit) matrix_of
  =
  fun eq ->
    fun m ->
      fun n ->
        fun add ->
          fun ma ->
            fun mb -> init m n (matrix_add_generator eq m n add ma mb)
let matrix_add_zero :
  'c .
    'c FStar_Algebra_CommMonoid_Equiv.equiv ->
      ('c, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
        Prims.pos -> Prims.pos -> ('c, unit, unit) matrix
  =
  fun eq ->
    fun add ->
      fun m ->
        fun n ->
          matrix_of_seq m n
            (FStar_Seq_Base.create (m * n)
               (FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__unit eq add))
let matrix_add_comm_monoid :
  'c .
    'c FStar_Algebra_CommMonoid_Equiv.equiv ->
      ('c, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
        Prims.pos ->
          Prims.pos ->
            (('c, unit, unit) matrix, unit) FStar_Algebra_CommMonoid_Equiv.cm
  =
  fun eq ->
    fun add ->
      fun m ->
        fun n ->
          FStar_Algebra_CommMonoid_Equiv.CM
            ((matrix_add_zero eq add m n), (matrix_add eq m n add), (), (),
              (), ())
let col :
  'c .
    Prims.pos ->
      Prims.pos ->
        ('c, unit, unit) matrix ->
          unit FStar_IntegerIntervals.under -> 'c FStar_Seq_Base.seq
  =
  fun m ->
    fun n ->
      fun mx -> fun j -> FStar_Seq_Base.init m (fun i -> ijth m n mx i j)
let row :
  'c .
    Prims.pos ->
      Prims.pos ->
        ('c, unit, unit) matrix ->
          unit FStar_IntegerIntervals.under -> 'c FStar_Seq_Base.seq
  =
  fun m ->
    fun n ->
      fun mx -> fun i -> FStar_Seq_Base.init n (fun j -> ijth m n mx i j)
let seq_op_const :
  'c .
    'c FStar_Algebra_CommMonoid_Equiv.equiv ->
      ('c, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
        'c FStar_Seq_Base.seq -> 'c -> 'c FStar_Seq_Base.seq
  =
  fun eq ->
    fun cm ->
      fun s ->
        fun const ->
          FStar_Seq_Base.init (FStar_Seq_Base.length s)
            (fun i ->
               FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq cm
                 (FStar_Seq_Base.index s i) const)
let const_op_seq :
  'c .
    'c FStar_Algebra_CommMonoid_Equiv.equiv ->
      ('c, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
        'c -> 'c FStar_Seq_Base.seq -> 'c FStar_Seq_Base.seq
  =
  fun eq ->
    fun cm ->
      fun const ->
        fun s ->
          FStar_Seq_Base.init (FStar_Seq_Base.length s)
            (fun i ->
               FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq cm
                 const (FStar_Seq_Base.index s i))
let seq_of_products :
  'c .
    'c FStar_Algebra_CommMonoid_Equiv.equiv ->
      ('c, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
        'c FStar_Seq_Base.seq ->
          'c FStar_Seq_Base.seq -> 'c FStar_Seq_Base.seq
  =
  fun eq ->
    fun mul ->
      fun s ->
        fun t ->
          FStar_Seq_Base.init (FStar_Seq_Base.length s)
            (fun i ->
               FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq mul
                 (FStar_Seq_Base.index s i) (FStar_Seq_Base.index t i))
let dot :
  'c .
    'c FStar_Algebra_CommMonoid_Equiv.equiv ->
      ('c, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
        ('c, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
          'c FStar_Seq_Base.seq -> 'c FStar_Seq_Base.seq -> 'c
  =
  fun eq ->
    fun add ->
      fun mul ->
        fun s ->
          fun t ->
            FStar_Seq_Permutation.foldm_snoc eq add
              (seq_of_products eq mul s t)
let matrix_mul_gen :
  'c .
    'c FStar_Algebra_CommMonoid_Equiv.equiv ->
      Prims.pos ->
        Prims.pos ->
          Prims.pos ->
            ('c, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
              ('c, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
                ('c, unit, unit) matrix ->
                  ('c, unit, unit) matrix ->
                    unit FStar_IntegerIntervals.under ->
                      unit FStar_IntegerIntervals.under -> 'c
  =
  fun eq ->
    fun m ->
      fun n ->
        fun p ->
          fun add ->
            fun mul ->
              fun mx ->
                fun my ->
                  fun i ->
                    fun k -> dot eq add mul (row m n mx i) (col n p my k)
let matrix_mul :
  'c .
    'c FStar_Algebra_CommMonoid_Equiv.equiv ->
      Prims.pos ->
        Prims.pos ->
          Prims.pos ->
            ('c, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
              ('c, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
                ('c, unit, unit) matrix ->
                  ('c, unit, unit) matrix -> ('c, unit, unit) matrix
  =
  fun eq ->
    fun m ->
      fun n ->
        fun p ->
          fun add ->
            fun mul ->
              fun mx ->
                fun my -> init m p (matrix_mul_gen eq m n p add mul mx my)
type ('c, 'eq, 'mul, 'add) is_left_distributive = unit
type ('c, 'eq, 'mul, 'add) is_right_distributive = unit
type ('c, 'eq, 'mul, 'add) is_fully_distributive = unit
type ('c, 'eq, 'z, 'op) is_absorber = unit
let matrix_mul_unit :
  'c .
    'c FStar_Algebra_CommMonoid_Equiv.equiv ->
      ('c, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
        ('c, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
          Prims.pos -> ('c, unit, unit) matrix
  =
  fun eq ->
    fun add ->
      fun mul ->
        fun m ->
          init m m
            (fun i ->
               fun j ->
                 if i = j
                 then
                   FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__unit eq
                     mul
                 else
                   FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__unit eq
                     add)