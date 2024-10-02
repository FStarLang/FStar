open Prims
type 'n fin = Prims.int
type 'p under = Prims.nat
type ('n, 'a) vect = 'a Prims.list
type ('n, 'a) seqn = 'a FStar_Seq_Base.seq
type ('a, 's) in_ = Prims.nat
let rec find :
  'a .
    'a FStar_Seq_Base.seq ->
      ('a -> Prims.bool) ->
        Prims.nat -> Prims.nat FStar_Pervasives_Native.option
  =
  fun s ->
    fun p ->
      fun i ->
        if p (FStar_Seq_Base.index s i)
        then FStar_Pervasives_Native.Some i
        else
          if (i + Prims.int_one) < (FStar_Seq_Base.length s)
          then find s p (i + Prims.int_one)
          else FStar_Pervasives_Native.None
let rec (pigeonhole :
  Prims.pos -> Prims.nat FStar_Seq_Base.seq -> (Prims.nat * Prims.nat)) =
  fun n ->
    fun s ->
      if n = Prims.int_one
      then (Prims.int_zero, Prims.int_one)
      else
        (let k0 = FStar_Seq_Base.index s Prims.int_zero in
         match find s (fun k -> k = k0) Prims.int_one with
         | FStar_Pervasives_Native.Some i -> (Prims.int_zero, i)
         | FStar_Pervasives_Native.None ->
             let uu___1 =
               pigeonhole (n - Prims.int_one)
                 (FStar_Seq_Base.init n
                    (fun i ->
                       let k = FStar_Seq_Base.index s (i + Prims.int_one) in
                       if k < k0 then k else k - Prims.int_one)) in
             (match uu___1 with
              | (i1, i2) -> ((i1 + Prims.int_one), (i2 + Prims.int_one))))
type 'a binary_relation = 'a -> 'a -> Prims.bool
type ('a, 'r) is_reflexive = unit
type ('a, 'r) is_symmetric = unit
type ('a, 'r) is_transitive = unit
type 'a equivalence_relation = 'a -> 'a -> Prims.bool
type ('a, 'eq, 's, 'x) contains_eq = unit
type ('a, 'eq, 's) items_of = 'a
let rec find_eq :
  'a . 'a equivalence_relation -> 'a FStar_Seq_Base.seq -> 'a -> Prims.nat =
  fun eq ->
    fun s ->
      fun x ->
        if (FStar_Seq_Base.length s) = Prims.int_one
        then Prims.int_zero
        else
          if eq x (FStar_Seq_Base.index s Prims.int_zero)
          then Prims.int_zero
          else
            (let ieq = find_eq eq (FStar_Seq_Properties.tail s) x in
             Prims.int_one + ieq)
let rec pigeonhole_eq :
  'a .
    'a equivalence_relation ->
      'a FStar_Seq_Base.seq ->
        ('a, unit, unit) items_of FStar_Seq_Base.seq ->
          (Prims.nat * Prims.nat)
  =
  fun eq ->
    fun holes ->
      fun pigeons ->
        if (FStar_Seq_Base.length holes) = Prims.int_one
        then (Prims.int_zero, Prims.int_one)
        else
          (let first_pigeon = FStar_Seq_Base.index pigeons Prims.int_zero in
           match find pigeons (fun k -> eq k first_pigeon) Prims.int_one with
           | FStar_Pervasives_Native.Some i -> (Prims.int_zero, i)
           | FStar_Pervasives_Native.None ->
               let index_of_first_pigeon = find_eq eq holes first_pigeon in
               let holes_except_first_pigeon =
                 FStar_Seq_Base.append
                   (FStar_Seq_Base.slice holes Prims.int_zero
                      index_of_first_pigeon)
                   (FStar_Seq_Base.slice holes
                      (index_of_first_pigeon + Prims.int_one)
                      (FStar_Seq_Base.length holes)) in
               let uu___1 =
                 pigeonhole_eq eq holes_except_first_pigeon
                   (FStar_Seq_Base.init
                      ((FStar_Seq_Base.length pigeons) - Prims.int_one)
                      (fun i ->
                         FStar_Seq_Base.index pigeons (i + Prims.int_one))) in
               (match uu___1 with
                | (i1, i2) -> ((i1 + Prims.int_one), (i2 + Prims.int_one))))