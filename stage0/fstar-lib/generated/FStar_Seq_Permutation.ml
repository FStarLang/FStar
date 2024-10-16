open Prims
type ('a, 's) index_fun =
  unit FStar_IntegerIntervals.under -> unit FStar_IntegerIntervals.under
type ('a, 's0, 's1, 'f) is_permutation = unit
type ('a, 's0, 's1) seqperm = ('a, unit) index_fun
let rec find :
  'a .
    'a ->
      'a FStar_Seq_Base.seq ->
        ('a FStar_Seq_Base.seq * 'a FStar_Seq_Base.seq)
  =
  fun x ->
    fun s ->
      if (FStar_Seq_Properties.head s) = x
      then ((FStar_Seq_Base.empty ()), (FStar_Seq_Properties.tail s))
      else
        (let uu___1 = find x (FStar_Seq_Properties.tail s) in
         match uu___1 with
         | (pfx, sfx) ->
             ((FStar_Seq_Base.cons (FStar_Seq_Properties.head s) pfx), sfx))
let adapt_index_fun :
  'a .
    'a FStar_Seq_Base.seq ->
      ('a, unit) index_fun -> Prims.nat -> ('a, unit) index_fun
  =
  fun s ->
    fun f ->
      fun n ->
        fun i ->
          if i = Prims.int_zero
          then n
          else
            if (f (i - Prims.int_one)) < n
            then f (i - Prims.int_one)
            else (f (i - Prims.int_one)) + Prims.int_one
let rec permutation_from_equal_counts :
  'a .
    'a FStar_Seq_Base.seq ->
      'a FStar_Seq_Base.seq -> ('a, unit, unit) seqperm
  =
  fun s0 ->
    fun s1 ->
      if (FStar_Seq_Base.length s0) = Prims.int_zero
      then let f i = i in f
      else
        (let uu___1 = find (FStar_Seq_Properties.head s0) s1 in
         match uu___1 with
         | (pfx, sfx) ->
             let s1' = FStar_Seq_Base.append pfx sfx in
             let f' =
               permutation_from_equal_counts (FStar_Seq_Properties.tail s0)
                 s1' in
             let n = FStar_Seq_Base.length pfx in
             let f = adapt_index_fun s0 f' n in f)
let foldm_snoc :
  'a .
    'a FStar_Algebra_CommMonoid_Equiv.equiv ->
      ('a, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
        'a FStar_Seq_Base.seq -> 'a
  =
  fun eq ->
    fun m ->
      fun s ->
        FStar_Seq_Properties.foldr_snoc
          (FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq m) s
          (FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__unit eq m)
let remove_i :
  'a . 'a FStar_Seq_Base.seq -> Prims.nat -> ('a * 'a FStar_Seq_Base.seq) =
  fun s ->
    fun i ->
      let uu___ = FStar_Seq_Properties.split s i in
      match uu___ with
      | (s0, s1) ->
          ((FStar_Seq_Properties.head s1),
            (FStar_Seq_Base.append s0 (FStar_Seq_Properties.tail s1)))
let shift_perm' :
  'a .
    'a FStar_Seq_Base.seq ->
      'a FStar_Seq_Base.seq ->
        unit -> ('a, unit, unit) seqperm -> ('a, unit, unit) seqperm
  =
  fun s0 ->
    fun s1 ->
      fun uu___ ->
        fun p ->
          let uu___1 = FStar_Seq_Properties.un_snoc s0 in
          match uu___1 with
          | (s0', last) ->
              let n = FStar_Seq_Base.length s0' in
              let p' i = if (p i) < (p n) then p i else (p i) - Prims.int_one in
              let uu___2 = remove_i s1 (p n) in
              (match uu___2 with | (uu___3, s1') -> p')
let shift_perm :
  'a .
    'a FStar_Seq_Base.seq ->
      'a FStar_Seq_Base.seq ->
        unit -> ('a, unit, unit) seqperm -> ('a, unit, unit) seqperm
  = fun s0 -> fun s1 -> fun uu___ -> fun p -> shift_perm' s0 s1 () p
let init_func_from_expr :
  'c .
    Prims.int ->
      unit FStar_IntegerIntervals.not_less_than ->
        ((unit, unit) FStar_IntegerIntervals.ifrom_ito -> 'c) ->
          (unit, unit) FStar_IntegerIntervals.ifrom_ito ->
            (unit, unit) FStar_IntegerIntervals.ifrom_ito ->
              unit FStar_IntegerIntervals.under -> 'c
  = fun n0 -> fun nk -> fun expr -> fun a -> fun b -> fun i -> expr (n0 + i)
let func_sum :
  'a 'c .
    'c FStar_Algebra_CommMonoid_Equiv.equiv ->
      ('c, unit) FStar_Algebra_CommMonoid_Equiv.cm ->
        ('a -> 'c) -> ('a -> 'c) -> 'a -> 'c
  =
  fun eq ->
    fun cm ->
      fun f ->
        fun g ->
          fun x ->
            FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq cm (
              f x) (g x)