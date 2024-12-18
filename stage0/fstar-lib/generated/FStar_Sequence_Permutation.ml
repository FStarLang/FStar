open Prims
type 'n nat_at_most = Prims.nat
type ('a, 's) index_fun = unit nat_at_most -> unit nat_at_most
type ('a, 's0, 's1, 'f) is_permutation = unit
type ('a, 's0, 's1) seqperm = ('a, unit) index_fun
let rec find :
  'a .
    'a ->
      'a FStar_Sequence_Base.seq ->
        ('a FStar_Sequence_Base.seq * 'a FStar_Sequence_Base.seq)
  =
  fun x ->
    fun s ->
      if (FStar_Sequence_Util.head s) = x
      then ((FStar_Sequence_Base.empty ()), (FStar_Sequence_Util.tail s))
      else
        (let uu___1 = find x (FStar_Sequence_Util.tail s) in
         match uu___1 with
         | (pfx, sfx) ->
             ((FStar_Sequence_Util.cons (FStar_Sequence_Util.head s) pfx),
               sfx))
let rec permutation_from_equal_counts :
  'a .
    'a FStar_Sequence_Base.seq ->
      'a FStar_Sequence_Base.seq -> ('a, unit, unit) seqperm
  =
  fun s0 ->
    fun s1 ->
      if (FStar_Sequence_Base.length s0) = Prims.int_zero
      then let f i = i in f
      else
        (let uu___1 = find (FStar_Sequence_Util.head s0) s1 in
         match uu___1 with
         | (pfx, sfx) ->
             let s1' = FStar_Sequence_Base.append pfx sfx in
             let f' =
               permutation_from_equal_counts (FStar_Sequence_Util.tail s0)
                 s1' in
             let n = FStar_Sequence_Base.length pfx in
             let f i =
               if i = Prims.int_zero
               then n
               else
                 if (f' (i - Prims.int_one)) < n
                 then f' (i - Prims.int_one)
                 else (f' (i - Prims.int_one)) + Prims.int_one in
             f)
let foldm_back :
  'a . 'a FStar_Algebra_CommMonoid.cm -> 'a FStar_Sequence_Base.seq -> 'a =
  fun m ->
    fun s ->
      FStar_Sequence_Util.fold_back
        (FStar_Algebra_CommMonoid.__proj__CM__item__mult m) s
        (FStar_Algebra_CommMonoid.__proj__CM__item__unit m)
let remove_i :
  'a .
    'a FStar_Sequence_Base.seq ->
      Prims.nat -> ('a * 'a FStar_Sequence_Base.seq)
  =
  fun s ->
    fun i ->
      let uu___ = FStar_Sequence_Util.split s i in
      match uu___ with
      | (s0, s1) ->
          ((FStar_Sequence_Util.head s1),
            (FStar_Sequence_Base.append s0 (FStar_Sequence_Util.tail s1)))
let shift_perm' :
  'a .
    'a FStar_Sequence_Base.seq ->
      'a FStar_Sequence_Base.seq ->
        unit -> ('a, unit, unit) seqperm -> ('a, unit, unit) seqperm
  =
  fun s0 ->
    fun s1 ->
      fun uu___ ->
        fun p ->
          let uu___1 = FStar_Sequence_Util.un_build s0 in
          match uu___1 with
          | (s0', last) ->
              let n = FStar_Sequence_Base.length s0' in
              let p' i = if (p i) < (p n) then p i else (p i) - Prims.int_one in
              let uu___2 = remove_i s1 (p n) in
              (match uu___2 with | (uu___3, s1') -> p')
let shift_perm :
  'a .
    'a FStar_Sequence_Base.seq ->
      'a FStar_Sequence_Base.seq ->
        unit -> ('a, unit, unit) seqperm -> ('a, unit, unit) seqperm
  = fun s0 -> fun s1 -> fun uu___ -> fun p -> shift_perm' s0 s1 () p