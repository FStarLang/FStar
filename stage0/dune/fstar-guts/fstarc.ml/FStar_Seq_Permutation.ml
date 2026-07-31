open Prims
type ('a, 's) index_fun =
  Obj.t FStar_IntegerIntervals.under -> Obj.t FStar_IntegerIntervals.under
type ('a, 's0, 's1) seqperm = ('a, 's0) index_fun
let rec find :
  'a .
    'a ->
      'a FStar_Seq_Base.seq ->
        ('a FStar_Seq_Base.seq * 'a FStar_Seq_Base.seq)
  =
  fun x s ->
    if (FStar_Seq_Properties.head s) = x
    then ((FStar_Seq_Base.empty ()), (FStar_Seq_Properties.tail s))
    else
      (let uu___ = find x (FStar_Seq_Properties.tail s) in
       match uu___ with
       | (pfx, sfx) ->
           ((FStar_Seq_Base.cons (FStar_Seq_Properties.head s) pfx), sfx))
let adapt_index_fun (s : 'a FStar_Seq_Base.seq) (f : ('a, Obj.t) index_fun)
  (n : Prims.nat) : ('a, Obj.t) index_fun=
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
      'a FStar_Seq_Base.seq -> ('a, Obj.t, Obj.t) seqperm
  =
  fun s0 s1 ->
    if (FStar_Seq_Base.length s0) = Prims.int_zero
    then let f i = i in f
    else
      (let uu___ = find (FStar_Seq_Properties.head s0) s1 in
       match uu___ with
       | (pfx, sfx) ->
           let s1' = FStar_Seq_Base.append pfx sfx in
           let f' =
             permutation_from_equal_counts (FStar_Seq_Properties.tail s0) s1' in
           let n = FStar_Seq_Base.length pfx in
           let f = adapt_index_fun s0 f' n in f)
let foldm_snoc (eq : 'a FStar_Algebra_CommMonoid_Equiv.equiv)
  (m : ('a, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm)
  (s : 'a FStar_Seq_Base.seq) : 'a=
  FStar_Seq_Properties.foldr_snoc
    (FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq m) s
    (FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__unit eq m)
let remove_i (s : 'a FStar_Seq_Base.seq) (i : Prims.nat) :
  ('a * 'a FStar_Seq_Base.seq)=
  let uu___ = FStar_Seq_Properties.split s i in
  match uu___ with
  | (s0, s1) ->
      ((FStar_Seq_Properties.head s1),
        (FStar_Seq_Base.append s0 (FStar_Seq_Properties.tail s1)))
let shift_perm' (s0 : 'a FStar_Seq_Base.seq) (s1 : 'a FStar_Seq_Base.seq)
  (uu___ : unit) (p : ('a, Obj.t, Obj.t) seqperm) :
  ('a, Obj.t, Obj.t) seqperm=
  let uu___1 = FStar_Seq_Properties.un_snoc s0 in
  match uu___1 with
  | (s0', last) ->
      let n = FStar_Seq_Base.length s0' in
      let p' i = if (p i) < (p n) then p i else (p i) - Prims.int_one in
      let uu___2 = remove_i s1 (p n) in
      (match uu___2 with | (uu___3, s1') -> p')
let shift_perm (s0 : 'a FStar_Seq_Base.seq) (s1 : 'a FStar_Seq_Base.seq)
  (uu___ : unit) (p : ('a, Obj.t, Obj.t) seqperm) :
  ('a, Obj.t, Obj.t) seqperm= shift_perm' s0 s1 () p
let init_func_from_expr (n0 : Prims.int)
  (nk : Obj.t FStar_IntegerIntervals.not_less_than)
  (expr : (Obj.t, Obj.t) FStar_IntegerIntervals.ifrom_ito -> 'c)
  (a : (Obj.t, Obj.t) FStar_IntegerIntervals.ifrom_ito)
  (b : (Obj.t, Obj.t) FStar_IntegerIntervals.ifrom_ito)
  (i : Obj.t FStar_IntegerIntervals.under) : 'c= expr (n0 + i)
let func_sum (eq : 'c FStar_Algebra_CommMonoid_Equiv.equiv)
  (cm : ('c, Obj.t) FStar_Algebra_CommMonoid_Equiv.cm) (f : 'a -> 'c)
  (g : 'a -> 'c) (x : 'a) : 'c=
  FStar_Algebra_CommMonoid_Equiv.__proj__CM__item__mult eq cm (f x) (g x)
