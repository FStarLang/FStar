open Fstarcompiler
open Prims
type ('a, 'l) lseq = 'a FStar_Seq_Base.seq
type ('a, 's, 'j) indexable = unit
let head (s : 'a FStar_Seq_Base.seq) : 'a=
  FStar_Seq_Base.index s Prims.int_zero
let tail (s : 'a FStar_Seq_Base.seq) : 'a FStar_Seq_Base.seq=
  FStar_Seq_Base.slice s Prims.int_one (FStar_Seq_Base.length s)
let last (s : 'a FStar_Seq_Base.seq) : 'a=
  FStar_Seq_Base.index s ((FStar_Seq_Base.length s) - Prims.int_one)
let split (s : 'a FStar_Seq_Base.seq) (i : Prims.nat) :
  ('a FStar_Seq_Base.seq * 'a FStar_Seq_Base.seq)=
  ((FStar_Seq_Base.slice s Prims.int_zero i),
    (FStar_Seq_Base.slice s i (FStar_Seq_Base.length s)))
let split_eq (s : 'a FStar_Seq_Base.seq) (i : Prims.nat) :
  ('a FStar_Seq_Base.seq * 'a FStar_Seq_Base.seq)= let x = split s i in x
let rec count : 'a . 'a -> 'a FStar_Seq_Base.seq -> Prims.nat =
  fun x s ->
    if (FStar_Seq_Base.length s) = Prims.int_zero
    then Prims.int_zero
    else
      if (head s) = x
      then Prims.int_one + (count x (tail s))
      else count x (tail s)
let mem (x : 'a) (l : 'a FStar_Seq_Base.seq) : Prims.bool=
  (count x l) > Prims.int_zero
let rec index_mem : 'a . 'a -> 'a FStar_Seq_Base.seq -> Prims.nat =
  fun x s ->
    if (head s) = x
    then Prims.int_zero
    else Prims.int_one + (index_mem x (tail s))
let swap (s : 'a FStar_Seq_Base.seq) (i : Prims.nat) (j : Prims.nat) :
  'a FStar_Seq_Base.seq=
  FStar_Seq_Base.upd (FStar_Seq_Base.upd s j (FStar_Seq_Base.index s i)) i
    (FStar_Seq_Base.index s j)
let rec sorted :
  'a . ('a -> 'a -> Prims.bool) -> 'a FStar_Seq_Base.seq -> Prims.bool =
  fun f s ->
    if (FStar_Seq_Base.length s) <= Prims.int_one
    then true
    else
      (let hd = head s in
       (f hd (FStar_Seq_Base.index s Prims.int_one)) && (sorted f (tail s)))
type ('a, 'f) total_order = unit
type 'a tot_ord = 'a -> 'a -> Prims.bool
let split_5 (s : 'a FStar_Seq_Base.seq) (i : Prims.nat) (j : Prims.nat) :
  'a FStar_Seq_Base.seq FStar_Seq_Base.seq=
  let frag_lo = FStar_Seq_Base.slice s Prims.int_zero i in
  let frag_i = FStar_Seq_Base.slice s i (i + Prims.int_one) in
  let frag_mid = FStar_Seq_Base.slice s (i + Prims.int_one) j in
  let frag_j = FStar_Seq_Base.slice s j (j + Prims.int_one) in
  let frag_hi =
    FStar_Seq_Base.slice s (j + Prims.int_one) (FStar_Seq_Base.length s) in
  FStar_Seq_Base.upd
    (FStar_Seq_Base.upd
       (FStar_Seq_Base.upd
          (FStar_Seq_Base.upd
             (FStar_Seq_Base.create (Prims.of_int (5)) frag_lo) Prims.int_one
             frag_i) (Prims.of_int (2)) frag_mid) (Prims.of_int (3)) frag_j)
    (Prims.of_int (4)) frag_hi
type ('a, 's1, 's2) permutation = unit
let splice (s1 : 'a FStar_Seq_Base.seq) (i : Prims.nat)
  (s2 : 'a FStar_Seq_Base.seq) (j : Prims.nat) : 'a FStar_Seq_Base.seq=
  FStar_Seq_Base.append (FStar_Seq_Base.slice s1 Prims.int_zero i)
    (FStar_Seq_Base.append (FStar_Seq_Base.slice s2 i j)
       (FStar_Seq_Base.slice s1 j (FStar_Seq_Base.length s1)))
let replace_subseq (s : 'a FStar_Seq_Base.seq) (i : Prims.nat)
  (j : Prims.nat) (sub : 'a FStar_Seq_Base.seq) : 'a FStar_Seq_Base.seq=
  FStar_Seq_Base.append (FStar_Seq_Base.slice s Prims.int_zero i)
    (FStar_Seq_Base.append sub
       (FStar_Seq_Base.slice s j (FStar_Seq_Base.length s)))
let snoc (s : 'a FStar_Seq_Base.seq) (x : 'a) : 'a FStar_Seq_Base.seq=
  FStar_Seq_Base.append s (FStar_Seq_Base.create Prims.int_one x)
let rec find_l :
  'a .
    ('a -> Prims.bool) ->
      'a FStar_Seq_Base.seq -> 'a FStar_Pervasives_Native.option
  =
  fun f l ->
    if (FStar_Seq_Base.length l) = Prims.int_zero
    then FStar_Pervasives_Native.None
    else
      if f (head l)
      then FStar_Pervasives_Native.Some (head l)
      else find_l f (tail l)
let un_snoc (s : 'a FStar_Seq_Base.seq) : ('a FStar_Seq_Base.seq * 'a)=
  let uu___ = split s ((FStar_Seq_Base.length s) - Prims.int_one) in
  match uu___ with
  | (s', a1) -> (s', (FStar_Seq_Base.index a1 Prims.int_zero))
let rec find_r :
  'a .
    ('a -> Prims.bool) ->
      'a FStar_Seq_Base.seq -> 'a FStar_Pervasives_Native.option
  =
  fun f l ->
    if (FStar_Seq_Base.length l) = Prims.int_zero
    then FStar_Pervasives_Native.None
    else
      (let uu___1 = un_snoc l in
       match uu___1 with
       | (prefix, last1) ->
           if f last1
           then FStar_Pervasives_Native.Some last1
           else find_r f prefix)
type 'i found = unit
let rec seq_find_aux :
  'a .
    ('a -> Prims.bool) ->
      'a FStar_Seq_Base.seq -> Prims.nat -> 'a FStar_Pervasives_Native.option
  =
  fun f l ctr ->
    match ctr with
    | uu___ when uu___ = Prims.int_zero -> FStar_Pervasives_Native.None
    | uu___ ->
        let i = ctr - Prims.int_one in
        if f (FStar_Seq_Base.index l i)
        then FStar_Pervasives_Native.Some (FStar_Seq_Base.index l i)
        else seq_find_aux f l i
let seq_find (f : 'a -> Prims.bool) (l : 'a FStar_Seq_Base.seq) :
  'a FStar_Pervasives_Native.option=
  seq_find_aux f l (FStar_Seq_Base.length l)
let for_all (f : 'a -> Prims.bool) (l : 'a FStar_Seq_Base.seq) : Prims.bool=
  FStar_Pervasives_Native.uu___is_None
    (seq_find (fun i -> Prims.op_Negation (f i)) l)
type ('a, 'l, 's) createL_post = unit
let createL (l : 'a Prims.list) : 'a FStar_Seq_Base.seq=
  let s = FStar_Seq_Base.seq_of_list l in s
type ('a, 's, 'x) contains = unit
type ('a, 'susuff, 's) suffix_of = unit
let of_list (l : 'a Prims.list) : 'a FStar_Seq_Base.seq=
  FStar_Seq_Base.seq_of_list l
type ('a, 'i, 's, 'l) explode_and = Obj.t
type ('uuuuu, 's, 'l) pointwise_and = Obj.t
let sortWith (f : 'a -> 'a -> Prims.int) (s : 'a FStar_Seq_Base.seq) :
  'a FStar_Seq_Base.seq=
  FStar_Seq_Base.seq_of_list
    (FStar_List_Tot_Base.sortWith f (FStar_Seq_Base.seq_to_list s))
let sort_lseq (n : Prims.nat) (f : 'a tot_ord) (s : ('a, Obj.t) lseq) :
  ('a, Obj.t) lseq=
  let s' = sortWith (FStar_List_Tot_Base.compare_of_bool f) s in s'
let rec foldr : 'a 'b . ('b -> 'a -> 'a) -> 'b FStar_Seq_Base.seq -> 'a -> 'a
  =
  fun f s init ->
    if (FStar_Seq_Base.length s) = Prims.int_zero
    then init
    else f (head s) (foldr f (tail s) init)
let rec foldr_snoc :
  'a 'b . ('b -> 'a -> 'a) -> 'b FStar_Seq_Base.seq -> 'a -> 'a =
  fun f s init ->
    if (FStar_Seq_Base.length s) = Prims.int_zero
    then init
    else
      (let uu___1 = un_snoc s in
       match uu___1 with | (s1, last1) -> f last1 (foldr_snoc f s1 init))
let rec map_seq :
  'a 'b . ('a -> 'b) -> 'a FStar_Seq_Base.seq -> 'b FStar_Seq_Base.seq =
  fun f s ->
    if (FStar_Seq_Base.length s) = Prims.int_zero
    then FStar_Seq_Base.empty ()
    else
      (let uu___1 = ((head s), (tail s)) in
       match uu___1 with
       | (hd, tl) -> FStar_Seq_Base.cons (f hd) (map_seq f tl))
