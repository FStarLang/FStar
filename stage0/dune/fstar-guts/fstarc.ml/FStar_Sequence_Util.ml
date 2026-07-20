open Prims
let slice (s : 'ty FStar_Sequence_Base.seq) (i : Prims.nat) (j : Prims.nat) :
  'ty FStar_Sequence_Base.seq=
  FStar_Sequence_Base.drop (FStar_Sequence_Base.take s j) i
let cons (x : 'a) (s : 'a FStar_Sequence_Base.seq) :
  'a FStar_Sequence_Base.seq=
  FStar_Sequence_Base.append (FStar_Sequence_Base.singleton x) s
let head (s : 'a FStar_Sequence_Base.seq) : 'a=
  FStar_Sequence_Base.op_Dollar_At () s Prims.int_zero
let tail (s : 'a FStar_Sequence_Base.seq) : 'a FStar_Sequence_Base.seq=
  FStar_Sequence_Base.drop s Prims.int_one
let un_build (s : 'a FStar_Sequence_Base.seq) :
  ('a FStar_Sequence_Base.seq * 'a)=
  ((FStar_Sequence_Base.take s
      ((FStar_Sequence_Base.length s) - Prims.int_one)),
    (FStar_Sequence_Base.op_Dollar_At () s
       ((FStar_Sequence_Base.length s) - Prims.int_one)))
let split (s : 'a FStar_Sequence_Base.seq) (i : Prims.nat) :
  ('a FStar_Sequence_Base.seq * 'a FStar_Sequence_Base.seq)=
  ((FStar_Sequence_Base.take s i), (FStar_Sequence_Base.drop s i))
let rec count_matches :
  'a . ('a -> Prims.bool) -> 'a FStar_Sequence_Base.seq -> Prims.nat =
  fun f s ->
    if (FStar_Sequence_Base.length s) = Prims.int_zero
    then Prims.int_zero
    else
      if f (head s)
      then Prims.int_one + (count_matches f (tail s))
      else count_matches f (tail s)
let count (x : 'a) (s : 'a FStar_Sequence_Base.seq) : Prims.nat=
  count_matches (fun y -> x = y) s
let rec fold_back :
  'a 'b . ('b -> 'a -> 'a) -> 'b FStar_Sequence_Base.seq -> 'a -> 'a =
  fun f s init ->
    if (FStar_Sequence_Base.length s) = Prims.int_zero
    then init
    else
      (let last =
         FStar_Sequence_Base.op_Dollar_At () s
           ((FStar_Sequence_Base.length s) - Prims.int_one) in
       let s1 =
         FStar_Sequence_Base.take s
           ((FStar_Sequence_Base.length s) - Prims.int_one) in
       f last (fold_back f s1 init))
