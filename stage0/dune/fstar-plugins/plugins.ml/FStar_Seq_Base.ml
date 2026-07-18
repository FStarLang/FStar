open Fstarcompiler
open Prims
type 'a seq =
  | MkSeq of 'a Prims.list 
let uu___is_MkSeq (projectee : 'a seq) : Prims.bool= true
let __proj__MkSeq__item__l (projectee : 'a seq) : 'a Prims.list=
  match projectee with | MkSeq l -> l
let length (s : 'uuuuu seq) : Prims.nat=
  FStar_List_Tot_Base.length (__proj__MkSeq__item__l s)
let seq_to_list (s : 'uuuuu seq) : 'uuuuu Prims.list=
  match s with | MkSeq l -> l
let seq_of_list (l : 'uuuuu Prims.list) : 'uuuuu seq= MkSeq l
let index (s : 'uuuuu seq) (i : Prims.nat) : 'uuuuu=
  FStar_List_Tot_Base.index (__proj__MkSeq__item__l s) i
let _cons (x : 'a) (s : 'a seq) : 'a seq=
  MkSeq (x :: (__proj__MkSeq__item__l s))
let hd (s : 'a seq) : 'a= FStar_List_Tot_Base.hd (__proj__MkSeq__item__l s)
let tl (s : 'a seq) : 'a seq=
  MkSeq (FStar_List_Tot_Base.tl (__proj__MkSeq__item__l s))
let rec create : 'uuuuu . Prims.nat -> 'uuuuu -> 'uuuuu seq =
  fun len v ->
    if len = Prims.int_zero
    then MkSeq []
    else _cons v (create (len - Prims.int_one) v)
let rec init_aux' :
  'a . Prims.nat -> Prims.nat -> (Prims.nat -> 'a) -> 'a seq =
  fun len k contents ->
    if (k + Prims.int_one) = len
    then MkSeq [contents k]
    else _cons (contents k) (init_aux' len (k + Prims.int_one) contents)
let init_aux : Prims.nat -> Prims.nat -> (Prims.nat -> 'a) -> 'a seq=
  init_aux'
let init (len : Prims.nat) (contents : Prims.nat -> 'uuuuu) : 'uuuuu seq=
  if len = Prims.int_zero
  then MkSeq []
  else init_aux len Prims.int_zero contents
let empty (uu___ : unit) : 'uuuuu seq= MkSeq []
let createEmpty (uu___ : unit) : 'a seq= empty ()
let rec upd' : 'a . 'a seq -> Prims.nat -> 'a -> 'a seq =
  fun s n v ->
    if n = Prims.int_zero
    then _cons v (tl s)
    else _cons (hd s) (upd' (tl s) (n - Prims.int_one) v)
let upd : 'a seq -> Prims.nat -> 'a -> 'a seq= upd'
let append (s1 : 'uuuuu seq) (s2 : 'uuuuu seq) : 'uuuuu seq=
  MkSeq
    (FStar_List_Tot_Base.append (__proj__MkSeq__item__l s1)
       (__proj__MkSeq__item__l s2))
let cons (x : 'a) (s : 'a seq) : 'a seq= append (create Prims.int_one x) s
let op_At_Bar (s1 : 'a seq) (s2 : 'a seq) : 'a seq= append s1 s2
let rec slice' : 'a . 'a seq -> Prims.nat -> Prims.nat -> 'a seq =
  fun s i j ->
    if i > Prims.int_zero
    then slice' (tl s) (i - Prims.int_one) (j - Prims.int_one)
    else
      if j = Prims.int_zero
      then MkSeq []
      else _cons (hd s) (slice' (tl s) i (j - Prims.int_one))
let slice : 'a seq -> Prims.nat -> Prims.nat -> 'a seq= slice'
type ('a, 's1, 's2) equal = unit
let rec eq_i' : 'a . 'a seq -> 'a seq -> Prims.nat -> Prims.bool =
  fun s1 s2 i ->
    if i = (length s1)
    then true
    else
      if (index s1 i) = (index s2 i)
      then eq_i' s1 s2 (i + Prims.int_one)
      else false
let eq_i : 'a seq -> 'a seq -> Prims.nat -> Prims.bool= eq_i'
let eq (s1 : 'uuuuu seq) (s2 : 'uuuuu seq) : Prims.bool=
  if (length s1) = (length s2) then eq_i s1 s2 Prims.int_zero else false
