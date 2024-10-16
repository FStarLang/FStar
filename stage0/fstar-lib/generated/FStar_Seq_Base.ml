open Prims
type 'a seq =
  | MkSeq of 'a Prims.list 
let uu___is_MkSeq : 'a . 'a seq -> Prims.bool = fun projectee -> true
let __proj__MkSeq__item__l : 'a . 'a seq -> 'a Prims.list =
  fun projectee -> match projectee with | MkSeq l -> l
let length : 'uuuuu . 'uuuuu seq -> Prims.nat =
  fun s -> FStar_List_Tot_Base.length (__proj__MkSeq__item__l s)
let seq_to_list : 'uuuuu . 'uuuuu seq -> 'uuuuu Prims.list =
  fun s -> match s with | MkSeq l -> l
let seq_of_list : 'uuuuu . 'uuuuu Prims.list -> 'uuuuu seq = fun l -> MkSeq l
let index : 'uuuuu . 'uuuuu seq -> Prims.nat -> 'uuuuu =
  fun s -> fun i -> FStar_List_Tot_Base.index (__proj__MkSeq__item__l s) i
let _cons : 'a . 'a -> 'a seq -> 'a seq =
  fun x -> fun s -> MkSeq (x :: (__proj__MkSeq__item__l s))
let hd : 'a . 'a seq -> 'a =
  fun s -> FStar_List_Tot_Base.hd (__proj__MkSeq__item__l s)
let tl : 'a . 'a seq -> 'a seq =
  fun s -> MkSeq (FStar_List_Tot_Base.tl (__proj__MkSeq__item__l s))
let rec create : 'uuuuu . Prims.nat -> 'uuuuu -> 'uuuuu seq =
  fun len ->
    fun v ->
      if len = Prims.int_zero
      then MkSeq []
      else _cons v (create (len - Prims.int_one) v)
let rec init_aux' :
  'a . Prims.nat -> Prims.nat -> (Prims.nat -> 'a) -> 'a seq =
  fun len ->
    fun k ->
      fun contents ->
        if (k + Prims.int_one) = len
        then MkSeq [contents k]
        else _cons (contents k) (init_aux' len (k + Prims.int_one) contents)
let init_aux : 'a . Prims.nat -> Prims.nat -> (Prims.nat -> 'a) -> 'a seq =
  init_aux'
let init : 'uuuuu . Prims.nat -> (Prims.nat -> 'uuuuu) -> 'uuuuu seq =
  fun len ->
    fun contents ->
      if len = Prims.int_zero
      then MkSeq []
      else init_aux len Prims.int_zero contents
let empty : 'uuuuu . unit -> 'uuuuu seq = fun uu___ -> MkSeq []
let createEmpty : 'a . unit -> 'a seq = fun uu___ -> empty ()
let rec upd' : 'a . 'a seq -> Prims.nat -> 'a -> 'a seq =
  fun s ->
    fun n ->
      fun v ->
        if n = Prims.int_zero
        then _cons v (tl s)
        else _cons (hd s) (upd' (tl s) (n - Prims.int_one) v)
let upd : 'a . 'a seq -> Prims.nat -> 'a -> 'a seq = upd'
let append : 'uuuuu . 'uuuuu seq -> 'uuuuu seq -> 'uuuuu seq =
  fun s1 ->
    fun s2 ->
      MkSeq
        (FStar_List_Tot_Base.append (__proj__MkSeq__item__l s1)
           (__proj__MkSeq__item__l s2))
let cons : 'a . 'a -> 'a seq -> 'a seq =
  fun x -> fun s -> append (create Prims.int_one x) s
let op_At_Bar : 'a . 'a seq -> 'a seq -> 'a seq =
  fun s1 -> fun s2 -> append s1 s2
let rec slice' : 'a . 'a seq -> Prims.nat -> Prims.nat -> 'a seq =
  fun s ->
    fun i ->
      fun j ->
        if i > Prims.int_zero
        then slice' (tl s) (i - Prims.int_one) (j - Prims.int_one)
        else
          if j = Prims.int_zero
          then MkSeq []
          else _cons (hd s) (slice' (tl s) i (j - Prims.int_one))
let slice : 'a . 'a seq -> Prims.nat -> Prims.nat -> 'a seq = slice'
type ('a, 's1, 's2) equal = unit
let rec eq_i' : 'a . 'a seq -> 'a seq -> Prims.nat -> Prims.bool =
  fun s1 ->
    fun s2 ->
      fun i ->
        if i = (length s1)
        then true
        else
          if (index s1 i) = (index s2 i)
          then eq_i' s1 s2 (i + Prims.int_one)
          else false
let eq_i : 'a . 'a seq -> 'a seq -> Prims.nat -> Prims.bool = eq_i'
let eq : 'uuuuu . 'uuuuu seq -> 'uuuuu seq -> Prims.bool =
  fun s1 ->
    fun s2 ->
      if (length s1) = (length s2) then eq_i s1 s2 Prims.int_zero else false