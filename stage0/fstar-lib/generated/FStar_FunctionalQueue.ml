open Prims
type 'a queue = ('a Prims.list * 'a Prims.list)
let empty : 'a . unit -> 'a queue = fun uu___ -> ([], [])
let queue_to_list : 'a . 'a queue -> 'a Prims.list =
  fun q ->
    match FStar_Pervasives_Native.fst q with
    | [] -> []
    | uu___ ->
        FStar_List_Tot_Base.op_At (FStar_Pervasives_Native.fst q)
          (FStar_List_Tot_Base.rev (FStar_Pervasives_Native.snd q))
let queue_of_list : 'a . 'a Prims.list -> 'a queue =
  fun l -> match l with | [] -> empty () | uu___ -> (l, [])
let queue_to_seq : 'a . 'a queue -> 'a FStar_Seq_Base.seq =
  fun q -> FStar_Seq_Base.seq_of_list (queue_to_list q)
let queue_of_seq : 'a . 'a FStar_Seq_Base.seq -> 'a queue =
  fun s -> queue_of_list (FStar_Seq_Base.seq_to_list s)
type ('a, 'q1, 'q2) equal = unit
type ('a, 'q) not_empty = unit
let enqueue : 'a . 'a -> 'a queue -> 'a queue =
  fun x ->
    fun q ->
      match FStar_Pervasives_Native.fst q with
      | [] -> ([x], [])
      | l -> (l, (x :: (FStar_Pervasives_Native.snd q)))
let dequeue : 'a . 'a queue -> ('a * 'a queue) =
  fun q ->
    let uu___ = FStar_Pervasives_Native.fst q in
    match uu___ with
    | hd::tl ->
        (match tl with
         | [] ->
             (hd,
               ((FStar_List_Tot_Base.rev (FStar_Pervasives_Native.snd q)),
                 []))
         | uu___1 -> (hd, (tl, (FStar_Pervasives_Native.snd q))))
let peek : 'a . 'a queue -> 'a =
  fun q -> FStar_List_Tot_Base.hd (FStar_Pervasives_Native.fst q)