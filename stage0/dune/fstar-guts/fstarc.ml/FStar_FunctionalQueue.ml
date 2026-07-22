open Prims
type 'a queue = ('a Prims.list * 'a Prims.list)
let empty (uu___ : unit) : 'a queue= ([], [])
let queue_to_list (q : 'a queue) : 'a Prims.list=
  match FStar_Pervasives_Native.fst q with
  | [] -> []
  | uu___ ->
      FStar_List_Tot_Base.op_At (FStar_Pervasives_Native.fst q)
        (FStar_List_Tot_Base.rev (FStar_Pervasives_Native.snd q))
let queue_of_list (l : 'a Prims.list) : 'a queue=
  match l with | [] -> empty () | uu___ -> (l, [])
let queue_to_seq (q : 'a queue) : 'a FStar_Seq_Base.seq=
  FStar_Seq_Base.seq_of_list (queue_to_list q)
let queue_of_seq (s : 'a FStar_Seq_Base.seq) : 'a queue=
  queue_of_list (FStar_Seq_Base.seq_to_list s)
let enqueue (x : 'a) (q : 'a queue) : 'a queue=
  match FStar_Pervasives_Native.fst q with
  | [] -> ([x], [])
  | l -> (l, (x :: (FStar_Pervasives_Native.snd q)))
let dequeue (q : 'a queue) : ('a * 'a queue)=
  let uu___ = FStar_Pervasives_Native.fst q in
  match uu___ with
  | hd::tl ->
      (match tl with
       | [] ->
           (hd,
             ((FStar_List_Tot_Base.rev (FStar_Pervasives_Native.snd q)), []))
       | uu___1 -> (hd, (tl, (FStar_Pervasives_Native.snd q))))
let peek (q : 'a queue) : 'a=
  FStar_List_Tot_Base.hd (FStar_Pervasives_Native.fst q)
