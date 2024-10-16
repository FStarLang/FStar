open Prims
let rec sequence_of_seq :
  'a . 'a FStar_Seq_Base.seq -> 'a FStar_Sequence_Base.seq =
  fun s ->
    if (FStar_Seq_Base.length s) = Prims.int_zero
    then FStar_Sequence_Base.empty ()
    else
      (let uu___1 = FStar_Seq_Properties.un_snoc s in
       match uu___1 with
       | (prefix, last) ->
           (FStar_Sequence_Base.op_Dollar_Colon_Colon ())
             (sequence_of_seq prefix) last)
let rec seq_of_sequence :
  'a . 'a FStar_Sequence_Base.seq -> 'a FStar_Seq_Base.seq =
  fun s ->
    if (FStar_Sequence_Base.length s) = Prims.int_zero
    then FStar_Seq_Base.empty ()
    else
      (let prefix =
         FStar_Sequence_Base.take s
           ((FStar_Sequence_Base.length s) - Prims.int_one) in
       FStar_Seq_Properties.snoc (seq_of_sequence prefix)
         ((FStar_Sequence_Base.op_Dollar_At ()) s
            ((FStar_Sequence_Base.length s) - Prims.int_one)))
type ('a, 's, 'su) related = unit