open Prims
type bytes = FStar_UInt8.t FStar_Seq_Base.seq
let rec (le_to_n : bytes -> Prims.nat) =
  fun b ->
    if (FStar_Seq_Base.length b) = Prims.int_zero
    then Prims.int_zero
    else
      (FStar_UInt8.v (FStar_Seq_Properties.head b)) +
        ((Prims.pow2 (Prims.of_int (8))) *
           (le_to_n (FStar_Seq_Properties.tail b)))
let rec (be_to_n : bytes -> Prims.nat) =
  fun b ->
    if (FStar_Seq_Base.length b) = Prims.int_zero
    then Prims.int_zero
    else
      (FStar_UInt8.v (FStar_Seq_Properties.last b)) +
        ((Prims.pow2 (Prims.of_int (8))) *
           (be_to_n
              (FStar_Seq_Base.slice b Prims.int_zero
                 ((FStar_Seq_Base.length b) - Prims.int_one))))
let rec (n_to_le : Prims.nat -> Prims.nat -> bytes) =
  fun len ->
    fun n ->
      if len = Prims.int_zero
      then FStar_Seq_Base.empty ()
      else
        (let len1 = len - Prims.int_one in
         let byte = FStar_UInt8.uint_to_t (n mod (Prims.of_int (256))) in
         let n' = n / (Prims.of_int (256)) in
         let b' = n_to_le len1 n' in let b = FStar_Seq_Base.cons byte b' in b)
let rec (n_to_be : Prims.nat -> Prims.nat -> bytes) =
  fun len ->
    fun n ->
      if len = Prims.int_zero
      then FStar_Seq_Base.empty ()
      else
        (let len1 = len - Prims.int_one in
         let byte = FStar_UInt8.uint_to_t (n mod (Prims.of_int (256))) in
         let n' = n / (Prims.of_int (256)) in
         let b' = n_to_be len1 n' in
         let b'' = FStar_Seq_Base.create Prims.int_one byte in
         let b = FStar_Seq_Base.append b' b'' in b)
let (uint32_of_le : bytes -> FStar_UInt32.t) =
  fun b -> let n = le_to_n b in FStar_UInt32.uint_to_t n
let (le_of_uint32 : FStar_UInt32.t -> bytes) =
  fun x -> n_to_le (Prims.of_int (4)) (FStar_UInt32.v x)
let (uint32_of_be : bytes -> FStar_UInt32.t) =
  fun b -> let n = be_to_n b in FStar_UInt32.uint_to_t n
let (be_of_uint32 : FStar_UInt32.t -> bytes) =
  fun x -> n_to_be (Prims.of_int (4)) (FStar_UInt32.v x)
let (uint64_of_le : bytes -> FStar_UInt64.t) =
  fun b -> let n = le_to_n b in FStar_UInt64.uint_to_t n
let (le_of_uint64 : FStar_UInt64.t -> bytes) =
  fun x -> n_to_le (Prims.of_int (8)) (FStar_UInt64.v x)
let (uint64_of_be : bytes -> FStar_UInt64.t) =
  fun b -> let n = be_to_n b in FStar_UInt64.uint_to_t n
let (be_of_uint64 : FStar_UInt64.t -> bytes) =
  fun x -> n_to_be (Prims.of_int (8)) (FStar_UInt64.v x)
let rec (seq_uint32_of_le :
  Prims.nat -> bytes -> FStar_UInt32.t FStar_Seq_Base.seq) =
  fun l ->
    fun b ->
      if (FStar_Seq_Base.length b) = Prims.int_zero
      then FStar_Seq_Base.empty ()
      else
        (let uu___1 = FStar_Seq_Properties.split b (Prims.of_int (4)) in
         match uu___1 with
         | (hd, tl) ->
             FStar_Seq_Base.cons (uint32_of_le hd)
               (seq_uint32_of_le (l - Prims.int_one) tl))
let rec (le_of_seq_uint32 : FStar_UInt32.t FStar_Seq_Base.seq -> bytes) =
  fun s ->
    if (FStar_Seq_Base.length s) = Prims.int_zero
    then FStar_Seq_Base.empty ()
    else
      FStar_Seq_Base.append (le_of_uint32 (FStar_Seq_Properties.head s))
        (le_of_seq_uint32 (FStar_Seq_Properties.tail s))
let rec (seq_uint32_of_be :
  Prims.nat -> bytes -> FStar_UInt32.t FStar_Seq_Base.seq) =
  fun l ->
    fun b ->
      if (FStar_Seq_Base.length b) = Prims.int_zero
      then FStar_Seq_Base.empty ()
      else
        (let uu___1 = FStar_Seq_Properties.split b (Prims.of_int (4)) in
         match uu___1 with
         | (hd, tl) ->
             FStar_Seq_Base.cons (uint32_of_be hd)
               (seq_uint32_of_be (l - Prims.int_one) tl))
let rec (be_of_seq_uint32 : FStar_UInt32.t FStar_Seq_Base.seq -> bytes) =
  fun s ->
    if (FStar_Seq_Base.length s) = Prims.int_zero
    then FStar_Seq_Base.empty ()
    else
      FStar_Seq_Base.append (be_of_uint32 (FStar_Seq_Properties.head s))
        (be_of_seq_uint32 (FStar_Seq_Properties.tail s))
let rec (seq_uint64_of_le :
  Prims.nat -> bytes -> FStar_UInt64.t FStar_Seq_Base.seq) =
  fun l ->
    fun b ->
      if (FStar_Seq_Base.length b) = Prims.int_zero
      then FStar_Seq_Base.empty ()
      else
        (let uu___1 = FStar_Seq_Properties.split b (Prims.of_int (8)) in
         match uu___1 with
         | (hd, tl) ->
             FStar_Seq_Base.cons (uint64_of_le hd)
               (seq_uint64_of_le (l - Prims.int_one) tl))
let rec (le_of_seq_uint64 : FStar_UInt64.t FStar_Seq_Base.seq -> bytes) =
  fun s ->
    if (FStar_Seq_Base.length s) = Prims.int_zero
    then FStar_Seq_Base.empty ()
    else
      FStar_Seq_Base.append (le_of_uint64 (FStar_Seq_Properties.head s))
        (le_of_seq_uint64 (FStar_Seq_Properties.tail s))
let rec (seq_uint64_of_be :
  Prims.nat -> bytes -> FStar_UInt64.t FStar_Seq_Base.seq) =
  fun l ->
    fun b ->
      if (FStar_Seq_Base.length b) = Prims.int_zero
      then FStar_Seq_Base.empty ()
      else
        (let uu___1 = FStar_Seq_Properties.split b (Prims.of_int (8)) in
         match uu___1 with
         | (hd, tl) ->
             FStar_Seq_Base.cons (uint64_of_be hd)
               (seq_uint64_of_be (l - Prims.int_one) tl))
let rec (be_of_seq_uint64 : FStar_UInt64.t FStar_Seq_Base.seq -> bytes) =
  fun s ->
    if (FStar_Seq_Base.length s) = Prims.int_zero
    then FStar_Seq_Base.empty ()
    else
      FStar_Seq_Base.append (be_of_uint64 (FStar_Seq_Properties.head s))
        (be_of_seq_uint64 (FStar_Seq_Properties.tail s))