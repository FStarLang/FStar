let b0 n =  (n          land 0xFF)
let b1 n =  ((n lsr 8)  land 0xFF)
let b2 n =  ((n lsr 16) land 0xFF)
let b3 n =  ((n lsr 24) land 0xFF)

let dummyRange = 0L

let lor64 = BatInt64.logor
let land64 = BatInt64.logand
let lsl64 = BatInt64.shift_left
let lsr64 = BatInt64.shift_right

let rec pown32 n = if n = 0 then 0  else (pown32 (n-1) lor (1 lsl (n-1)))
let rec pown64 n = if n = 0 then 0L else (lor64 (pown64 (n-1)) (lsl64 1L (n-1)))
let mask32 m n = (pown32 n) lsl m
let mask64 m n = lsl64 (pown64 n) m

let string_ord (a:string) (b:string) = compare a b
let int_ord (a:int) (b:int) = compare a b
let int32_ord (a:FStar_BaseTypes.int32) (b:FStar_BaseTypes.int32) = compare a b

let pair_ord (compare1,compare2) (a1,a2) (aa1,aa2) =
  let res1 = compare1 a1 aa1 in
  if res1 <> 0 then res1 else compare2 a2 aa2

let proj_ord f a1 a2 = compare (f a1)  (f a2)

type file_idx = FStar_BaseTypes.int32
type pos = FStar_BaseTypes.int32
type range = FStar_BaseTypes.int64

let col_nbits  = 9
let line_nbits  = 16

let pos_nbits = line_nbits + col_nbits
let _ = assert (pos_nbits <= 32)
let pos_col_mask  = mask32 0         col_nbits
let line_col_mask = mask32 col_nbits line_nbits

let mk_pos l c =
  let l = max 0 l in
  let c = max 0 c in
  (c land pos_col_mask)
  lor ((l lsl col_nbits) land line_col_mask)
let line_of_pos p =  (p lsr col_nbits)
let col_of_pos p =  (p land pos_col_mask)

let bits_of_pos (x:pos) : FStar_BaseTypes.int32 = x
let pos_of_bits (x:FStar_BaseTypes.int32) : pos = x

let file_idx_nbits = 14
let start_line_nbits = line_nbits
let start_col_nbits = col_nbits
let end_line_nbits = line_nbits
let end_col_nbits = col_nbits
let _ = assert (file_idx_nbits + start_line_nbits + start_col_nbits + end_line_nbits + end_col_nbits = 64)

let file_idx_mask   = mask64 0 file_idx_nbits
let start_line_mask = mask64 (file_idx_nbits) start_line_nbits
let start_col_mask  = mask64 (file_idx_nbits + start_line_nbits) start_col_nbits
let end_line_mask   = mask64 (file_idx_nbits + start_line_nbits + start_col_nbits) end_line_nbits
let end_col_mask    = mask64 (file_idx_nbits + start_line_nbits + start_col_nbits + end_line_nbits) end_col_nbits

let mk_file_idx_range fidx b e =
  lor64
    (lor64
       (lor64
          (lor64
             (BatInt64.of_int fidx)
             (lsl64 (BatInt64.of_int (line_of_pos b)) file_idx_nbits))
          (lsl64 (BatInt64.of_int (col_of_pos b)) (file_idx_nbits + start_line_nbits)))
       (lsl64 (BatInt64.of_int (line_of_pos e)) (file_idx_nbits + start_line_nbits + start_col_nbits)))
    (lsl64 (BatInt64.of_int (col_of_pos e)) (file_idx_nbits + start_line_nbits + start_col_nbits + end_line_nbits))
let file_idx_of_range r   = BatInt64.to_int (land64 r file_idx_mask)
let start_line_of_range r = BatInt64.to_int (lsr64 (land64 r start_line_mask) file_idx_nbits)
let start_col_of_range r  = BatInt64.to_int (lsr64 (land64 r start_col_mask) (file_idx_nbits + start_line_nbits))
let end_line_of_range r   = BatInt64.to_int (lsr64 (land64 r end_line_mask) (file_idx_nbits + start_line_nbits + start_col_nbits))
let end_col_of_range r    = BatInt64.to_int (lsr64 (land64 r end_col_mask) (file_idx_nbits + start_line_nbits + start_col_nbits + end_line_nbits))

(* This is just a standard unique-index table *)
module FileIndexTable = struct
  type 'a t = {
    indexToFileTable : 'a BatDynArray.t;
    fileToIndexTable  : (string, int) BatHashtbl.t
  }
  let fileToIndex t f =
    try
      BatHashtbl.find t.fileToIndexTable f
    with
    | Not_found ->
       let n = BatDynArray.length t.indexToFileTable in
       BatDynArray.add t.indexToFileTable f;
       BatHashtbl.add t.fileToIndexTable f n;
       n
  let indexToFile t n =
    (if n < 0 then failwith ("file_of_file_idx: negative argument: n = "^(string_of_int n)^"\n"));
    (if n >= BatDynArray.length t.indexToFileTable then failwith ("file_of_file_idx: invalid argument: n = "^(string_of_int n)^"\n"));
    BatDynArray.get t.indexToFileTable n
end
open FileIndexTable

let maxFileIndex = pown32 file_idx_nbits

let fileIndexTable = {
  indexToFileTable = BatDynArray.make 11;
  fileToIndexTable = BatHashtbl.create 11
}
let file_idx_of_file f = (fileToIndex fileIndexTable f) mod maxFileIndex
let file_of_file_idx n = indexToFile fileIndexTable n

let mk_range f b e = mk_file_idx_range (file_idx_of_file f) b e
let file_of_range r = file_of_file_idx (file_idx_of_range r)

let start_of_range r = mk_pos (start_line_of_range r) (start_col_of_range r)
let end_of_range r = mk_pos (end_line_of_range r) (end_col_of_range r)
let dest_file_idx_range r = file_idx_of_range r,start_of_range r,end_of_range r
let dest_range r = file_of_range r,start_of_range r,end_of_range r
let dest_pos p = line_of_pos p,col_of_pos p
let end_range (r:range) = mk_range (file_of_range r) (end_of_range r) (end_of_range r)

let trim_range_right r n =
  let fidx,p1,p2 = dest_file_idx_range r in
  let l2,c2 = dest_pos p2 in
  mk_file_idx_range fidx p1 (mk_pos l2 (max 0 (c2 - n)))

let pos_ord   p1 p2 = pair_ord (int_ord   ,int_ord) (dest_pos p1) (dest_pos p2)
(* range_ord: not a total order, but enough to sort on ranges *)
let range_ord r1 r2 = pair_ord (string_ord,pos_ord) (file_of_range r1,start_of_range r1) (file_of_range r2,start_of_range r2)

let output_pos (os:out_channel) m = Printf.fprintf os "(%d,%d)" (line_of_pos m) (col_of_pos m)
let output_range (os:out_channel) m = Printf.fprintf os "%s%a-%a" (file_of_range m) output_pos (start_of_range m) output_pos (end_of_range m)
let boutput_pos os m = Printf.bprintf os "(%d,%d)" (line_of_pos m) (col_of_pos m)
let boutput_range os m = Printf.bprintf os "%s%a-%a" (file_of_range m) boutput_pos (start_of_range m) boutput_pos (end_of_range m)

let start_range_of_range m =    let f,s,e = dest_file_idx_range m in mk_file_idx_range f s s
let end_range_of_range m =   let f,s,e = dest_file_idx_range m in mk_file_idx_range f e e
let pos_gt p1 p2 =
  (line_of_pos p1 > line_of_pos p2 ||
     (line_of_pos p1 = line_of_pos p2 &&
        col_of_pos p1 > col_of_pos p2))

let pos_eq p1 p2 = (line_of_pos p1 = line_of_pos p2 &&  col_of_pos p1 = col_of_pos p2)
let pos_geq p1 p2 = pos_eq p1 p2 || pos_gt p1 p2

let union_ranges m1 m2 =
  if file_idx_of_range m1 <> file_idx_of_range m2 then m2 else
    let b =
      if pos_geq (start_of_range m1) (start_of_range m2) then (start_of_range m2)
      else (start_of_range m1) in
    let e =
      if pos_geq (end_of_range m1) (end_of_range m2) then (end_of_range m1)
      else (end_of_range m2) in
    mk_file_idx_range (file_idx_of_range m1) b e

let range_contains_range m1 m2 =
  (file_of_range m1) = (file_of_range m2) &&
    pos_geq (start_of_range m2) (start_of_range m1) &&
      pos_geq (end_of_range m1) (end_of_range m2)

let range_contains_pos m1 p =
  pos_geq p (start_of_range m1) &&
    pos_geq (end_of_range m1) p

let range_before_pos m1 p =
  pos_geq p (end_of_range m1)

let rangeN filename line =  mk_range filename (mk_pos line 0) (mk_pos line 80)
let pos0 = mk_pos 1 0
let range0 =  rangeN "unknown" 1
let rangeStartup = rangeN "startup" 1

(* // Store a file_idx in the pos_fname field, so we don't have to look up the  *)
(* // file_idx hash table to map back from pos_fname to a file_idx during lexing  *)
let encode_file_idx idx =
  FStar_Util.string_of_unicode [|idx land 0x7F; (idx lsr 7) land 0x7F|]

let encode_file file = encode_file_idx (file_idx_of_file file)

let _ = assert (file_idx_nbits <= 14) (* this encoding is size limited *)
let decode_file_idx (s:string) =
  if BatString.length s = 0 then 0 else
    let idx =   (int_of_char (BatString.get s 0))
                lor ((int_of_char (BatString.get s 1)) lsl 7) in
    idx

(* For Diagnostics *)
let string_of_pos   pos = let line,col = line_of_pos pos,col_of_pos pos in Printf.sprintf "%d,%d" line col
let string_of_range r   = Printf.sprintf "%s(%s-%s)" (file_of_range r) (string_of_pos (start_of_range r)) (string_of_pos (end_of_range r))

let compare r1 r2 =
  let fcomp = String.compare (file_of_range r1) (file_of_range r2) in
  if fcomp = 0
  then let start1 = start_of_range r1 in
       let start2 = start_of_range r2 in
       let lcomp = line_of_pos start1 - line_of_pos start2 in
       if lcomp = 0
       then col_of_pos start1 - col_of_pos start2
       else lcomp
  else fcomp
