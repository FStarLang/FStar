(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.Seq --admit_fsi FStar.IO;
    other-files:FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.IO.fsti
  --*)
module TestSeq
open FStar
open FStar.IO

val print_seq : i:nat -> s:Seq.seq int {i <= Seq.length s} -> unit
let rec print_seq i s = 
  if i = Seq.length s then ()
  else (print_string (string_of_int (Seq.index s i)); 
        print_seq (i + 1) s)

let main =
  let x = Seq.create 100 0 in
  print_seq 0 x
