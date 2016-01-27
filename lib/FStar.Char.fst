(*--build-config
  options: --admit_fsi FStar.Set;
  other-files: FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst
  --*)
module FStar.Char

assume val lowercase: char -> char
assume val uppercase: char -> char
assume val int_of_char: char -> int
