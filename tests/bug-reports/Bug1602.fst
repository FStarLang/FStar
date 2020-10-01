module Bug1602

open FStar.Seq

let op_String_Access #t #l (s:lseq t l) i = index s i
let f #t #l (s:lseq t l) i = s.[i]

let op_Brack_Lens_Access #t #l (s:lseq t l) i = index s i
let g #t #l (s:lseq t l) i = s.[|i|]

let op_Array_Access #t #l (s:lseq t l) i = index s i
let h #t #l (s:lseq t l) i = s.(i)

let op_Lens_Access #t #l (s:lseq t l) i = index s i
let k #t #l (s:lseq t l) i = s.(|i|)
