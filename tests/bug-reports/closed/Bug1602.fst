module Bug1602

open FStar.Seq

let ( .[] ) #t #l (s:lseq t l) i = index s i
let f #t #l (s:lseq t l) i = s.[i]

let ( .[||] ) #t #l (s:lseq t l) i = index s i
let g #t #l (s:lseq t l) i = s.[|i|]

let ( .() ) #t #l (s:lseq t l) i = index s i
let h #t #l (s:lseq t l) i = s.(i)

let ( .(||) ) #t #l (s:lseq t l) i = index s i
let k #t #l (s:lseq t l) i = s.(|i|)
