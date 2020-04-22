module Bug2010

open FStar.Seq

[@(expect_failure [66])]
let concat' #l1 #l2 (s1 : lseq 'a l1) (s2 : lseq 'a l2) : lseq 'a _ = append s1 s2

