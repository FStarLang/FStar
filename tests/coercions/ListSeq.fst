module ListSeq

open FStar.Seq

[@@coercion]
let lseq (#a:Type) (l:list a) : seq a = seq_of_list l

let x : seq int = [1;2;3;4]
