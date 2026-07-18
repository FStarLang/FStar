module SeqLit

let x = seq![1; 2; 3]
let y = [1; 2; 3]

let _ = assert (FStar.Seq.seq_to_list x == y)

let _ = 1 :: [2] @ [3]
let _ = 1 :: 2 :: [3]
let _ = 1 :: 2 :: 3 :: []
let _ = 1 :: 2 :: 3 :: []

let _ = 1 `Seq.cons` seq![2] `Seq.append` seq![3]
let _ = 1 `Seq.cons` (2 `Seq.cons` seq![3])
let _ = 1 `Seq.cons` (2 `Seq.cons` (3 `Seq.cons` seq![]))
let _ = 1 `Seq.cons` (2 `Seq.cons` (3 `Seq.cons` seq![]))
