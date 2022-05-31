module Bug2595

noeq
type sum_type  =
  | SumType1: string -> sum_type
  | SumType2: nat -> sum_type

let test_buggy (x:(b:bool & (if b then nat else string))): sum_type =
  match x with
  | (|false, x2|) -> SumType1 x2
  | (|true, x4|) -> SumType2 x4
