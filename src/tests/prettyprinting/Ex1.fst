module Ex1

[@ one two three four five six seven eight nine ten eleven ten eleven ten eleven ten eleven ten here
   eleven ten eleven ten eleven ten eleven]
type t =
  | A : int -> t
  | B
  | C : int -> int -> t
  | D of int

