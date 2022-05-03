module A

type data =
  | A
  | B
  | C

let data_to_string = function
  | A -> "A"
  | B -> "B"
  | C -> "C"
