module Bug1319a

[@(fail [54])]
let foo x l =
  match l with
  | [] -> x                      // this should obviously be [x] instead for correct code
  | hd :: tl -> x :: l
