module MonadicLetBindings

open FStar.Option

let head: list _ -> option _
  = function | v::_ -> Some v
             |   _ -> None

let option_example (a b: list (int * int)) (c: option bool) = 
  let? haL, haR = head a 
  and? hbL, hbR = head b in
  match? c with
  | true  -> Some (haL + hbL)
  | false -> Some (haR + hbR)

let letPunning (a: option int)
  = let? a in // equivalent to [let? a = a in]
    Some (a + 10)

let _ = assert_norm (option_example [(1,2)] [(3,4)] (Some true) == Some 4)
let _ = assert_norm (option_example [] [(3,4)] (Some true) == None)

open FStar.List.Tot

let ( let:: ) (l: list 'a) (f: 'a -> list 'b): list 'b
  = flatten (map f l)

let rec zip (a: list 'a) (b: list 'b): list ('a * 'b)
  = match a, b with
  | ha::ta, hb::tb -> (ha,hb)::zip ta tb
  | _            -> []

let ( and:: ) (a: list 'a) (b: list 'b): list ('a * 'b)
  = zip a b 

let list_example1 =
  let:: x = [10;20;30] in
  [x + 1; x + 2; x + 3]

let _ = assert_norm (list_example1 == [11;12;13;21;22;23;31;32;33])

let list_example2 =
  let:: x = [10;20;30]
  and:: y = ["A";"B";"C"] in
  [x + 5, y ^ "!"]

let _ = assert_norm (list_example2 == [15, "A!"; 25, "B!"; 35, "C!"])

