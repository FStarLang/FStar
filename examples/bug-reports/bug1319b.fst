module Bug1319b

let map_rev (f : 'a -> 'b) (l : list 'a) : list 'b =
  let rec aux l acc =
   match l with 
   | [] -> acc 
   | x :: xs -> aux xs (f x :: acc)
   in  aux l []
