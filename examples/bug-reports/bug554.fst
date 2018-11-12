module Bug554

let index f l =
  let rec index i f l =
    match l with
    | [] ->
        0
    | hd :: tl ->
        if f hd then
          i
        else
          index (i + 1) f tl
  in
  index 0 f l
