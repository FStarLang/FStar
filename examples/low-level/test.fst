module Test

let rec length: #a:Type -> l:list a -> Tot nat = fun #a l -> match l with | [] -> 0 | hd::tl -> 1+length tl

let rec index' (i:'b) (f:'a -> bool) (l:list 'a) =
    match l with
    | [] ->
        0
    | hd :: tl ->
        if f hd then
          i
        else
          index' (i + 1) f tl

let index (f:'a -> bool) (l:list 'a) =
  let rec index (i:nat) (f:'a -> bool) (l:list 'a) : ML nat =
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
