module LList

let rec length #a (l:list a)
  : nat
  = match l with
    | [] -> 0
    | _::tl -> 1 + length tl

let rec get #a (i:nat) (v:list a { i < length v })
  = let hd :: tl = v in
    if i = 0 then hd
    else get (i - 1) tl

let rec split_at #a (i:nat) (v:list a { i <= length v })
  : r:(list a & list a){
        length (fst r) == i /\
        length (snd r) == (length v - i)
     }
  = if i = 0
    then [], v
    else let hd :: tl = v in
         let l, r = split_at (i - 1) tl in
         hd::l, r

let rec append #a (v1 v2:list a)
  : v:list a { length v == length v1 + length v2 }
  = match v1 with
    | [] -> v2
    | hd::tl -> hd :: append tl v2
