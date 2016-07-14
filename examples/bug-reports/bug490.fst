module Bug490

type t (i:nat) = unit

type s = t

let f (x: s 0) = ()
