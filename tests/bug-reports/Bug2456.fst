module Bug2456

type set (a : Type { hasEq a }) : nat -> Type =
    | Empty : set a 0
    | Next : #n:nat -> (hd : a) -> (tl : set a n) -> set a (n + 1)

let rec contains (#n : nat) (#a : Type { hasEq a }) (v : a) (s : set a n) =
    match s with
    | Empty -> false
    | Next hd tl -> hd = v || (contains v tl)

let containsWorks2 = assert(contains 3 (Next 3 Empty))

