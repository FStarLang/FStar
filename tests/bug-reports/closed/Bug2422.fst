module Bug2422

module L = FStar.List.Tot

assume
val t (n:nat) : Type0

assume
val mkt (x:list (bool & int)) : t (L.length x)

let test (x:list int)
         (y:list (bool & int))
         (_:squash (L.length x == L.length y /\ Cons? y))
    : t (L.length x)
    = mkt ((false, 0) :: Cons?.tl y)

let test2 (x:list int)
         (y:list (bool & int))
         (_: squash (L.length x == L.length y /\ Cons? y))
    : t (L.length x)
    = mkt (Mktuple2 #bool #int false 0 :: Cons?.tl y)
