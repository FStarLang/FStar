module Bug3207b

open FStar.List.Tot

type t (i : list int) = | Mk of int

#set-options "--no_smt"
 
let f #l (x : t l) : t ([] @ l) = x