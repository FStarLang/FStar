module Bug815b

open FStar.List.Tot

val pop : s1:(list int){length s1 > 0} ->
  Tot (s2:(list int){length s2 = length s1 - 1})
let pop = Cons?.tl

(* This works: *)
(* let pop xs = Cons?.tl xs *)
