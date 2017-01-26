module Bug747

open FStar.List.Tot

val append_hd: l:list int -> r:list int ->
  Lemma (requires (Cons? l /\ Cons? r))
        (ensures (Cons? l /\ Cons? r /\ (hd (l@r) = hd l)))
