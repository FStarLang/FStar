module Bug747

open FStar.List.Tot

val append_hd: l:list int -> r:list int ->
  Lemma (requires (is_Cons l /\ is_Cons r))
        (ensures (is_Cons l /\ is_Cons r /\ (hd (l@r) = hd l)))
